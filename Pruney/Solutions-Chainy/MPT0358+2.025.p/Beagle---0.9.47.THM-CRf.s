%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:03 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   63 (  85 expanded)
%              Number of leaves         :   31 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :   74 ( 114 expanded)
%              Number of equality atoms :   26 (  47 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_82,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(c_38,plain,(
    ! [A_21] : k1_subset_1(A_21) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_52,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_53,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_52])).

tff(c_109,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_53])).

tff(c_8,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_111,plain,(
    ! [A_7] : r1_tarski('#skF_4',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_8])).

tff(c_46,plain,
    ( k1_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_54,plain,
    ( k1_xboole_0 != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_46])).

tff(c_193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_109,c_54])).

tff(c_195,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_194,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_42,plain,(
    ! [A_24] : ~ v1_xboole_0(k1_zfmisc_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_385,plain,(
    ! [B_63,A_64] :
      ( r2_hidden(B_63,A_64)
      | ~ m1_subset_1(B_63,A_64)
      | v1_xboole_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_18,plain,(
    ! [C_18,A_14] :
      ( r1_tarski(C_18,A_14)
      | ~ r2_hidden(C_18,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_392,plain,(
    ! [B_63,A_14] :
      ( r1_tarski(B_63,A_14)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_14))
      | v1_xboole_0(k1_zfmisc_1(A_14)) ) ),
    inference(resolution,[status(thm)],[c_385,c_18])).

tff(c_397,plain,(
    ! [B_65,A_66] :
      ( r1_tarski(B_65,A_66)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_66)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_392])).

tff(c_410,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_397])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_478,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_410,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_546,plain,(
    ! [A_70,B_71] :
      ( k4_xboole_0(A_70,B_71) = k3_subset_1(A_70,B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_559,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_546])).

tff(c_10,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_566,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_559,c_10])).

tff(c_572,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_2,c_566])).

tff(c_16,plain,(
    ! [A_11,C_13,B_12] :
      ( r1_xboole_0(A_11,k4_xboole_0(C_13,B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_761,plain,(
    ! [A_84] :
      ( r1_xboole_0(A_84,'#skF_4')
      | ~ r1_tarski(A_84,k3_subset_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_572,c_16])).

tff(c_774,plain,(
    r1_xboole_0('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_194,c_761])).

tff(c_14,plain,(
    ! [A_10] :
      ( ~ r1_xboole_0(A_10,A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_778,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_774,c_14])).

tff(c_782,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_778])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:42:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.35  
% 2.66/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.35  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.66/1.35  
% 2.66/1.35  %Foreground sorts:
% 2.66/1.35  
% 2.66/1.35  
% 2.66/1.35  %Background operators:
% 2.66/1.35  
% 2.66/1.35  
% 2.66/1.35  %Foreground operators:
% 2.66/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.66/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.66/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.66/1.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.66/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.66/1.35  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.66/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.66/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.66/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.66/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.66/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.66/1.35  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.66/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.66/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.66/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.66/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.66/1.35  
% 2.66/1.36  tff(f_75, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.66/1.36  tff(f_89, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 2.66/1.36  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.66/1.36  tff(f_82, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.66/1.36  tff(f_73, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.66/1.36  tff(f_60, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.66/1.36  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.66/1.36  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.66/1.36  tff(f_79, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.66/1.36  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.66/1.36  tff(f_53, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 2.66/1.36  tff(f_49, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.66/1.36  tff(c_38, plain, (![A_21]: (k1_subset_1(A_21)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.66/1.36  tff(c_52, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.66/1.36  tff(c_53, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_52])).
% 2.66/1.36  tff(c_109, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_53])).
% 2.66/1.36  tff(c_8, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.66/1.36  tff(c_111, plain, (![A_7]: (r1_tarski('#skF_4', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_8])).
% 2.66/1.36  tff(c_46, plain, (k1_subset_1('#skF_3')!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.66/1.36  tff(c_54, plain, (k1_xboole_0!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_46])).
% 2.66/1.36  tff(c_193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_111, c_109, c_54])).
% 2.66/1.36  tff(c_195, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_53])).
% 2.66/1.36  tff(c_194, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_53])).
% 2.66/1.36  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.66/1.36  tff(c_42, plain, (![A_24]: (~v1_xboole_0(k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.66/1.36  tff(c_385, plain, (![B_63, A_64]: (r2_hidden(B_63, A_64) | ~m1_subset_1(B_63, A_64) | v1_xboole_0(A_64))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.66/1.36  tff(c_18, plain, (![C_18, A_14]: (r1_tarski(C_18, A_14) | ~r2_hidden(C_18, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.66/1.36  tff(c_392, plain, (![B_63, A_14]: (r1_tarski(B_63, A_14) | ~m1_subset_1(B_63, k1_zfmisc_1(A_14)) | v1_xboole_0(k1_zfmisc_1(A_14)))), inference(resolution, [status(thm)], [c_385, c_18])).
% 2.66/1.36  tff(c_397, plain, (![B_65, A_66]: (r1_tarski(B_65, A_66) | ~m1_subset_1(B_65, k1_zfmisc_1(A_66)))), inference(negUnitSimplification, [status(thm)], [c_42, c_392])).
% 2.66/1.36  tff(c_410, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_397])).
% 2.66/1.36  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.66/1.36  tff(c_478, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_410, c_6])).
% 2.66/1.36  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.66/1.36  tff(c_546, plain, (![A_70, B_71]: (k4_xboole_0(A_70, B_71)=k3_subset_1(A_70, B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.66/1.36  tff(c_559, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_546])).
% 2.66/1.36  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.66/1.36  tff(c_566, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_559, c_10])).
% 2.66/1.36  tff(c_572, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_478, c_2, c_566])).
% 2.66/1.36  tff(c_16, plain, (![A_11, C_13, B_12]: (r1_xboole_0(A_11, k4_xboole_0(C_13, B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.66/1.36  tff(c_761, plain, (![A_84]: (r1_xboole_0(A_84, '#skF_4') | ~r1_tarski(A_84, k3_subset_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_572, c_16])).
% 2.66/1.36  tff(c_774, plain, (r1_xboole_0('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_194, c_761])).
% 2.66/1.36  tff(c_14, plain, (![A_10]: (~r1_xboole_0(A_10, A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.66/1.36  tff(c_778, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_774, c_14])).
% 2.66/1.36  tff(c_782, plain, $false, inference(negUnitSimplification, [status(thm)], [c_195, c_778])).
% 2.66/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.36  
% 2.66/1.36  Inference rules
% 2.66/1.36  ----------------------
% 2.66/1.36  #Ref     : 0
% 2.66/1.36  #Sup     : 192
% 2.66/1.36  #Fact    : 0
% 2.66/1.36  #Define  : 0
% 2.66/1.36  #Split   : 2
% 2.66/1.36  #Chain   : 0
% 2.66/1.36  #Close   : 0
% 2.66/1.36  
% 2.66/1.36  Ordering : KBO
% 2.66/1.36  
% 2.66/1.36  Simplification rules
% 2.66/1.36  ----------------------
% 2.66/1.36  #Subsume      : 23
% 2.66/1.36  #Demod        : 85
% 2.66/1.36  #Tautology    : 119
% 2.66/1.36  #SimpNegUnit  : 3
% 2.66/1.36  #BackRed      : 7
% 2.66/1.36  
% 2.66/1.36  #Partial instantiations: 0
% 2.66/1.36  #Strategies tried      : 1
% 2.66/1.36  
% 2.66/1.36  Timing (in seconds)
% 2.66/1.36  ----------------------
% 2.77/1.37  Preprocessing        : 0.31
% 2.77/1.37  Parsing              : 0.16
% 2.77/1.37  CNF conversion       : 0.02
% 2.77/1.37  Main loop            : 0.30
% 2.77/1.37  Inferencing          : 0.11
% 2.77/1.37  Reduction            : 0.11
% 2.77/1.37  Demodulation         : 0.08
% 2.77/1.37  BG Simplification    : 0.02
% 2.77/1.37  Subsumption          : 0.05
% 2.77/1.37  Abstraction          : 0.02
% 2.77/1.37  MUC search           : 0.00
% 2.77/1.37  Cooper               : 0.00
% 2.77/1.37  Total                : 0.64
% 2.77/1.37  Index Insertion      : 0.00
% 2.77/1.37  Index Deletion       : 0.00
% 2.77/1.37  Index Matching       : 0.00
% 2.77/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
