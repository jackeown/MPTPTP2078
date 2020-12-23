%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:10 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   61 (  99 expanded)
%              Number of leaves         :   26 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :   70 ( 138 expanded)
%              Number of equality atoms :   27 (  61 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_57,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_64,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_30,plain,(
    ! [A_16] : k2_subset_1(A_16) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_38,plain,
    ( k2_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_46,plain,
    ( '#skF_3' != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_38])).

tff(c_101,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_44,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | k2_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_45,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_44])).

tff(c_102,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_45])).

tff(c_103,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_101])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_104,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_36])).

tff(c_233,plain,(
    ! [A_51,B_52] :
      ( k4_xboole_0(A_51,B_52) = k3_subset_1(A_51,B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_245,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k3_subset_1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_104,c_233])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_259,plain,(
    r1_tarski(k3_subset_1('#skF_4','#skF_4'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_6])).

tff(c_264,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_259])).

tff(c_265,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_34,plain,(
    ! [A_19] : ~ v1_xboole_0(k1_zfmisc_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_340,plain,(
    ! [B_63,A_64] :
      ( r2_hidden(B_63,A_64)
      | ~ m1_subset_1(B_63,A_64)
      | v1_xboole_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [C_13,A_9] :
      ( r1_tarski(C_13,A_9)
      | ~ r2_hidden(C_13,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_344,plain,(
    ! [B_63,A_9] :
      ( r1_tarski(B_63,A_9)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_9))
      | v1_xboole_0(k1_zfmisc_1(A_9)) ) ),
    inference(resolution,[status(thm)],[c_340,c_10])).

tff(c_350,plain,(
    ! [B_65,A_66] :
      ( r1_tarski(B_65,A_66)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_66)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_344])).

tff(c_359,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_350])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_363,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_359,c_4])).

tff(c_266,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_273,plain,(
    ! [A_57,B_58] :
      ( k2_xboole_0(A_57,B_58) = B_58
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_280,plain,(
    k2_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_266,c_273])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_285,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_2])).

tff(c_414,plain,(
    ! [A_74,B_75] :
      ( k4_xboole_0(A_74,B_75) = k3_subset_1(A_74,B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_427,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_414])).

tff(c_8,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_432,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_427,c_8])).

tff(c_444,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_285,c_432])).

tff(c_446,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_265,c_444])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:15:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.49  
% 2.20/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.50  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.35/1.50  
% 2.35/1.50  %Foreground sorts:
% 2.35/1.50  
% 2.35/1.50  
% 2.35/1.50  %Background operators:
% 2.35/1.50  
% 2.35/1.50  
% 2.35/1.50  %Foreground operators:
% 2.35/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.35/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.35/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.35/1.50  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.35/1.50  tff('#skF_3', type, '#skF_3': $i).
% 2.35/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.35/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.50  tff('#skF_4', type, '#skF_4': $i).
% 2.35/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.35/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.35/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.35/1.50  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.35/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.35/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.35/1.50  
% 2.35/1.51  tff(f_57, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.35/1.51  tff(f_71, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 2.35/1.51  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.35/1.51  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.35/1.51  tff(f_64, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.35/1.51  tff(f_55, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.35/1.51  tff(f_42, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.35/1.51  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.35/1.51  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.35/1.51  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.35/1.51  tff(c_30, plain, (![A_16]: (k2_subset_1(A_16)=A_16)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.35/1.51  tff(c_38, plain, (k2_subset_1('#skF_3')!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.35/1.51  tff(c_46, plain, ('#skF_3'!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_38])).
% 2.35/1.51  tff(c_101, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_46])).
% 2.35/1.51  tff(c_44, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | k2_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.35/1.51  tff(c_45, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_44])).
% 2.35/1.51  tff(c_102, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_101, c_45])).
% 2.35/1.51  tff(c_103, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_101])).
% 2.35/1.51  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.35/1.51  tff(c_104, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_36])).
% 2.35/1.51  tff(c_233, plain, (![A_51, B_52]: (k4_xboole_0(A_51, B_52)=k3_subset_1(A_51, B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.35/1.51  tff(c_245, plain, (k4_xboole_0('#skF_4', '#skF_4')=k3_subset_1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_104, c_233])).
% 2.35/1.51  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.35/1.51  tff(c_259, plain, (r1_tarski(k3_subset_1('#skF_4', '#skF_4'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_245, c_6])).
% 2.35/1.51  tff(c_264, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_259])).
% 2.35/1.51  tff(c_265, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_46])).
% 2.35/1.51  tff(c_34, plain, (![A_19]: (~v1_xboole_0(k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.35/1.51  tff(c_340, plain, (![B_63, A_64]: (r2_hidden(B_63, A_64) | ~m1_subset_1(B_63, A_64) | v1_xboole_0(A_64))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.35/1.51  tff(c_10, plain, (![C_13, A_9]: (r1_tarski(C_13, A_9) | ~r2_hidden(C_13, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.35/1.51  tff(c_344, plain, (![B_63, A_9]: (r1_tarski(B_63, A_9) | ~m1_subset_1(B_63, k1_zfmisc_1(A_9)) | v1_xboole_0(k1_zfmisc_1(A_9)))), inference(resolution, [status(thm)], [c_340, c_10])).
% 2.35/1.51  tff(c_350, plain, (![B_65, A_66]: (r1_tarski(B_65, A_66) | ~m1_subset_1(B_65, k1_zfmisc_1(A_66)))), inference(negUnitSimplification, [status(thm)], [c_34, c_344])).
% 2.35/1.51  tff(c_359, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_350])).
% 2.35/1.51  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.35/1.51  tff(c_363, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_359, c_4])).
% 2.35/1.51  tff(c_266, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_46])).
% 2.35/1.51  tff(c_273, plain, (![A_57, B_58]: (k2_xboole_0(A_57, B_58)=B_58 | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.35/1.51  tff(c_280, plain, (k2_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_266, c_273])).
% 2.35/1.51  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.35/1.51  tff(c_285, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_280, c_2])).
% 2.35/1.51  tff(c_414, plain, (![A_74, B_75]: (k4_xboole_0(A_74, B_75)=k3_subset_1(A_74, B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.35/1.51  tff(c_427, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_36, c_414])).
% 2.35/1.51  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.35/1.51  tff(c_432, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_427, c_8])).
% 2.35/1.51  tff(c_444, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_363, c_285, c_432])).
% 2.35/1.51  tff(c_446, plain, $false, inference(negUnitSimplification, [status(thm)], [c_265, c_444])).
% 2.35/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.51  
% 2.35/1.51  Inference rules
% 2.35/1.51  ----------------------
% 2.35/1.51  #Ref     : 0
% 2.35/1.51  #Sup     : 94
% 2.35/1.51  #Fact    : 0
% 2.35/1.51  #Define  : 0
% 2.35/1.51  #Split   : 1
% 2.35/1.51  #Chain   : 0
% 2.35/1.51  #Close   : 0
% 2.35/1.51  
% 2.35/1.51  Ordering : KBO
% 2.35/1.51  
% 2.35/1.51  Simplification rules
% 2.35/1.51  ----------------------
% 2.35/1.51  #Subsume      : 8
% 2.35/1.51  #Demod        : 20
% 2.35/1.51  #Tautology    : 60
% 2.35/1.51  #SimpNegUnit  : 8
% 2.35/1.51  #BackRed      : 2
% 2.35/1.51  
% 2.35/1.51  #Partial instantiations: 0
% 2.35/1.51  #Strategies tried      : 1
% 2.35/1.51  
% 2.35/1.51  Timing (in seconds)
% 2.35/1.51  ----------------------
% 2.35/1.51  Preprocessing        : 0.38
% 2.35/1.51  Parsing              : 0.21
% 2.35/1.51  CNF conversion       : 0.02
% 2.35/1.51  Main loop            : 0.22
% 2.35/1.51  Inferencing          : 0.08
% 2.35/1.51  Reduction            : 0.07
% 2.35/1.51  Demodulation         : 0.05
% 2.35/1.51  BG Simplification    : 0.01
% 2.35/1.51  Subsumption          : 0.03
% 2.35/1.51  Abstraction          : 0.01
% 2.35/1.51  MUC search           : 0.00
% 2.35/1.51  Cooper               : 0.00
% 2.35/1.51  Total                : 0.63
% 2.35/1.51  Index Insertion      : 0.00
% 2.35/1.51  Index Deletion       : 0.00
% 2.35/1.51  Index Matching       : 0.00
% 2.35/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
