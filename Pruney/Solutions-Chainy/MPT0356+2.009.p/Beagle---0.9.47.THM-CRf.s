%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:56 EST 2020

% Result     : Theorem 3.66s
% Output     : CNFRefutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :   56 (  68 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   78 ( 110 expanded)
%              Number of equality atoms :   12 (  17 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,k3_subset_1(A,C))
             => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_78,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_42,plain,(
    ! [A_23] : ~ v1_xboole_0(k1_zfmisc_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_97,plain,(
    ! [B_47,A_48] :
      ( r2_hidden(B_47,A_48)
      | ~ m1_subset_1(B_47,A_48)
      | v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    ! [C_18,A_14] :
      ( r1_tarski(C_18,A_14)
      | ~ r2_hidden(C_18,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_101,plain,(
    ! [B_47,A_14] :
      ( r1_tarski(B_47,A_14)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_14))
      | v1_xboole_0(k1_zfmisc_1(A_14)) ) ),
    inference(resolution,[status(thm)],[c_97,c_20])).

tff(c_105,plain,(
    ! [B_49,A_50] :
      ( r1_tarski(B_49,A_50)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_101])).

tff(c_117,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_105])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_322,plain,(
    ! [A_75,B_76] :
      ( k4_xboole_0(A_75,B_76) = k3_subset_1(A_75,B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_338,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_322])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,C_5)
      | ~ r1_tarski(A_3,k4_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_541,plain,(
    ! [A_87] :
      ( r1_xboole_0(A_87,'#skF_5')
      | ~ r1_tarski(A_87,k3_subset_1('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_8])).

tff(c_560,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_541])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = A_6
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_566,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_560,c_12])).

tff(c_80,plain,(
    ! [A_39,C_40,B_41] :
      ( r1_xboole_0(A_39,k4_xboole_0(C_40,B_41))
      | ~ r1_tarski(A_39,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_84,plain,(
    ! [A_39,C_40,B_41] :
      ( k4_xboole_0(A_39,k4_xboole_0(C_40,B_41)) = A_39
      | ~ r1_tarski(A_39,B_41) ) ),
    inference(resolution,[status(thm)],[c_80,c_12])).

tff(c_639,plain,(
    ! [A_93] :
      ( k4_xboole_0(A_93,'#skF_4') = A_93
      | ~ r1_tarski(A_93,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_566,c_84])).

tff(c_654,plain,(
    k4_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_6,c_639])).

tff(c_168,plain,(
    ! [A_60,C_61,B_62] :
      ( r1_xboole_0(A_60,C_61)
      | ~ r1_tarski(A_60,k4_xboole_0(B_62,C_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_183,plain,(
    ! [B_62,C_61] : r1_xboole_0(k4_xboole_0(B_62,C_61),C_61) ),
    inference(resolution,[status(thm)],[c_6,c_168])).

tff(c_673,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_654,c_183])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_339,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_322])).

tff(c_454,plain,(
    ! [A_80,B_81,C_82] :
      ( r1_tarski(A_80,k4_xboole_0(B_81,C_82))
      | ~ r1_xboole_0(A_80,C_82)
      | ~ r1_tarski(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1672,plain,(
    ! [A_120] :
      ( r1_tarski(A_120,k3_subset_1('#skF_3','#skF_4'))
      | ~ r1_xboole_0(A_120,'#skF_4')
      | ~ r1_tarski(A_120,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_454])).

tff(c_44,plain,(
    ~ r1_tarski('#skF_5',k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1687,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_4')
    | ~ r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_1672,c_44])).

tff(c_1695,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_673,c_1687])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:45:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.66/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.66/1.57  
% 3.66/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.66/1.57  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.66/1.57  
% 3.66/1.57  %Foreground sorts:
% 3.66/1.57  
% 3.66/1.57  
% 3.66/1.57  %Background operators:
% 3.66/1.57  
% 3.66/1.57  
% 3.66/1.57  %Foreground operators:
% 3.66/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.66/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.66/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.66/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.66/1.57  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.66/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.66/1.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.66/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.66/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.66/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.66/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.66/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.66/1.57  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.66/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.66/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.66/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.66/1.57  
% 3.66/1.59  tff(f_88, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_subset_1)).
% 3.66/1.59  tff(f_78, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.66/1.59  tff(f_71, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.66/1.59  tff(f_58, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.66/1.59  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.66/1.59  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.66/1.59  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.66/1.59  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.66/1.59  tff(f_45, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 3.66/1.59  tff(f_51, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 3.66/1.59  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.66/1.59  tff(c_42, plain, (![A_23]: (~v1_xboole_0(k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.66/1.59  tff(c_97, plain, (![B_47, A_48]: (r2_hidden(B_47, A_48) | ~m1_subset_1(B_47, A_48) | v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.66/1.59  tff(c_20, plain, (![C_18, A_14]: (r1_tarski(C_18, A_14) | ~r2_hidden(C_18, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.66/1.59  tff(c_101, plain, (![B_47, A_14]: (r1_tarski(B_47, A_14) | ~m1_subset_1(B_47, k1_zfmisc_1(A_14)) | v1_xboole_0(k1_zfmisc_1(A_14)))), inference(resolution, [status(thm)], [c_97, c_20])).
% 3.66/1.59  tff(c_105, plain, (![B_49, A_50]: (r1_tarski(B_49, A_50) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)))), inference(negUnitSimplification, [status(thm)], [c_42, c_101])).
% 3.66/1.59  tff(c_117, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_105])).
% 3.66/1.59  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.66/1.59  tff(c_46, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.66/1.59  tff(c_322, plain, (![A_75, B_76]: (k4_xboole_0(A_75, B_76)=k3_subset_1(A_75, B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.66/1.59  tff(c_338, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_322])).
% 3.66/1.59  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, C_5) | ~r1_tarski(A_3, k4_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.66/1.59  tff(c_541, plain, (![A_87]: (r1_xboole_0(A_87, '#skF_5') | ~r1_tarski(A_87, k3_subset_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_338, c_8])).
% 3.66/1.59  tff(c_560, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_541])).
% 3.66/1.59  tff(c_12, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=A_6 | ~r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.66/1.59  tff(c_566, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_560, c_12])).
% 3.66/1.59  tff(c_80, plain, (![A_39, C_40, B_41]: (r1_xboole_0(A_39, k4_xboole_0(C_40, B_41)) | ~r1_tarski(A_39, B_41))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.66/1.59  tff(c_84, plain, (![A_39, C_40, B_41]: (k4_xboole_0(A_39, k4_xboole_0(C_40, B_41))=A_39 | ~r1_tarski(A_39, B_41))), inference(resolution, [status(thm)], [c_80, c_12])).
% 3.66/1.59  tff(c_639, plain, (![A_93]: (k4_xboole_0(A_93, '#skF_4')=A_93 | ~r1_tarski(A_93, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_566, c_84])).
% 3.66/1.59  tff(c_654, plain, (k4_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_6, c_639])).
% 3.66/1.59  tff(c_168, plain, (![A_60, C_61, B_62]: (r1_xboole_0(A_60, C_61) | ~r1_tarski(A_60, k4_xboole_0(B_62, C_61)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.66/1.59  tff(c_183, plain, (![B_62, C_61]: (r1_xboole_0(k4_xboole_0(B_62, C_61), C_61))), inference(resolution, [status(thm)], [c_6, c_168])).
% 3.66/1.59  tff(c_673, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_654, c_183])).
% 3.66/1.59  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.66/1.59  tff(c_339, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_322])).
% 3.66/1.59  tff(c_454, plain, (![A_80, B_81, C_82]: (r1_tarski(A_80, k4_xboole_0(B_81, C_82)) | ~r1_xboole_0(A_80, C_82) | ~r1_tarski(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.66/1.59  tff(c_1672, plain, (![A_120]: (r1_tarski(A_120, k3_subset_1('#skF_3', '#skF_4')) | ~r1_xboole_0(A_120, '#skF_4') | ~r1_tarski(A_120, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_339, c_454])).
% 3.66/1.59  tff(c_44, plain, (~r1_tarski('#skF_5', k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.66/1.59  tff(c_1687, plain, (~r1_xboole_0('#skF_5', '#skF_4') | ~r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_1672, c_44])).
% 3.66/1.59  tff(c_1695, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_117, c_673, c_1687])).
% 3.66/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.66/1.59  
% 3.66/1.59  Inference rules
% 3.66/1.59  ----------------------
% 3.66/1.59  #Ref     : 0
% 3.66/1.59  #Sup     : 395
% 3.66/1.59  #Fact    : 0
% 3.66/1.59  #Define  : 0
% 3.66/1.59  #Split   : 3
% 3.66/1.59  #Chain   : 0
% 3.66/1.59  #Close   : 0
% 3.66/1.59  
% 3.66/1.59  Ordering : KBO
% 3.66/1.59  
% 3.66/1.59  Simplification rules
% 3.66/1.59  ----------------------
% 3.66/1.59  #Subsume      : 49
% 3.66/1.59  #Demod        : 208
% 3.66/1.59  #Tautology    : 220
% 3.66/1.59  #SimpNegUnit  : 2
% 3.66/1.59  #BackRed      : 0
% 3.66/1.59  
% 3.66/1.59  #Partial instantiations: 0
% 3.66/1.59  #Strategies tried      : 1
% 3.66/1.59  
% 3.66/1.59  Timing (in seconds)
% 3.66/1.59  ----------------------
% 3.66/1.59  Preprocessing        : 0.30
% 3.66/1.59  Parsing              : 0.15
% 3.66/1.59  CNF conversion       : 0.02
% 3.66/1.59  Main loop            : 0.49
% 3.66/1.59  Inferencing          : 0.18
% 3.66/1.59  Reduction            : 0.17
% 3.66/1.59  Demodulation         : 0.12
% 3.66/1.59  BG Simplification    : 0.03
% 3.66/1.59  Subsumption          : 0.10
% 3.66/1.59  Abstraction          : 0.02
% 3.66/1.59  MUC search           : 0.00
% 3.66/1.59  Cooper               : 0.00
% 3.66/1.59  Total                : 0.82
% 3.66/1.59  Index Insertion      : 0.00
% 3.66/1.59  Index Deletion       : 0.00
% 3.66/1.59  Index Matching       : 0.00
% 3.66/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
