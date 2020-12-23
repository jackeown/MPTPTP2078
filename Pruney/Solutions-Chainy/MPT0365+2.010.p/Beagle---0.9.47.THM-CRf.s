%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:43 EST 2020

% Result     : Theorem 10.29s
% Output     : CNFRefutation 10.44s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 131 expanded)
%              Number of leaves         :   32 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :   80 ( 210 expanded)
%              Number of equality atoms :   45 (  86 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ( r1_xboole_0(B,C)
                & r1_xboole_0(k3_subset_1(A,B),k3_subset_1(A,C)) )
             => B = k3_subset_1(A,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | k4_xboole_0(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_36,plain,(
    k3_subset_1('#skF_1','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_216,plain,(
    ! [A_70,B_71] :
      ( k4_xboole_0(A_70,B_71) = k3_subset_1(A_70,B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_224,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_216])).

tff(c_40,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_62,plain,(
    ! [A_49,B_50] :
      ( k3_xboole_0(A_49,B_50) = k1_xboole_0
      | ~ r1_xboole_0(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_70,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_62])).

tff(c_8,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_74,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_8])).

tff(c_38,plain,(
    r1_xboole_0(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_84,plain,(
    r1_xboole_0(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_6])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_136,plain,(
    k3_xboole_0(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_84,c_2])).

tff(c_44,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_223,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_216])).

tff(c_327,plain,(
    ! [A_82,B_83,C_84] : k3_xboole_0(k4_xboole_0(A_82,B_83),k4_xboole_0(A_82,C_84)) = k4_xboole_0(A_82,k2_xboole_0(B_83,C_84)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_651,plain,(
    ! [C_105] : k3_xboole_0(k3_subset_1('#skF_1','#skF_3'),k4_xboole_0('#skF_1',C_105)) = k4_xboole_0('#skF_1',k2_xboole_0('#skF_3',C_105)) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_327])).

tff(c_674,plain,(
    k3_xboole_0(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) = k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_651])).

tff(c_677,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_674])).

tff(c_196,plain,(
    ! [A_67,B_68,C_69] : k4_xboole_0(k4_xboole_0(A_67,B_68),C_69) = k4_xboole_0(A_67,k2_xboole_0(B_68,C_69)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( k2_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = B_13
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2735,plain,(
    ! [C_145,A_146,B_147] :
      ( k2_xboole_0(C_145,k4_xboole_0(A_146,k2_xboole_0(B_147,C_145))) = k4_xboole_0(A_146,B_147)
      | ~ r1_tarski(C_145,k4_xboole_0(A_146,B_147)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_16])).

tff(c_2823,plain,
    ( k4_xboole_0('#skF_1','#skF_3') = k2_xboole_0('#skF_2',k1_xboole_0)
    | ~ r1_tarski('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_677,c_2735])).

tff(c_2887,plain,
    ( k3_subset_1('#skF_1','#skF_3') = '#skF_2'
    | ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_74,c_224,c_2823])).

tff(c_2888,plain,(
    ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_2887])).

tff(c_2898,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_2888])).

tff(c_251,plain,(
    ! [A_72,B_73] :
      ( k3_subset_1(A_72,k3_subset_1(A_72,B_73)) = B_73
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_256,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_44,c_251])).

tff(c_270,plain,(
    ! [A_74,B_75] :
      ( m1_subset_1(k3_subset_1(A_74,B_75),k1_zfmisc_1(A_74))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,(
    ! [A_38,B_39] :
      ( k4_xboole_0(A_38,B_39) = k3_subset_1(A_38,B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2578,plain,(
    ! [A_143,B_144] :
      ( k4_xboole_0(A_143,k3_subset_1(A_143,B_144)) = k3_subset_1(A_143,k3_subset_1(A_143,B_144))
      | ~ m1_subset_1(B_144,k1_zfmisc_1(A_143)) ) ),
    inference(resolution,[status(thm)],[c_270,c_30])).

tff(c_2582,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_2578])).

tff(c_2587,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_2582])).

tff(c_257,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_42,c_251])).

tff(c_2584,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_42,c_2578])).

tff(c_2589,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_2584])).

tff(c_18,plain,(
    ! [A_14,B_15,C_16] : k3_xboole_0(k4_xboole_0(A_14,B_15),k4_xboole_0(A_14,C_16)) = k4_xboole_0(A_14,k2_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18855,plain,(
    ! [B_303] : k4_xboole_0('#skF_1',k2_xboole_0(B_303,k3_subset_1('#skF_1','#skF_3'))) = k3_xboole_0(k4_xboole_0('#skF_1',B_303),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2589,c_18])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] : k4_xboole_0(k4_xboole_0(A_9,B_10),C_11) = k4_xboole_0(A_9,k2_xboole_0(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2620,plain,(
    ! [C_11] : k4_xboole_0('#skF_1',k2_xboole_0(k3_subset_1('#skF_1','#skF_2'),C_11)) = k4_xboole_0('#skF_2',C_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_2587,c_14])).

tff(c_18928,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')),'#skF_3') = k4_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_18855,c_2620])).

tff(c_19043,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2587,c_18928])).

tff(c_19045,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2898,c_19043])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:34:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.29/4.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.38/4.35  
% 10.38/4.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.38/4.36  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 10.38/4.36  
% 10.38/4.36  %Foreground sorts:
% 10.38/4.36  
% 10.38/4.36  
% 10.38/4.36  %Background operators:
% 10.38/4.36  
% 10.38/4.36  
% 10.38/4.36  %Foreground operators:
% 10.38/4.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.38/4.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.38/4.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.38/4.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.38/4.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.38/4.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.38/4.36  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 10.38/4.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.38/4.36  tff('#skF_2', type, '#skF_2': $i).
% 10.38/4.36  tff('#skF_3', type, '#skF_3': $i).
% 10.38/4.36  tff('#skF_1', type, '#skF_1': $i).
% 10.38/4.36  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.38/4.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.38/4.36  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 10.38/4.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.38/4.36  tff(k3_tarski, type, k3_tarski: $i > $i).
% 10.38/4.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.38/4.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.38/4.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.38/4.36  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 10.38/4.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.38/4.36  
% 10.44/4.37  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 10.44/4.37  tff(f_81, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_xboole_0(B, C) & r1_xboole_0(k3_subset_1(A, B), k3_subset_1(A, C))) => (B = k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_subset_1)).
% 10.44/4.37  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 10.44/4.37  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 10.44/4.37  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 10.44/4.37  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 10.44/4.37  tff(f_47, axiom, (![A, B, C]: (k4_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_xboole_1)).
% 10.44/4.37  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 10.44/4.37  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 10.44/4.37  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 10.44/4.37  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 10.44/4.37  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | k4_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.44/4.37  tff(c_36, plain, (k3_subset_1('#skF_1', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.44/4.37  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.44/4.37  tff(c_216, plain, (![A_70, B_71]: (k4_xboole_0(A_70, B_71)=k3_subset_1(A_70, B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.44/4.37  tff(c_224, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_216])).
% 10.44/4.37  tff(c_40, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.44/4.37  tff(c_62, plain, (![A_49, B_50]: (k3_xboole_0(A_49, B_50)=k1_xboole_0 | ~r1_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.44/4.37  tff(c_70, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_62])).
% 10.44/4.37  tff(c_8, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k3_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.44/4.37  tff(c_74, plain, (k2_xboole_0('#skF_2', k1_xboole_0)='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_70, c_8])).
% 10.44/4.37  tff(c_38, plain, (r1_xboole_0(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.44/4.37  tff(c_6, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.44/4.37  tff(c_84, plain, (r1_xboole_0(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_6])).
% 10.44/4.37  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.44/4.37  tff(c_136, plain, (k3_xboole_0(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_84, c_2])).
% 10.44/4.37  tff(c_44, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.44/4.37  tff(c_223, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_216])).
% 10.44/4.37  tff(c_327, plain, (![A_82, B_83, C_84]: (k3_xboole_0(k4_xboole_0(A_82, B_83), k4_xboole_0(A_82, C_84))=k4_xboole_0(A_82, k2_xboole_0(B_83, C_84)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.44/4.37  tff(c_651, plain, (![C_105]: (k3_xboole_0(k3_subset_1('#skF_1', '#skF_3'), k4_xboole_0('#skF_1', C_105))=k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', C_105)))), inference(superposition, [status(thm), theory('equality')], [c_224, c_327])).
% 10.44/4.37  tff(c_674, plain, (k3_xboole_0(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2'))=k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_223, c_651])).
% 10.44/4.37  tff(c_677, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_136, c_674])).
% 10.44/4.37  tff(c_196, plain, (![A_67, B_68, C_69]: (k4_xboole_0(k4_xboole_0(A_67, B_68), C_69)=k4_xboole_0(A_67, k2_xboole_0(B_68, C_69)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.44/4.37  tff(c_16, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k4_xboole_0(B_13, A_12))=B_13 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.44/4.37  tff(c_2735, plain, (![C_145, A_146, B_147]: (k2_xboole_0(C_145, k4_xboole_0(A_146, k2_xboole_0(B_147, C_145)))=k4_xboole_0(A_146, B_147) | ~r1_tarski(C_145, k4_xboole_0(A_146, B_147)))), inference(superposition, [status(thm), theory('equality')], [c_196, c_16])).
% 10.44/4.37  tff(c_2823, plain, (k4_xboole_0('#skF_1', '#skF_3')=k2_xboole_0('#skF_2', k1_xboole_0) | ~r1_tarski('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_677, c_2735])).
% 10.44/4.37  tff(c_2887, plain, (k3_subset_1('#skF_1', '#skF_3')='#skF_2' | ~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_224, c_74, c_224, c_2823])).
% 10.44/4.37  tff(c_2888, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_36, c_2887])).
% 10.44/4.37  tff(c_2898, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_2888])).
% 10.44/4.37  tff(c_251, plain, (![A_72, B_73]: (k3_subset_1(A_72, k3_subset_1(A_72, B_73))=B_73 | ~m1_subset_1(B_73, k1_zfmisc_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.44/4.37  tff(c_256, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_44, c_251])).
% 10.44/4.37  tff(c_270, plain, (![A_74, B_75]: (m1_subset_1(k3_subset_1(A_74, B_75), k1_zfmisc_1(A_74)) | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.44/4.37  tff(c_30, plain, (![A_38, B_39]: (k4_xboole_0(A_38, B_39)=k3_subset_1(A_38, B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.44/4.37  tff(c_2578, plain, (![A_143, B_144]: (k4_xboole_0(A_143, k3_subset_1(A_143, B_144))=k3_subset_1(A_143, k3_subset_1(A_143, B_144)) | ~m1_subset_1(B_144, k1_zfmisc_1(A_143)))), inference(resolution, [status(thm)], [c_270, c_30])).
% 10.44/4.37  tff(c_2582, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_44, c_2578])).
% 10.44/4.37  tff(c_2587, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_256, c_2582])).
% 10.44/4.37  tff(c_257, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_42, c_251])).
% 10.44/4.37  tff(c_2584, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_42, c_2578])).
% 10.44/4.37  tff(c_2589, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_257, c_2584])).
% 10.44/4.37  tff(c_18, plain, (![A_14, B_15, C_16]: (k3_xboole_0(k4_xboole_0(A_14, B_15), k4_xboole_0(A_14, C_16))=k4_xboole_0(A_14, k2_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.44/4.37  tff(c_18855, plain, (![B_303]: (k4_xboole_0('#skF_1', k2_xboole_0(B_303, k3_subset_1('#skF_1', '#skF_3')))=k3_xboole_0(k4_xboole_0('#skF_1', B_303), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2589, c_18])).
% 10.44/4.37  tff(c_14, plain, (![A_9, B_10, C_11]: (k4_xboole_0(k4_xboole_0(A_9, B_10), C_11)=k4_xboole_0(A_9, k2_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.44/4.37  tff(c_2620, plain, (![C_11]: (k4_xboole_0('#skF_1', k2_xboole_0(k3_subset_1('#skF_1', '#skF_2'), C_11))=k4_xboole_0('#skF_2', C_11))), inference(superposition, [status(thm), theory('equality')], [c_2587, c_14])).
% 10.44/4.37  tff(c_18928, plain, (k3_xboole_0(k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2')), '#skF_3')=k4_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_18855, c_2620])).
% 10.44/4.37  tff(c_19043, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2587, c_18928])).
% 10.44/4.37  tff(c_19045, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2898, c_19043])).
% 10.44/4.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.44/4.37  
% 10.44/4.37  Inference rules
% 10.44/4.37  ----------------------
% 10.44/4.37  #Ref     : 0
% 10.44/4.37  #Sup     : 4884
% 10.44/4.37  #Fact    : 0
% 10.44/4.37  #Define  : 0
% 10.44/4.37  #Split   : 27
% 10.44/4.37  #Chain   : 0
% 10.44/4.37  #Close   : 0
% 10.44/4.37  
% 10.44/4.37  Ordering : KBO
% 10.44/4.37  
% 10.44/4.37  Simplification rules
% 10.44/4.37  ----------------------
% 10.44/4.37  #Subsume      : 752
% 10.44/4.37  #Demod        : 4719
% 10.44/4.37  #Tautology    : 1955
% 10.44/4.37  #SimpNegUnit  : 33
% 10.44/4.37  #BackRed      : 13
% 10.44/4.37  
% 10.44/4.37  #Partial instantiations: 0
% 10.44/4.37  #Strategies tried      : 1
% 10.44/4.37  
% 10.44/4.37  Timing (in seconds)
% 10.44/4.37  ----------------------
% 10.44/4.37  Preprocessing        : 0.30
% 10.44/4.37  Parsing              : 0.16
% 10.44/4.37  CNF conversion       : 0.02
% 10.44/4.37  Main loop            : 3.25
% 10.44/4.37  Inferencing          : 0.69
% 10.44/4.37  Reduction            : 1.76
% 10.44/4.37  Demodulation         : 1.49
% 10.44/4.37  BG Simplification    : 0.10
% 10.44/4.37  Subsumption          : 0.53
% 10.44/4.37  Abstraction          : 0.15
% 10.44/4.38  MUC search           : 0.00
% 10.44/4.38  Cooper               : 0.00
% 10.44/4.38  Total                : 3.58
% 10.44/4.38  Index Insertion      : 0.00
% 10.44/4.38  Index Deletion       : 0.00
% 10.44/4.38  Index Matching       : 0.00
% 10.44/4.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
