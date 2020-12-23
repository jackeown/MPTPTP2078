%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:34 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 120 expanded)
%              Number of leaves         :   31 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :   88 ( 183 expanded)
%              Number of equality atoms :   46 (  70 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_62,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_60,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_32,plain,(
    ! [A_30] : v1_relat_1(k6_relat_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_34,plain,(
    ! [A_30] : v4_relat_1(k6_relat_1(A_30),A_30) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_98,plain,(
    ! [B_48,A_49] :
      ( k7_relat_1(B_48,A_49) = B_48
      | ~ v4_relat_1(B_48,A_49)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_101,plain,(
    ! [A_30] :
      ( k7_relat_1(k6_relat_1(A_30),A_30) = k6_relat_1(A_30)
      | ~ v1_relat_1(k6_relat_1(A_30)) ) ),
    inference(resolution,[status(thm)],[c_34,c_98])).

tff(c_104,plain,(
    ! [A_30] : k7_relat_1(k6_relat_1(A_30),A_30) = k6_relat_1(A_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_101])).

tff(c_394,plain,(
    ! [C_71,A_72,B_73] :
      ( k7_relat_1(k7_relat_1(C_71,A_72),B_73) = k7_relat_1(C_71,k3_xboole_0(A_72,B_73))
      | ~ v1_relat_1(C_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_430,plain,(
    ! [A_30,B_73] :
      ( k7_relat_1(k6_relat_1(A_30),k3_xboole_0(A_30,B_73)) = k7_relat_1(k6_relat_1(A_30),B_73)
      | ~ v1_relat_1(k6_relat_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_394])).

tff(c_434,plain,(
    ! [A_30,B_73] : k7_relat_1(k6_relat_1(A_30),k3_xboole_0(A_30,B_73)) = k7_relat_1(k6_relat_1(A_30),B_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_430])).

tff(c_22,plain,(
    ! [A_21] : k4_relat_1(k6_relat_1(A_21)) = k6_relat_1(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_20] : k1_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_258,plain,(
    ! [B_64,A_65] :
      ( k7_relat_1(B_64,A_65) = B_64
      | ~ r1_tarski(k1_relat_1(B_64),A_65)
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_274,plain,(
    ! [A_20,A_65] :
      ( k7_relat_1(k6_relat_1(A_20),A_65) = k6_relat_1(A_20)
      | ~ r1_tarski(A_20,A_65)
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_258])).

tff(c_435,plain,(
    ! [A_74,A_75] :
      ( k7_relat_1(k6_relat_1(A_74),A_75) = k6_relat_1(A_74)
      | ~ r1_tarski(A_74,A_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_274])).

tff(c_133,plain,(
    ! [B_53,A_54] :
      ( k3_xboole_0(k1_relat_1(B_53),A_54) = k1_relat_1(k7_relat_1(B_53,A_54))
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_145,plain,(
    ! [A_20,A_54] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_20),A_54)) = k3_xboole_0(A_20,A_54)
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_133])).

tff(c_149,plain,(
    ! [A_20,A_54] : k1_relat_1(k7_relat_1(k6_relat_1(A_20),A_54)) = k3_xboole_0(A_20,A_54) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_145])).

tff(c_458,plain,(
    ! [A_74,A_75] :
      ( k3_xboole_0(A_74,A_75) = k1_relat_1(k6_relat_1(A_74))
      | ~ r1_tarski(A_74,A_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_149])).

tff(c_499,plain,(
    ! [A_76,A_77] :
      ( k3_xboole_0(A_76,A_77) = A_76
      | ~ r1_tarski(A_76,A_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_458])).

tff(c_512,plain,(
    ! [A_1,B_2] : k3_xboole_0(k3_xboole_0(A_1,B_2),A_1) = k3_xboole_0(A_1,B_2) ),
    inference(resolution,[status(thm)],[c_2,c_499])).

tff(c_619,plain,(
    ! [A_84,B_85] : k7_relat_1(k6_relat_1(A_84),k3_xboole_0(A_84,B_85)) = k7_relat_1(k6_relat_1(A_84),B_85) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_430])).

tff(c_643,plain,(
    ! [A_1,B_2] : k7_relat_1(k6_relat_1(k3_xboole_0(A_1,B_2)),k3_xboole_0(A_1,B_2)) = k7_relat_1(k6_relat_1(k3_xboole_0(A_1,B_2)),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_512,c_619])).

tff(c_663,plain,(
    ! [A_1,B_2] : k7_relat_1(k6_relat_1(k3_xboole_0(A_1,B_2)),A_1) = k6_relat_1(k3_xboole_0(A_1,B_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_643])).

tff(c_28,plain,(
    ! [A_26,B_27] :
      ( k5_relat_1(k6_relat_1(A_26),B_27) = k7_relat_1(B_27,A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_542,plain,(
    ! [B_80,A_81] :
      ( k5_relat_1(k4_relat_1(B_80),k4_relat_1(A_81)) = k4_relat_1(k5_relat_1(A_81,B_80))
      | ~ v1_relat_1(B_80)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_557,plain,(
    ! [B_80,A_21] :
      ( k5_relat_1(k4_relat_1(B_80),k6_relat_1(A_21)) = k4_relat_1(k5_relat_1(k6_relat_1(A_21),B_80))
      | ~ v1_relat_1(B_80)
      | ~ v1_relat_1(k6_relat_1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_542])).

tff(c_889,plain,(
    ! [B_96,A_97] :
      ( k5_relat_1(k4_relat_1(B_96),k6_relat_1(A_97)) = k4_relat_1(k5_relat_1(k6_relat_1(A_97),B_96))
      | ~ v1_relat_1(B_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_557])).

tff(c_901,plain,(
    ! [A_97,A_21] :
      ( k4_relat_1(k5_relat_1(k6_relat_1(A_97),k6_relat_1(A_21))) = k5_relat_1(k6_relat_1(A_21),k6_relat_1(A_97))
      | ~ v1_relat_1(k6_relat_1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_889])).

tff(c_925,plain,(
    ! [A_100,A_101] : k4_relat_1(k5_relat_1(k6_relat_1(A_100),k6_relat_1(A_101))) = k5_relat_1(k6_relat_1(A_101),k6_relat_1(A_100)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_901])).

tff(c_957,plain,(
    ! [A_101,A_26] :
      ( k5_relat_1(k6_relat_1(A_101),k6_relat_1(A_26)) = k4_relat_1(k7_relat_1(k6_relat_1(A_101),A_26))
      | ~ v1_relat_1(k6_relat_1(A_101)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_925])).

tff(c_1060,plain,(
    ! [A_106,A_107] : k5_relat_1(k6_relat_1(A_106),k6_relat_1(A_107)) = k4_relat_1(k7_relat_1(k6_relat_1(A_106),A_107)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_957])).

tff(c_1077,plain,(
    ! [A_106,A_107] :
      ( k4_relat_1(k7_relat_1(k6_relat_1(A_106),A_107)) = k7_relat_1(k6_relat_1(A_107),A_106)
      | ~ v1_relat_1(k6_relat_1(A_107)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1060,c_28])).

tff(c_1197,plain,(
    ! [A_114,A_115] : k4_relat_1(k7_relat_1(k6_relat_1(A_114),A_115)) = k7_relat_1(k6_relat_1(A_115),A_114) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1077])).

tff(c_1218,plain,(
    ! [A_1,B_2] : k7_relat_1(k6_relat_1(A_1),k3_xboole_0(A_1,B_2)) = k4_relat_1(k6_relat_1(k3_xboole_0(A_1,B_2))) ),
    inference(superposition,[status(thm),theory(equality)],[c_663,c_1197])).

tff(c_1242,plain,(
    ! [A_1,B_2] : k7_relat_1(k6_relat_1(A_1),B_2) = k6_relat_1(k3_xboole_0(A_1,B_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_22,c_1218])).

tff(c_114,plain,(
    ! [A_51,B_52] :
      ( k5_relat_1(k6_relat_1(A_51),B_52) = k7_relat_1(B_52,A_51)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_38,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_123,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_38])).

tff(c_131,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_123])).

tff(c_1257,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1242,c_131])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:37:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.99/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.42  
% 2.99/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.43  %$ v5_relat_1 > v4_relat_1 > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.99/1.43  
% 2.99/1.43  %Foreground sorts:
% 2.99/1.43  
% 2.99/1.43  
% 2.99/1.43  %Background operators:
% 2.99/1.43  
% 2.99/1.43  
% 2.99/1.43  %Foreground operators:
% 2.99/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.43  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.99/1.43  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.99/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.99/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.99/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.99/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.99/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.99/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.99/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.99/1.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.99/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.99/1.43  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.99/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.99/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.99/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.99/1.43  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.99/1.43  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.99/1.43  
% 2.99/1.44  tff(f_88, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc24_relat_1)).
% 2.99/1.44  tff(f_49, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.99/1.44  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 2.99/1.44  tff(f_62, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_relat_1)).
% 2.99/1.44  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.99/1.44  tff(f_60, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.99/1.44  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 2.99/1.44  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.99/1.44  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.99/1.44  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 2.99/1.44  tff(f_91, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 2.99/1.44  tff(c_32, plain, (![A_30]: (v1_relat_1(k6_relat_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.99/1.44  tff(c_34, plain, (![A_30]: (v4_relat_1(k6_relat_1(A_30), A_30))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.99/1.44  tff(c_98, plain, (![B_48, A_49]: (k7_relat_1(B_48, A_49)=B_48 | ~v4_relat_1(B_48, A_49) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.99/1.44  tff(c_101, plain, (![A_30]: (k7_relat_1(k6_relat_1(A_30), A_30)=k6_relat_1(A_30) | ~v1_relat_1(k6_relat_1(A_30)))), inference(resolution, [status(thm)], [c_34, c_98])).
% 2.99/1.44  tff(c_104, plain, (![A_30]: (k7_relat_1(k6_relat_1(A_30), A_30)=k6_relat_1(A_30))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_101])).
% 2.99/1.44  tff(c_394, plain, (![C_71, A_72, B_73]: (k7_relat_1(k7_relat_1(C_71, A_72), B_73)=k7_relat_1(C_71, k3_xboole_0(A_72, B_73)) | ~v1_relat_1(C_71))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.99/1.44  tff(c_430, plain, (![A_30, B_73]: (k7_relat_1(k6_relat_1(A_30), k3_xboole_0(A_30, B_73))=k7_relat_1(k6_relat_1(A_30), B_73) | ~v1_relat_1(k6_relat_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_104, c_394])).
% 2.99/1.44  tff(c_434, plain, (![A_30, B_73]: (k7_relat_1(k6_relat_1(A_30), k3_xboole_0(A_30, B_73))=k7_relat_1(k6_relat_1(A_30), B_73))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_430])).
% 2.99/1.44  tff(c_22, plain, (![A_21]: (k4_relat_1(k6_relat_1(A_21))=k6_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.99/1.44  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.99/1.44  tff(c_18, plain, (![A_20]: (k1_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.99/1.44  tff(c_258, plain, (![B_64, A_65]: (k7_relat_1(B_64, A_65)=B_64 | ~r1_tarski(k1_relat_1(B_64), A_65) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.99/1.44  tff(c_274, plain, (![A_20, A_65]: (k7_relat_1(k6_relat_1(A_20), A_65)=k6_relat_1(A_20) | ~r1_tarski(A_20, A_65) | ~v1_relat_1(k6_relat_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_258])).
% 2.99/1.44  tff(c_435, plain, (![A_74, A_75]: (k7_relat_1(k6_relat_1(A_74), A_75)=k6_relat_1(A_74) | ~r1_tarski(A_74, A_75))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_274])).
% 2.99/1.44  tff(c_133, plain, (![B_53, A_54]: (k3_xboole_0(k1_relat_1(B_53), A_54)=k1_relat_1(k7_relat_1(B_53, A_54)) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.99/1.44  tff(c_145, plain, (![A_20, A_54]: (k1_relat_1(k7_relat_1(k6_relat_1(A_20), A_54))=k3_xboole_0(A_20, A_54) | ~v1_relat_1(k6_relat_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_133])).
% 2.99/1.44  tff(c_149, plain, (![A_20, A_54]: (k1_relat_1(k7_relat_1(k6_relat_1(A_20), A_54))=k3_xboole_0(A_20, A_54))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_145])).
% 2.99/1.44  tff(c_458, plain, (![A_74, A_75]: (k3_xboole_0(A_74, A_75)=k1_relat_1(k6_relat_1(A_74)) | ~r1_tarski(A_74, A_75))), inference(superposition, [status(thm), theory('equality')], [c_435, c_149])).
% 2.99/1.44  tff(c_499, plain, (![A_76, A_77]: (k3_xboole_0(A_76, A_77)=A_76 | ~r1_tarski(A_76, A_77))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_458])).
% 2.99/1.44  tff(c_512, plain, (![A_1, B_2]: (k3_xboole_0(k3_xboole_0(A_1, B_2), A_1)=k3_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_2, c_499])).
% 2.99/1.44  tff(c_619, plain, (![A_84, B_85]: (k7_relat_1(k6_relat_1(A_84), k3_xboole_0(A_84, B_85))=k7_relat_1(k6_relat_1(A_84), B_85))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_430])).
% 2.99/1.44  tff(c_643, plain, (![A_1, B_2]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_1, B_2)), k3_xboole_0(A_1, B_2))=k7_relat_1(k6_relat_1(k3_xboole_0(A_1, B_2)), A_1))), inference(superposition, [status(thm), theory('equality')], [c_512, c_619])).
% 2.99/1.44  tff(c_663, plain, (![A_1, B_2]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_1, B_2)), A_1)=k6_relat_1(k3_xboole_0(A_1, B_2)))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_643])).
% 2.99/1.44  tff(c_28, plain, (![A_26, B_27]: (k5_relat_1(k6_relat_1(A_26), B_27)=k7_relat_1(B_27, A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.99/1.44  tff(c_542, plain, (![B_80, A_81]: (k5_relat_1(k4_relat_1(B_80), k4_relat_1(A_81))=k4_relat_1(k5_relat_1(A_81, B_80)) | ~v1_relat_1(B_80) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.99/1.44  tff(c_557, plain, (![B_80, A_21]: (k5_relat_1(k4_relat_1(B_80), k6_relat_1(A_21))=k4_relat_1(k5_relat_1(k6_relat_1(A_21), B_80)) | ~v1_relat_1(B_80) | ~v1_relat_1(k6_relat_1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_542])).
% 2.99/1.44  tff(c_889, plain, (![B_96, A_97]: (k5_relat_1(k4_relat_1(B_96), k6_relat_1(A_97))=k4_relat_1(k5_relat_1(k6_relat_1(A_97), B_96)) | ~v1_relat_1(B_96))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_557])).
% 2.99/1.44  tff(c_901, plain, (![A_97, A_21]: (k4_relat_1(k5_relat_1(k6_relat_1(A_97), k6_relat_1(A_21)))=k5_relat_1(k6_relat_1(A_21), k6_relat_1(A_97)) | ~v1_relat_1(k6_relat_1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_889])).
% 2.99/1.44  tff(c_925, plain, (![A_100, A_101]: (k4_relat_1(k5_relat_1(k6_relat_1(A_100), k6_relat_1(A_101)))=k5_relat_1(k6_relat_1(A_101), k6_relat_1(A_100)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_901])).
% 2.99/1.44  tff(c_957, plain, (![A_101, A_26]: (k5_relat_1(k6_relat_1(A_101), k6_relat_1(A_26))=k4_relat_1(k7_relat_1(k6_relat_1(A_101), A_26)) | ~v1_relat_1(k6_relat_1(A_101)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_925])).
% 2.99/1.44  tff(c_1060, plain, (![A_106, A_107]: (k5_relat_1(k6_relat_1(A_106), k6_relat_1(A_107))=k4_relat_1(k7_relat_1(k6_relat_1(A_106), A_107)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_957])).
% 2.99/1.44  tff(c_1077, plain, (![A_106, A_107]: (k4_relat_1(k7_relat_1(k6_relat_1(A_106), A_107))=k7_relat_1(k6_relat_1(A_107), A_106) | ~v1_relat_1(k6_relat_1(A_107)))), inference(superposition, [status(thm), theory('equality')], [c_1060, c_28])).
% 2.99/1.44  tff(c_1197, plain, (![A_114, A_115]: (k4_relat_1(k7_relat_1(k6_relat_1(A_114), A_115))=k7_relat_1(k6_relat_1(A_115), A_114))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1077])).
% 2.99/1.44  tff(c_1218, plain, (![A_1, B_2]: (k7_relat_1(k6_relat_1(A_1), k3_xboole_0(A_1, B_2))=k4_relat_1(k6_relat_1(k3_xboole_0(A_1, B_2))))), inference(superposition, [status(thm), theory('equality')], [c_663, c_1197])).
% 2.99/1.44  tff(c_1242, plain, (![A_1, B_2]: (k7_relat_1(k6_relat_1(A_1), B_2)=k6_relat_1(k3_xboole_0(A_1, B_2)))), inference(demodulation, [status(thm), theory('equality')], [c_434, c_22, c_1218])).
% 2.99/1.44  tff(c_114, plain, (![A_51, B_52]: (k5_relat_1(k6_relat_1(A_51), B_52)=k7_relat_1(B_52, A_51) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.99/1.44  tff(c_38, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.99/1.44  tff(c_123, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_114, c_38])).
% 2.99/1.44  tff(c_131, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_123])).
% 2.99/1.44  tff(c_1257, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1242, c_131])).
% 2.99/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.44  
% 2.99/1.44  Inference rules
% 2.99/1.44  ----------------------
% 2.99/1.44  #Ref     : 0
% 2.99/1.44  #Sup     : 272
% 2.99/1.44  #Fact    : 0
% 2.99/1.44  #Define  : 0
% 2.99/1.44  #Split   : 1
% 2.99/1.44  #Chain   : 0
% 2.99/1.44  #Close   : 0
% 2.99/1.44  
% 2.99/1.44  Ordering : KBO
% 2.99/1.44  
% 2.99/1.44  Simplification rules
% 2.99/1.44  ----------------------
% 2.99/1.44  #Subsume      : 11
% 2.99/1.44  #Demod        : 321
% 2.99/1.44  #Tautology    : 161
% 2.99/1.44  #SimpNegUnit  : 0
% 2.99/1.44  #BackRed      : 15
% 2.99/1.44  
% 2.99/1.44  #Partial instantiations: 0
% 2.99/1.44  #Strategies tried      : 1
% 2.99/1.44  
% 2.99/1.44  Timing (in seconds)
% 2.99/1.44  ----------------------
% 2.99/1.44  Preprocessing        : 0.31
% 2.99/1.44  Parsing              : 0.17
% 2.99/1.44  CNF conversion       : 0.02
% 2.99/1.44  Main loop            : 0.38
% 2.99/1.44  Inferencing          : 0.15
% 2.99/1.44  Reduction            : 0.13
% 2.99/1.44  Demodulation         : 0.10
% 2.99/1.44  BG Simplification    : 0.02
% 2.99/1.44  Subsumption          : 0.05
% 2.99/1.44  Abstraction          : 0.03
% 2.99/1.44  MUC search           : 0.00
% 2.99/1.44  Cooper               : 0.00
% 2.99/1.44  Total                : 0.72
% 2.99/1.44  Index Insertion      : 0.00
% 2.99/1.44  Index Deletion       : 0.00
% 2.99/1.44  Index Matching       : 0.00
% 2.99/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
