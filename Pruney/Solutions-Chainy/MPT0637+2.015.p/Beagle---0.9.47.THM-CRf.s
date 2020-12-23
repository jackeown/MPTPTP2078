%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:26 EST 2020

% Result     : Theorem 6.37s
% Output     : CNFRefutation 6.45s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 150 expanded)
%              Number of leaves         :   35 (  68 expanded)
%              Depth                    :   11
%              Number of atoms          :  103 ( 212 expanded)
%              Number of equality atoms :   46 (  83 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_51,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k8_relat_1(A,k5_relat_1(B,C)) = k5_relat_1(B,k8_relat_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_105,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_109,plain,(
    ! [A_68,B_69] : k1_setfam_1(k2_tarski(A_68,B_69)) = k3_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_124,plain,(
    ! [B_70,A_71] : k1_setfam_1(k2_tarski(B_70,A_71)) = k3_xboole_0(A_71,B_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_109])).

tff(c_18,plain,(
    ! [A_32,B_33] : k1_setfam_1(k2_tarski(A_32,B_33)) = k3_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_147,plain,(
    ! [B_72,A_73] : k3_xboole_0(B_72,A_73) = k3_xboole_0(A_73,B_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_18])).

tff(c_162,plain,(
    ! [B_72,A_73] : r1_tarski(k3_xboole_0(B_72,A_73),A_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_2])).

tff(c_22,plain,(
    ! [A_36] : v1_relat_1(k6_relat_1(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_317,plain,(
    ! [A_86,B_87] :
      ( k5_relat_1(k6_relat_1(A_86),B_87) = k7_relat_1(B_87,A_86)
      | ~ v1_relat_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_26,plain,(
    ! [B_42,A_41] :
      ( k5_relat_1(B_42,k6_relat_1(A_41)) = k8_relat_1(A_41,B_42)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_324,plain,(
    ! [A_41,A_86] :
      ( k8_relat_1(A_41,k6_relat_1(A_86)) = k7_relat_1(k6_relat_1(A_41),A_86)
      | ~ v1_relat_1(k6_relat_1(A_86))
      | ~ v1_relat_1(k6_relat_1(A_41)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_26])).

tff(c_362,plain,(
    ! [A_41,A_86] : k8_relat_1(A_41,k6_relat_1(A_86)) = k7_relat_1(k6_relat_1(A_41),A_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_324])).

tff(c_34,plain,(
    ! [A_50] : k2_relat_1(k6_relat_1(A_50)) = A_50 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_580,plain,(
    ! [B_106,A_107] :
      ( k5_relat_1(B_106,k6_relat_1(A_107)) = B_106
      | ~ r1_tarski(k2_relat_1(B_106),A_107)
      | ~ v1_relat_1(B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_587,plain,(
    ! [A_50,A_107] :
      ( k5_relat_1(k6_relat_1(A_50),k6_relat_1(A_107)) = k6_relat_1(A_50)
      | ~ r1_tarski(A_50,A_107)
      | ~ v1_relat_1(k6_relat_1(A_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_580])).

tff(c_784,plain,(
    ! [A_119,A_120] :
      ( k5_relat_1(k6_relat_1(A_119),k6_relat_1(A_120)) = k6_relat_1(A_119)
      | ~ r1_tarski(A_119,A_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_587])).

tff(c_44,plain,(
    ! [A_57,B_58] :
      ( k5_relat_1(k6_relat_1(A_57),B_58) = k7_relat_1(B_58,A_57)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_796,plain,(
    ! [A_120,A_119] :
      ( k7_relat_1(k6_relat_1(A_120),A_119) = k6_relat_1(A_119)
      | ~ v1_relat_1(k6_relat_1(A_120))
      | ~ r1_tarski(A_119,A_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_784,c_44])).

tff(c_846,plain,(
    ! [A_120,A_119] :
      ( k7_relat_1(k6_relat_1(A_120),A_119) = k6_relat_1(A_119)
      | ~ r1_tarski(A_119,A_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_796])).

tff(c_397,plain,(
    ! [A_91,A_92] : k8_relat_1(A_91,k6_relat_1(A_92)) = k7_relat_1(k6_relat_1(A_91),A_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_324])).

tff(c_250,plain,(
    ! [B_81,A_82] :
      ( k5_relat_1(B_81,k6_relat_1(A_82)) = k8_relat_1(A_82,B_81)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_20,plain,(
    ! [A_34,B_35] :
      ( v1_relat_1(k5_relat_1(A_34,B_35))
      | ~ v1_relat_1(B_35)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_264,plain,(
    ! [A_82,B_81] :
      ( v1_relat_1(k8_relat_1(A_82,B_81))
      | ~ v1_relat_1(k6_relat_1(A_82))
      | ~ v1_relat_1(B_81)
      | ~ v1_relat_1(B_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_20])).

tff(c_289,plain,(
    ! [A_82,B_81] :
      ( v1_relat_1(k8_relat_1(A_82,B_81))
      | ~ v1_relat_1(B_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_264])).

tff(c_407,plain,(
    ! [A_91,A_92] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_91),A_92))
      | ~ v1_relat_1(k6_relat_1(A_92)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_289])).

tff(c_417,plain,(
    ! [A_91,A_92] : v1_relat_1(k7_relat_1(k6_relat_1(A_91),A_92)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_407])).

tff(c_32,plain,(
    ! [A_50] : k1_relat_1(k6_relat_1(A_50)) = A_50 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_486,plain,(
    ! [B_100,A_101] :
      ( k3_xboole_0(k1_relat_1(B_100),A_101) = k1_relat_1(k7_relat_1(B_100,A_101))
      | ~ v1_relat_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_515,plain,(
    ! [A_50,A_101] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_50),A_101)) = k3_xboole_0(A_50,A_101)
      | ~ v1_relat_1(k6_relat_1(A_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_486])).

tff(c_519,plain,(
    ! [A_50,A_101] : k1_relat_1(k7_relat_1(k6_relat_1(A_50),A_101)) = k3_xboole_0(A_50,A_101) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_515])).

tff(c_1840,plain,(
    ! [A_152,B_153,C_154] :
      ( k8_relat_1(A_152,k5_relat_1(B_153,C_154)) = k5_relat_1(B_153,k8_relat_1(A_152,C_154))
      | ~ v1_relat_1(C_154)
      | ~ v1_relat_1(B_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1869,plain,(
    ! [B_42,A_152,A_41] :
      ( k5_relat_1(B_42,k8_relat_1(A_152,k6_relat_1(A_41))) = k8_relat_1(A_152,k8_relat_1(A_41,B_42))
      | ~ v1_relat_1(k6_relat_1(A_41))
      | ~ v1_relat_1(B_42)
      | ~ v1_relat_1(B_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1840])).

tff(c_4716,plain,(
    ! [B_226,A_227,A_228] :
      ( k5_relat_1(B_226,k7_relat_1(k6_relat_1(A_227),A_228)) = k8_relat_1(A_227,k8_relat_1(A_228,B_226))
      | ~ v1_relat_1(B_226) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_362,c_1869])).

tff(c_36,plain,(
    ! [A_51] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_51)),A_51) = A_51
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4751,plain,(
    ! [A_227,A_228] :
      ( k8_relat_1(A_227,k8_relat_1(A_228,k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(A_227),A_228))))) = k7_relat_1(k6_relat_1(A_227),A_228)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_227),A_228))
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(A_227),A_228)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4716,c_36])).

tff(c_7615,plain,(
    ! [A_303,A_304] : k8_relat_1(A_303,k7_relat_1(k6_relat_1(A_304),k3_xboole_0(A_303,A_304))) = k7_relat_1(k6_relat_1(A_303),A_304) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_417,c_519,c_362,c_4751])).

tff(c_7710,plain,(
    ! [A_303,A_120] :
      ( k8_relat_1(A_303,k6_relat_1(k3_xboole_0(A_303,A_120))) = k7_relat_1(k6_relat_1(A_303),A_120)
      | ~ r1_tarski(k3_xboole_0(A_303,A_120),A_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_846,c_7615])).

tff(c_7752,plain,(
    ! [A_305,A_306] : k7_relat_1(k6_relat_1(A_305),k3_xboole_0(A_305,A_306)) = k7_relat_1(k6_relat_1(A_305),A_306) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_362,c_7710])).

tff(c_7846,plain,(
    ! [A_305,A_306] :
      ( k7_relat_1(k6_relat_1(A_305),A_306) = k6_relat_1(k3_xboole_0(A_305,A_306))
      | ~ r1_tarski(k3_xboole_0(A_305,A_306),A_305) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7752,c_846])).

tff(c_7967,plain,(
    ! [A_305,A_306] : k7_relat_1(k6_relat_1(A_305),A_306) = k6_relat_1(k3_xboole_0(A_305,A_306)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_7846])).

tff(c_46,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_342,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_46])).

tff(c_370,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_342])).

tff(c_8022,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7967,c_370])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:28:22 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.37/2.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.38/2.39  
% 6.38/2.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.38/2.39  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 6.38/2.39  
% 6.38/2.39  %Foreground sorts:
% 6.38/2.39  
% 6.38/2.39  
% 6.38/2.39  %Background operators:
% 6.38/2.39  
% 6.38/2.39  
% 6.38/2.39  %Foreground operators:
% 6.38/2.39  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 6.38/2.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.38/2.39  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.38/2.39  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.38/2.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.38/2.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.38/2.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.38/2.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.38/2.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.38/2.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.38/2.39  tff('#skF_2', type, '#skF_2': $i).
% 6.38/2.39  tff('#skF_1', type, '#skF_1': $i).
% 6.38/2.39  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.38/2.39  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.38/2.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.38/2.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.38/2.39  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.38/2.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.38/2.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.38/2.39  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.38/2.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.38/2.39  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.38/2.39  
% 6.45/2.41  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 6.45/2.41  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.45/2.41  tff(f_43, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 6.45/2.41  tff(f_51, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 6.45/2.41  tff(f_102, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 6.45/2.41  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 6.45/2.41  tff(f_80, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 6.45/2.41  tff(f_90, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 6.45/2.41  tff(f_49, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 6.45/2.41  tff(f_98, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 6.45/2.41  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k8_relat_1(A, k5_relat_1(B, C)) = k5_relat_1(B, k8_relat_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_relat_1)).
% 6.45/2.41  tff(f_84, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 6.45/2.41  tff(f_105, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 6.45/2.41  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.45/2.41  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.45/2.41  tff(c_109, plain, (![A_68, B_69]: (k1_setfam_1(k2_tarski(A_68, B_69))=k3_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.45/2.41  tff(c_124, plain, (![B_70, A_71]: (k1_setfam_1(k2_tarski(B_70, A_71))=k3_xboole_0(A_71, B_70))), inference(superposition, [status(thm), theory('equality')], [c_4, c_109])).
% 6.45/2.41  tff(c_18, plain, (![A_32, B_33]: (k1_setfam_1(k2_tarski(A_32, B_33))=k3_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.45/2.41  tff(c_147, plain, (![B_72, A_73]: (k3_xboole_0(B_72, A_73)=k3_xboole_0(A_73, B_72))), inference(superposition, [status(thm), theory('equality')], [c_124, c_18])).
% 6.45/2.41  tff(c_162, plain, (![B_72, A_73]: (r1_tarski(k3_xboole_0(B_72, A_73), A_73))), inference(superposition, [status(thm), theory('equality')], [c_147, c_2])).
% 6.45/2.41  tff(c_22, plain, (![A_36]: (v1_relat_1(k6_relat_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.45/2.41  tff(c_317, plain, (![A_86, B_87]: (k5_relat_1(k6_relat_1(A_86), B_87)=k7_relat_1(B_87, A_86) | ~v1_relat_1(B_87))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.45/2.41  tff(c_26, plain, (![B_42, A_41]: (k5_relat_1(B_42, k6_relat_1(A_41))=k8_relat_1(A_41, B_42) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.45/2.41  tff(c_324, plain, (![A_41, A_86]: (k8_relat_1(A_41, k6_relat_1(A_86))=k7_relat_1(k6_relat_1(A_41), A_86) | ~v1_relat_1(k6_relat_1(A_86)) | ~v1_relat_1(k6_relat_1(A_41)))), inference(superposition, [status(thm), theory('equality')], [c_317, c_26])).
% 6.45/2.41  tff(c_362, plain, (![A_41, A_86]: (k8_relat_1(A_41, k6_relat_1(A_86))=k7_relat_1(k6_relat_1(A_41), A_86))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_324])).
% 6.45/2.41  tff(c_34, plain, (![A_50]: (k2_relat_1(k6_relat_1(A_50))=A_50)), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.45/2.41  tff(c_580, plain, (![B_106, A_107]: (k5_relat_1(B_106, k6_relat_1(A_107))=B_106 | ~r1_tarski(k2_relat_1(B_106), A_107) | ~v1_relat_1(B_106))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.45/2.41  tff(c_587, plain, (![A_50, A_107]: (k5_relat_1(k6_relat_1(A_50), k6_relat_1(A_107))=k6_relat_1(A_50) | ~r1_tarski(A_50, A_107) | ~v1_relat_1(k6_relat_1(A_50)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_580])).
% 6.45/2.41  tff(c_784, plain, (![A_119, A_120]: (k5_relat_1(k6_relat_1(A_119), k6_relat_1(A_120))=k6_relat_1(A_119) | ~r1_tarski(A_119, A_120))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_587])).
% 6.45/2.41  tff(c_44, plain, (![A_57, B_58]: (k5_relat_1(k6_relat_1(A_57), B_58)=k7_relat_1(B_58, A_57) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.45/2.41  tff(c_796, plain, (![A_120, A_119]: (k7_relat_1(k6_relat_1(A_120), A_119)=k6_relat_1(A_119) | ~v1_relat_1(k6_relat_1(A_120)) | ~r1_tarski(A_119, A_120))), inference(superposition, [status(thm), theory('equality')], [c_784, c_44])).
% 6.45/2.41  tff(c_846, plain, (![A_120, A_119]: (k7_relat_1(k6_relat_1(A_120), A_119)=k6_relat_1(A_119) | ~r1_tarski(A_119, A_120))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_796])).
% 6.45/2.41  tff(c_397, plain, (![A_91, A_92]: (k8_relat_1(A_91, k6_relat_1(A_92))=k7_relat_1(k6_relat_1(A_91), A_92))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_324])).
% 6.45/2.41  tff(c_250, plain, (![B_81, A_82]: (k5_relat_1(B_81, k6_relat_1(A_82))=k8_relat_1(A_82, B_81) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.45/2.41  tff(c_20, plain, (![A_34, B_35]: (v1_relat_1(k5_relat_1(A_34, B_35)) | ~v1_relat_1(B_35) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.45/2.41  tff(c_264, plain, (![A_82, B_81]: (v1_relat_1(k8_relat_1(A_82, B_81)) | ~v1_relat_1(k6_relat_1(A_82)) | ~v1_relat_1(B_81) | ~v1_relat_1(B_81))), inference(superposition, [status(thm), theory('equality')], [c_250, c_20])).
% 6.45/2.41  tff(c_289, plain, (![A_82, B_81]: (v1_relat_1(k8_relat_1(A_82, B_81)) | ~v1_relat_1(B_81))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_264])).
% 6.45/2.41  tff(c_407, plain, (![A_91, A_92]: (v1_relat_1(k7_relat_1(k6_relat_1(A_91), A_92)) | ~v1_relat_1(k6_relat_1(A_92)))), inference(superposition, [status(thm), theory('equality')], [c_397, c_289])).
% 6.45/2.41  tff(c_417, plain, (![A_91, A_92]: (v1_relat_1(k7_relat_1(k6_relat_1(A_91), A_92)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_407])).
% 6.45/2.41  tff(c_32, plain, (![A_50]: (k1_relat_1(k6_relat_1(A_50))=A_50)), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.45/2.41  tff(c_486, plain, (![B_100, A_101]: (k3_xboole_0(k1_relat_1(B_100), A_101)=k1_relat_1(k7_relat_1(B_100, A_101)) | ~v1_relat_1(B_100))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.45/2.41  tff(c_515, plain, (![A_50, A_101]: (k1_relat_1(k7_relat_1(k6_relat_1(A_50), A_101))=k3_xboole_0(A_50, A_101) | ~v1_relat_1(k6_relat_1(A_50)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_486])).
% 6.45/2.41  tff(c_519, plain, (![A_50, A_101]: (k1_relat_1(k7_relat_1(k6_relat_1(A_50), A_101))=k3_xboole_0(A_50, A_101))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_515])).
% 6.45/2.41  tff(c_1840, plain, (![A_152, B_153, C_154]: (k8_relat_1(A_152, k5_relat_1(B_153, C_154))=k5_relat_1(B_153, k8_relat_1(A_152, C_154)) | ~v1_relat_1(C_154) | ~v1_relat_1(B_153))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.45/2.41  tff(c_1869, plain, (![B_42, A_152, A_41]: (k5_relat_1(B_42, k8_relat_1(A_152, k6_relat_1(A_41)))=k8_relat_1(A_152, k8_relat_1(A_41, B_42)) | ~v1_relat_1(k6_relat_1(A_41)) | ~v1_relat_1(B_42) | ~v1_relat_1(B_42))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1840])).
% 6.45/2.41  tff(c_4716, plain, (![B_226, A_227, A_228]: (k5_relat_1(B_226, k7_relat_1(k6_relat_1(A_227), A_228))=k8_relat_1(A_227, k8_relat_1(A_228, B_226)) | ~v1_relat_1(B_226))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_362, c_1869])).
% 6.45/2.41  tff(c_36, plain, (![A_51]: (k5_relat_1(k6_relat_1(k1_relat_1(A_51)), A_51)=A_51 | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.45/2.41  tff(c_4751, plain, (![A_227, A_228]: (k8_relat_1(A_227, k8_relat_1(A_228, k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(A_227), A_228)))))=k7_relat_1(k6_relat_1(A_227), A_228) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_227), A_228)) | ~v1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(A_227), A_228)))))), inference(superposition, [status(thm), theory('equality')], [c_4716, c_36])).
% 6.45/2.41  tff(c_7615, plain, (![A_303, A_304]: (k8_relat_1(A_303, k7_relat_1(k6_relat_1(A_304), k3_xboole_0(A_303, A_304)))=k7_relat_1(k6_relat_1(A_303), A_304))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_417, c_519, c_362, c_4751])).
% 6.45/2.41  tff(c_7710, plain, (![A_303, A_120]: (k8_relat_1(A_303, k6_relat_1(k3_xboole_0(A_303, A_120)))=k7_relat_1(k6_relat_1(A_303), A_120) | ~r1_tarski(k3_xboole_0(A_303, A_120), A_120))), inference(superposition, [status(thm), theory('equality')], [c_846, c_7615])).
% 6.45/2.41  tff(c_7752, plain, (![A_305, A_306]: (k7_relat_1(k6_relat_1(A_305), k3_xboole_0(A_305, A_306))=k7_relat_1(k6_relat_1(A_305), A_306))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_362, c_7710])).
% 6.45/2.41  tff(c_7846, plain, (![A_305, A_306]: (k7_relat_1(k6_relat_1(A_305), A_306)=k6_relat_1(k3_xboole_0(A_305, A_306)) | ~r1_tarski(k3_xboole_0(A_305, A_306), A_305))), inference(superposition, [status(thm), theory('equality')], [c_7752, c_846])).
% 6.45/2.41  tff(c_7967, plain, (![A_305, A_306]: (k7_relat_1(k6_relat_1(A_305), A_306)=k6_relat_1(k3_xboole_0(A_305, A_306)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_7846])).
% 6.45/2.41  tff(c_46, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.45/2.41  tff(c_342, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_317, c_46])).
% 6.45/2.41  tff(c_370, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_342])).
% 6.45/2.41  tff(c_8022, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7967, c_370])).
% 6.45/2.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.45/2.41  
% 6.45/2.41  Inference rules
% 6.45/2.41  ----------------------
% 6.45/2.41  #Ref     : 0
% 6.45/2.41  #Sup     : 1912
% 6.45/2.41  #Fact    : 0
% 6.45/2.41  #Define  : 0
% 6.45/2.41  #Split   : 1
% 6.45/2.41  #Chain   : 0
% 6.45/2.41  #Close   : 0
% 6.45/2.41  
% 6.45/2.41  Ordering : KBO
% 6.45/2.41  
% 6.45/2.41  Simplification rules
% 6.45/2.41  ----------------------
% 6.45/2.41  #Subsume      : 248
% 6.45/2.41  #Demod        : 2545
% 6.45/2.41  #Tautology    : 960
% 6.45/2.41  #SimpNegUnit  : 0
% 6.45/2.41  #BackRed      : 26
% 6.45/2.41  
% 6.45/2.41  #Partial instantiations: 0
% 6.45/2.41  #Strategies tried      : 1
% 6.45/2.41  
% 6.45/2.41  Timing (in seconds)
% 6.45/2.41  ----------------------
% 6.49/2.41  Preprocessing        : 0.33
% 6.49/2.41  Parsing              : 0.18
% 6.49/2.41  CNF conversion       : 0.02
% 6.49/2.41  Main loop            : 1.32
% 6.49/2.41  Inferencing          : 0.38
% 6.49/2.41  Reduction            : 0.62
% 6.49/2.41  Demodulation         : 0.52
% 6.49/2.41  BG Simplification    : 0.05
% 6.49/2.41  Subsumption          : 0.20
% 6.49/2.41  Abstraction          : 0.07
% 6.49/2.41  MUC search           : 0.00
% 6.49/2.41  Cooper               : 0.00
% 6.49/2.41  Total                : 1.68
% 6.49/2.41  Index Insertion      : 0.00
% 6.49/2.41  Index Deletion       : 0.00
% 6.49/2.41  Index Matching       : 0.00
% 6.49/2.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
