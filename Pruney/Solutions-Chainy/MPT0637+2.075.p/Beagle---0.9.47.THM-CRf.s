%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:34 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 131 expanded)
%              Number of leaves         :   30 (  59 expanded)
%              Depth                    :   12
%              Number of atoms          :   86 ( 186 expanded)
%              Number of equality atoms :   47 (  85 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_95,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_71,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_73,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_34,plain,(
    ! [A_38] : v1_relat_1(k6_relat_1(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_22,plain,(
    ! [A_29] : k2_relat_1(k6_relat_1(A_29)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_130,plain,(
    ! [A_57,B_58] :
      ( k5_relat_1(k6_relat_1(A_57),B_58) = k7_relat_1(B_58,A_57)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_26,plain,(
    ! [A_31] :
      ( k5_relat_1(A_31,k6_relat_1(k2_relat_1(A_31))) = A_31
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_141,plain,(
    ! [A_57] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_57))),A_57) = k6_relat_1(A_57)
      | ~ v1_relat_1(k6_relat_1(A_57))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_57)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_26])).

tff(c_162,plain,(
    ! [A_57] : k7_relat_1(k6_relat_1(A_57),A_57) = k6_relat_1(A_57) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_22,c_141])).

tff(c_469,plain,(
    ! [C_80,A_81,B_82] :
      ( k7_relat_1(k7_relat_1(C_80,A_81),B_82) = k7_relat_1(C_80,k3_xboole_0(A_81,B_82))
      | ~ v1_relat_1(C_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_508,plain,(
    ! [A_57,B_82] :
      ( k7_relat_1(k6_relat_1(A_57),k3_xboole_0(A_57,B_82)) = k7_relat_1(k6_relat_1(A_57),B_82)
      | ~ v1_relat_1(k6_relat_1(A_57)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_469])).

tff(c_514,plain,(
    ! [A_57,B_82] : k7_relat_1(k6_relat_1(A_57),k3_xboole_0(A_57,B_82)) = k7_relat_1(k6_relat_1(A_57),B_82) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_508])).

tff(c_24,plain,(
    ! [A_30] : k4_relat_1(k6_relat_1(A_30)) = k6_relat_1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_29] : k1_relat_1(k6_relat_1(A_29)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_263,plain,(
    ! [B_70,A_71] :
      ( k7_relat_1(B_70,A_71) = B_70
      | ~ r1_tarski(k1_relat_1(B_70),A_71)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_276,plain,(
    ! [A_29,A_71] :
      ( k7_relat_1(k6_relat_1(A_29),A_71) = k6_relat_1(A_29)
      | ~ r1_tarski(A_29,A_71)
      | ~ v1_relat_1(k6_relat_1(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_263])).

tff(c_311,plain,(
    ! [A_73,A_74] :
      ( k7_relat_1(k6_relat_1(A_73),A_74) = k6_relat_1(A_73)
      | ~ r1_tarski(A_73,A_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_276])).

tff(c_181,plain,(
    ! [B_60,A_61] :
      ( k3_xboole_0(k1_relat_1(B_60),A_61) = k1_relat_1(k7_relat_1(B_60,A_61))
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_193,plain,(
    ! [A_29,A_61] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_29),A_61)) = k3_xboole_0(A_29,A_61)
      | ~ v1_relat_1(k6_relat_1(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_181])).

tff(c_197,plain,(
    ! [A_29,A_61] : k1_relat_1(k7_relat_1(k6_relat_1(A_29),A_61)) = k3_xboole_0(A_29,A_61) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_193])).

tff(c_324,plain,(
    ! [A_73,A_74] :
      ( k3_xboole_0(A_73,A_74) = k1_relat_1(k6_relat_1(A_73))
      | ~ r1_tarski(A_73,A_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_197])).

tff(c_364,plain,(
    ! [A_75,A_76] :
      ( k3_xboole_0(A_75,A_76) = A_75
      | ~ r1_tarski(A_75,A_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_324])).

tff(c_377,plain,(
    ! [A_1,B_2] : k3_xboole_0(k3_xboole_0(A_1,B_2),A_1) = k3_xboole_0(A_1,B_2) ),
    inference(resolution,[status(thm)],[c_2,c_364])).

tff(c_537,plain,(
    ! [A_85,B_86] : k7_relat_1(k6_relat_1(A_85),k3_xboole_0(A_85,B_86)) = k7_relat_1(k6_relat_1(A_85),B_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_508])).

tff(c_561,plain,(
    ! [A_1,B_2] : k7_relat_1(k6_relat_1(k3_xboole_0(A_1,B_2)),k3_xboole_0(A_1,B_2)) = k7_relat_1(k6_relat_1(k3_xboole_0(A_1,B_2)),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_537])).

tff(c_581,plain,(
    ! [A_1,B_2] : k7_relat_1(k6_relat_1(k3_xboole_0(A_1,B_2)),A_1) = k6_relat_1(k3_xboole_0(A_1,B_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_561])).

tff(c_30,plain,(
    ! [A_34,B_35] :
      ( k5_relat_1(k6_relat_1(A_34),B_35) = k7_relat_1(B_35,A_34)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_515,plain,(
    ! [B_83,A_84] :
      ( k5_relat_1(k4_relat_1(B_83),k4_relat_1(A_84)) = k4_relat_1(k5_relat_1(A_84,B_83))
      | ~ v1_relat_1(B_83)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_527,plain,(
    ! [A_30,A_84] :
      ( k5_relat_1(k6_relat_1(A_30),k4_relat_1(A_84)) = k4_relat_1(k5_relat_1(A_84,k6_relat_1(A_30)))
      | ~ v1_relat_1(k6_relat_1(A_30))
      | ~ v1_relat_1(A_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_515])).

tff(c_813,plain,(
    ! [A_100,A_101] :
      ( k5_relat_1(k6_relat_1(A_100),k4_relat_1(A_101)) = k4_relat_1(k5_relat_1(A_101,k6_relat_1(A_100)))
      | ~ v1_relat_1(A_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_527])).

tff(c_835,plain,(
    ! [A_30,A_100] :
      ( k4_relat_1(k5_relat_1(k6_relat_1(A_30),k6_relat_1(A_100))) = k5_relat_1(k6_relat_1(A_100),k6_relat_1(A_30))
      | ~ v1_relat_1(k6_relat_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_813])).

tff(c_950,plain,(
    ! [A_109,A_110] : k4_relat_1(k5_relat_1(k6_relat_1(A_109),k6_relat_1(A_110))) = k5_relat_1(k6_relat_1(A_110),k6_relat_1(A_109)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_835])).

tff(c_972,plain,(
    ! [A_110,A_34] :
      ( k5_relat_1(k6_relat_1(A_110),k6_relat_1(A_34)) = k4_relat_1(k7_relat_1(k6_relat_1(A_110),A_34))
      | ~ v1_relat_1(k6_relat_1(A_110)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_950])).

tff(c_1100,plain,(
    ! [A_115,A_116] : k5_relat_1(k6_relat_1(A_115),k6_relat_1(A_116)) = k4_relat_1(k7_relat_1(k6_relat_1(A_115),A_116)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_972])).

tff(c_1115,plain,(
    ! [A_115,A_116] :
      ( k4_relat_1(k7_relat_1(k6_relat_1(A_115),A_116)) = k7_relat_1(k6_relat_1(A_116),A_115)
      | ~ v1_relat_1(k6_relat_1(A_116)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1100,c_30])).

tff(c_1190,plain,(
    ! [A_119,A_120] : k4_relat_1(k7_relat_1(k6_relat_1(A_119),A_120)) = k7_relat_1(k6_relat_1(A_120),A_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1115])).

tff(c_1208,plain,(
    ! [A_1,B_2] : k7_relat_1(k6_relat_1(A_1),k3_xboole_0(A_1,B_2)) = k4_relat_1(k6_relat_1(k3_xboole_0(A_1,B_2))) ),
    inference(superposition,[status(thm),theory(equality)],[c_581,c_1190])).

tff(c_1230,plain,(
    ! [A_1,B_2] : k7_relat_1(k6_relat_1(A_1),B_2) = k6_relat_1(k3_xboole_0(A_1,B_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_24,c_1208])).

tff(c_38,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_144,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_38])).

tff(c_164,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_144])).

tff(c_1308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1230,c_164])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:46:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.51  
% 3.14/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.51  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.14/1.51  
% 3.14/1.51  %Foreground sorts:
% 3.14/1.51  
% 3.14/1.51  
% 3.14/1.51  %Background operators:
% 3.14/1.51  
% 3.14/1.51  
% 3.14/1.51  %Foreground operators:
% 3.14/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.14/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.51  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.14/1.51  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.14/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.14/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.14/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.14/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.14/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.14/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.14/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.14/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.14/1.51  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.14/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.14/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.14/1.51  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.14/1.51  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.14/1.51  
% 3.14/1.53  tff(f_95, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.14/1.53  tff(f_71, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.14/1.53  tff(f_85, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 3.14/1.53  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 3.14/1.53  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 3.14/1.53  tff(f_73, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_relat_1)).
% 3.14/1.53  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.14/1.53  tff(f_91, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 3.14/1.53  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 3.14/1.53  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 3.14/1.53  tff(f_98, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 3.14/1.53  tff(c_34, plain, (![A_38]: (v1_relat_1(k6_relat_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.14/1.53  tff(c_22, plain, (![A_29]: (k2_relat_1(k6_relat_1(A_29))=A_29)), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.14/1.53  tff(c_130, plain, (![A_57, B_58]: (k5_relat_1(k6_relat_1(A_57), B_58)=k7_relat_1(B_58, A_57) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.14/1.53  tff(c_26, plain, (![A_31]: (k5_relat_1(A_31, k6_relat_1(k2_relat_1(A_31)))=A_31 | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.14/1.53  tff(c_141, plain, (![A_57]: (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_57))), A_57)=k6_relat_1(A_57) | ~v1_relat_1(k6_relat_1(A_57)) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_57)))))), inference(superposition, [status(thm), theory('equality')], [c_130, c_26])).
% 3.14/1.53  tff(c_162, plain, (![A_57]: (k7_relat_1(k6_relat_1(A_57), A_57)=k6_relat_1(A_57))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_22, c_141])).
% 3.14/1.53  tff(c_469, plain, (![C_80, A_81, B_82]: (k7_relat_1(k7_relat_1(C_80, A_81), B_82)=k7_relat_1(C_80, k3_xboole_0(A_81, B_82)) | ~v1_relat_1(C_80))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.14/1.53  tff(c_508, plain, (![A_57, B_82]: (k7_relat_1(k6_relat_1(A_57), k3_xboole_0(A_57, B_82))=k7_relat_1(k6_relat_1(A_57), B_82) | ~v1_relat_1(k6_relat_1(A_57)))), inference(superposition, [status(thm), theory('equality')], [c_162, c_469])).
% 3.14/1.53  tff(c_514, plain, (![A_57, B_82]: (k7_relat_1(k6_relat_1(A_57), k3_xboole_0(A_57, B_82))=k7_relat_1(k6_relat_1(A_57), B_82))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_508])).
% 3.14/1.53  tff(c_24, plain, (![A_30]: (k4_relat_1(k6_relat_1(A_30))=k6_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.14/1.53  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.14/1.53  tff(c_20, plain, (![A_29]: (k1_relat_1(k6_relat_1(A_29))=A_29)), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.14/1.53  tff(c_263, plain, (![B_70, A_71]: (k7_relat_1(B_70, A_71)=B_70 | ~r1_tarski(k1_relat_1(B_70), A_71) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.14/1.53  tff(c_276, plain, (![A_29, A_71]: (k7_relat_1(k6_relat_1(A_29), A_71)=k6_relat_1(A_29) | ~r1_tarski(A_29, A_71) | ~v1_relat_1(k6_relat_1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_263])).
% 3.14/1.53  tff(c_311, plain, (![A_73, A_74]: (k7_relat_1(k6_relat_1(A_73), A_74)=k6_relat_1(A_73) | ~r1_tarski(A_73, A_74))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_276])).
% 3.14/1.53  tff(c_181, plain, (![B_60, A_61]: (k3_xboole_0(k1_relat_1(B_60), A_61)=k1_relat_1(k7_relat_1(B_60, A_61)) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.14/1.53  tff(c_193, plain, (![A_29, A_61]: (k1_relat_1(k7_relat_1(k6_relat_1(A_29), A_61))=k3_xboole_0(A_29, A_61) | ~v1_relat_1(k6_relat_1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_181])).
% 3.14/1.53  tff(c_197, plain, (![A_29, A_61]: (k1_relat_1(k7_relat_1(k6_relat_1(A_29), A_61))=k3_xboole_0(A_29, A_61))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_193])).
% 3.14/1.53  tff(c_324, plain, (![A_73, A_74]: (k3_xboole_0(A_73, A_74)=k1_relat_1(k6_relat_1(A_73)) | ~r1_tarski(A_73, A_74))), inference(superposition, [status(thm), theory('equality')], [c_311, c_197])).
% 3.14/1.53  tff(c_364, plain, (![A_75, A_76]: (k3_xboole_0(A_75, A_76)=A_75 | ~r1_tarski(A_75, A_76))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_324])).
% 3.14/1.53  tff(c_377, plain, (![A_1, B_2]: (k3_xboole_0(k3_xboole_0(A_1, B_2), A_1)=k3_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_2, c_364])).
% 3.14/1.53  tff(c_537, plain, (![A_85, B_86]: (k7_relat_1(k6_relat_1(A_85), k3_xboole_0(A_85, B_86))=k7_relat_1(k6_relat_1(A_85), B_86))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_508])).
% 3.14/1.53  tff(c_561, plain, (![A_1, B_2]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_1, B_2)), k3_xboole_0(A_1, B_2))=k7_relat_1(k6_relat_1(k3_xboole_0(A_1, B_2)), A_1))), inference(superposition, [status(thm), theory('equality')], [c_377, c_537])).
% 3.14/1.53  tff(c_581, plain, (![A_1, B_2]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_1, B_2)), A_1)=k6_relat_1(k3_xboole_0(A_1, B_2)))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_561])).
% 3.14/1.53  tff(c_30, plain, (![A_34, B_35]: (k5_relat_1(k6_relat_1(A_34), B_35)=k7_relat_1(B_35, A_34) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.14/1.53  tff(c_515, plain, (![B_83, A_84]: (k5_relat_1(k4_relat_1(B_83), k4_relat_1(A_84))=k4_relat_1(k5_relat_1(A_84, B_83)) | ~v1_relat_1(B_83) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.14/1.53  tff(c_527, plain, (![A_30, A_84]: (k5_relat_1(k6_relat_1(A_30), k4_relat_1(A_84))=k4_relat_1(k5_relat_1(A_84, k6_relat_1(A_30))) | ~v1_relat_1(k6_relat_1(A_30)) | ~v1_relat_1(A_84))), inference(superposition, [status(thm), theory('equality')], [c_24, c_515])).
% 3.14/1.53  tff(c_813, plain, (![A_100, A_101]: (k5_relat_1(k6_relat_1(A_100), k4_relat_1(A_101))=k4_relat_1(k5_relat_1(A_101, k6_relat_1(A_100))) | ~v1_relat_1(A_101))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_527])).
% 3.14/1.53  tff(c_835, plain, (![A_30, A_100]: (k4_relat_1(k5_relat_1(k6_relat_1(A_30), k6_relat_1(A_100)))=k5_relat_1(k6_relat_1(A_100), k6_relat_1(A_30)) | ~v1_relat_1(k6_relat_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_813])).
% 3.14/1.53  tff(c_950, plain, (![A_109, A_110]: (k4_relat_1(k5_relat_1(k6_relat_1(A_109), k6_relat_1(A_110)))=k5_relat_1(k6_relat_1(A_110), k6_relat_1(A_109)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_835])).
% 3.14/1.53  tff(c_972, plain, (![A_110, A_34]: (k5_relat_1(k6_relat_1(A_110), k6_relat_1(A_34))=k4_relat_1(k7_relat_1(k6_relat_1(A_110), A_34)) | ~v1_relat_1(k6_relat_1(A_110)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_950])).
% 3.14/1.53  tff(c_1100, plain, (![A_115, A_116]: (k5_relat_1(k6_relat_1(A_115), k6_relat_1(A_116))=k4_relat_1(k7_relat_1(k6_relat_1(A_115), A_116)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_972])).
% 3.14/1.53  tff(c_1115, plain, (![A_115, A_116]: (k4_relat_1(k7_relat_1(k6_relat_1(A_115), A_116))=k7_relat_1(k6_relat_1(A_116), A_115) | ~v1_relat_1(k6_relat_1(A_116)))), inference(superposition, [status(thm), theory('equality')], [c_1100, c_30])).
% 3.14/1.53  tff(c_1190, plain, (![A_119, A_120]: (k4_relat_1(k7_relat_1(k6_relat_1(A_119), A_120))=k7_relat_1(k6_relat_1(A_120), A_119))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1115])).
% 3.14/1.53  tff(c_1208, plain, (![A_1, B_2]: (k7_relat_1(k6_relat_1(A_1), k3_xboole_0(A_1, B_2))=k4_relat_1(k6_relat_1(k3_xboole_0(A_1, B_2))))), inference(superposition, [status(thm), theory('equality')], [c_581, c_1190])).
% 3.14/1.53  tff(c_1230, plain, (![A_1, B_2]: (k7_relat_1(k6_relat_1(A_1), B_2)=k6_relat_1(k3_xboole_0(A_1, B_2)))), inference(demodulation, [status(thm), theory('equality')], [c_514, c_24, c_1208])).
% 3.14/1.53  tff(c_38, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.14/1.53  tff(c_144, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_130, c_38])).
% 3.14/1.53  tff(c_164, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_144])).
% 3.14/1.53  tff(c_1308, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1230, c_164])).
% 3.14/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.53  
% 3.14/1.53  Inference rules
% 3.14/1.53  ----------------------
% 3.14/1.53  #Ref     : 0
% 3.14/1.53  #Sup     : 282
% 3.14/1.53  #Fact    : 0
% 3.14/1.53  #Define  : 0
% 3.14/1.53  #Split   : 1
% 3.14/1.53  #Chain   : 0
% 3.14/1.53  #Close   : 0
% 3.14/1.53  
% 3.14/1.53  Ordering : KBO
% 3.14/1.53  
% 3.14/1.53  Simplification rules
% 3.14/1.53  ----------------------
% 3.14/1.53  #Subsume      : 11
% 3.14/1.53  #Demod        : 340
% 3.14/1.53  #Tautology    : 164
% 3.14/1.53  #SimpNegUnit  : 0
% 3.14/1.53  #BackRed      : 15
% 3.14/1.53  
% 3.14/1.53  #Partial instantiations: 0
% 3.14/1.53  #Strategies tried      : 1
% 3.14/1.53  
% 3.14/1.53  Timing (in seconds)
% 3.14/1.53  ----------------------
% 3.14/1.53  Preprocessing        : 0.32
% 3.14/1.53  Parsing              : 0.17
% 3.14/1.53  CNF conversion       : 0.02
% 3.14/1.53  Main loop            : 0.40
% 3.14/1.53  Inferencing          : 0.15
% 3.14/1.53  Reduction            : 0.14
% 3.14/1.53  Demodulation         : 0.10
% 3.14/1.53  BG Simplification    : 0.03
% 3.14/1.53  Subsumption          : 0.06
% 3.14/1.53  Abstraction          : 0.03
% 3.14/1.53  MUC search           : 0.00
% 3.14/1.53  Cooper               : 0.00
% 3.14/1.53  Total                : 0.75
% 3.14/1.53  Index Insertion      : 0.00
% 3.14/1.53  Index Deletion       : 0.00
% 3.14/1.53  Index Matching       : 0.00
% 3.14/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
