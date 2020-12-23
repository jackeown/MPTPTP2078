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
% DateTime   : Thu Dec  3 09:57:22 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 203 expanded)
%              Number of leaves         :   37 (  82 expanded)
%              Depth                    :   18
%              Number of atoms          :   93 ( 263 expanded)
%              Number of equality atoms :   65 ( 150 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_68,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_70,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_39,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_77,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_91,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_72,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_89,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_94,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_50,plain,(
    ! [A_30] : k2_tarski(A_30,A_30) = k1_tarski(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_116,plain,(
    ! [A_67,B_68] : k1_enumset1(A_67,A_67,B_68) = k2_tarski(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_24,plain,(
    ! [E_20,A_14,B_15] : r2_hidden(E_20,k1_enumset1(A_14,B_15,E_20)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_146,plain,(
    ! [B_71,A_72] : r2_hidden(B_71,k2_tarski(A_72,B_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_24])).

tff(c_149,plain,(
    ! [A_30] : r2_hidden(A_30,k1_tarski(A_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_146])).

tff(c_12,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_92,plain,(
    ! [A_47,B_48] : r1_tarski(k3_xboole_0(A_47,B_48),A_47) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_95,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_92])).

tff(c_202,plain,(
    ! [B_81,A_82] :
      ( B_81 = A_82
      | ~ r1_tarski(B_81,A_82)
      | ~ r1_tarski(A_82,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_215,plain,(
    ! [A_83] :
      ( k1_xboole_0 = A_83
      | ~ r1_tarski(A_83,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_95,c_202])).

tff(c_230,plain,(
    ! [B_6] : k3_xboole_0(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_215])).

tff(c_250,plain,(
    ! [B_86] : k3_xboole_0(k1_xboole_0,B_86) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_215])).

tff(c_14,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_272,plain,(
    ! [B_87] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_14])).

tff(c_16,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_286,plain,(
    ! [B_11] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,B_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_16])).

tff(c_302,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_286])).

tff(c_255,plain,(
    ! [B_86] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_14])).

tff(c_305,plain,(
    ! [B_86] : k4_xboole_0(k1_xboole_0,B_86) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_255])).

tff(c_102,plain,(
    ! [A_63,B_64] :
      ( r1_xboole_0(A_63,B_64)
      | k4_xboole_0(A_63,B_64) != A_63 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_189,plain,(
    ! [B_79,A_80] :
      ( r1_xboole_0(B_79,A_80)
      | k4_xboole_0(A_80,B_79) != A_80 ) ),
    inference(resolution,[status(thm)],[c_102,c_2])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(A_12,B_13) = A_12
      | ~ r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_442,plain,(
    ! [B_105,A_106] :
      ( k4_xboole_0(B_105,A_106) = B_105
      | k4_xboole_0(A_106,B_105) != A_106 ) ),
    inference(resolution,[status(thm)],[c_189,c_18])).

tff(c_450,plain,(
    ! [B_107] : k4_xboole_0(B_107,k1_xboole_0) = B_107 ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_442])).

tff(c_462,plain,(
    ! [B_107] : k4_xboole_0(B_107,B_107) = k3_xboole_0(B_107,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_450,c_16])).

tff(c_477,plain,(
    ! [B_108] : k4_xboole_0(B_108,B_108) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_462])).

tff(c_56,plain,(
    ! [A_36,B_37] :
      ( ~ r2_hidden(A_36,B_37)
      | ~ r1_xboole_0(k1_tarski(A_36),B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_199,plain,(
    ! [A_36,A_80] :
      ( ~ r2_hidden(A_36,A_80)
      | k4_xboole_0(A_80,k1_tarski(A_36)) != A_80 ) ),
    inference(resolution,[status(thm)],[c_189,c_56])).

tff(c_489,plain,(
    ! [A_36] :
      ( ~ r2_hidden(A_36,k1_tarski(A_36))
      | k1_tarski(A_36) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_477,c_199])).

tff(c_509,plain,(
    ! [A_36] : k1_tarski(A_36) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_489])).

tff(c_62,plain,(
    ! [A_42] : k1_setfam_1(k1_tarski(A_42)) = A_42 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_52,plain,(
    ! [A_31,B_32] : k1_enumset1(A_31,A_31,B_32) = k2_tarski(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_54,plain,(
    ! [A_33,B_34,C_35] : k2_enumset1(A_33,A_33,B_34,C_35) = k1_enumset1(A_33,B_34,C_35) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_428,plain,(
    ! [A_100,B_101,C_102,D_103] : k2_xboole_0(k1_enumset1(A_100,B_101,C_102),k1_tarski(D_103)) = k2_enumset1(A_100,B_101,C_102,D_103) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_437,plain,(
    ! [A_31,B_32,D_103] : k2_xboole_0(k2_tarski(A_31,B_32),k1_tarski(D_103)) = k2_enumset1(A_31,A_31,B_32,D_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_428])).

tff(c_768,plain,(
    ! [A_132,B_133,D_134] : k2_xboole_0(k2_tarski(A_132,B_133),k1_tarski(D_134)) = k1_enumset1(A_132,B_133,D_134) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_437])).

tff(c_777,plain,(
    ! [A_30,D_134] : k2_xboole_0(k1_tarski(A_30),k1_tarski(D_134)) = k1_enumset1(A_30,A_30,D_134) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_768])).

tff(c_780,plain,(
    ! [A_30,D_134] : k2_xboole_0(k1_tarski(A_30),k1_tarski(D_134)) = k2_tarski(A_30,D_134) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_777])).

tff(c_516,plain,(
    ! [A_110,B_111] :
      ( k3_xboole_0(k1_setfam_1(A_110),k1_setfam_1(B_111)) = k1_setfam_1(k2_xboole_0(A_110,B_111))
      | k1_xboole_0 = B_111
      | k1_xboole_0 = A_110 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_537,plain,(
    ! [A_110,A_42] :
      ( k1_setfam_1(k2_xboole_0(A_110,k1_tarski(A_42))) = k3_xboole_0(k1_setfam_1(A_110),A_42)
      | k1_tarski(A_42) = k1_xboole_0
      | k1_xboole_0 = A_110 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_516])).

tff(c_858,plain,(
    ! [A_144,A_145] :
      ( k1_setfam_1(k2_xboole_0(A_144,k1_tarski(A_145))) = k3_xboole_0(k1_setfam_1(A_144),A_145)
      | k1_xboole_0 = A_144 ) ),
    inference(negUnitSimplification,[status(thm)],[c_509,c_537])).

tff(c_881,plain,(
    ! [A_30,D_134] :
      ( k3_xboole_0(k1_setfam_1(k1_tarski(A_30)),D_134) = k1_setfam_1(k2_tarski(A_30,D_134))
      | k1_tarski(A_30) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_780,c_858])).

tff(c_901,plain,(
    ! [A_30,D_134] :
      ( k1_setfam_1(k2_tarski(A_30,D_134)) = k3_xboole_0(A_30,D_134)
      | k1_tarski(A_30) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_881])).

tff(c_902,plain,(
    ! [A_30,D_134] : k1_setfam_1(k2_tarski(A_30,D_134)) = k3_xboole_0(A_30,D_134) ),
    inference(negUnitSimplification,[status(thm)],[c_509,c_901])).

tff(c_64,plain,(
    k1_setfam_1(k2_tarski('#skF_3','#skF_4')) != k3_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_908,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_902,c_64])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:17:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.56/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.44  
% 2.56/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.44  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.56/1.44  
% 2.56/1.44  %Foreground sorts:
% 2.56/1.44  
% 2.56/1.44  
% 2.56/1.44  %Background operators:
% 2.56/1.44  
% 2.56/1.44  
% 2.56/1.44  %Foreground operators:
% 2.56/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.56/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.56/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.56/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.56/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.56/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.56/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.56/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.56/1.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.56/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.56/1.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.56/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.56/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.44  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.56/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.56/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.56/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.56/1.44  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.56/1.44  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.56/1.44  
% 2.96/1.45  tff(f_68, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.96/1.45  tff(f_70, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.96/1.45  tff(f_62, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.96/1.45  tff(f_39, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.96/1.45  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.96/1.45  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.96/1.45  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.96/1.45  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.96/1.45  tff(f_47, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.96/1.45  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.96/1.45  tff(f_77, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.96/1.45  tff(f_91, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.96/1.45  tff(f_72, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.96/1.45  tff(f_64, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 2.96/1.45  tff(f_89, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_setfam_1)).
% 2.96/1.45  tff(f_94, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.96/1.45  tff(c_50, plain, (![A_30]: (k2_tarski(A_30, A_30)=k1_tarski(A_30))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.96/1.45  tff(c_116, plain, (![A_67, B_68]: (k1_enumset1(A_67, A_67, B_68)=k2_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.96/1.45  tff(c_24, plain, (![E_20, A_14, B_15]: (r2_hidden(E_20, k1_enumset1(A_14, B_15, E_20)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.96/1.45  tff(c_146, plain, (![B_71, A_72]: (r2_hidden(B_71, k2_tarski(A_72, B_71)))), inference(superposition, [status(thm), theory('equality')], [c_116, c_24])).
% 2.96/1.45  tff(c_149, plain, (![A_30]: (r2_hidden(A_30, k1_tarski(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_146])).
% 2.96/1.45  tff(c_12, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.96/1.45  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.96/1.45  tff(c_92, plain, (![A_47, B_48]: (r1_tarski(k3_xboole_0(A_47, B_48), A_47))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.96/1.45  tff(c_95, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(superposition, [status(thm), theory('equality')], [c_12, c_92])).
% 2.96/1.45  tff(c_202, plain, (![B_81, A_82]: (B_81=A_82 | ~r1_tarski(B_81, A_82) | ~r1_tarski(A_82, B_81))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.96/1.45  tff(c_215, plain, (![A_83]: (k1_xboole_0=A_83 | ~r1_tarski(A_83, k1_xboole_0))), inference(resolution, [status(thm)], [c_95, c_202])).
% 2.96/1.45  tff(c_230, plain, (![B_6]: (k3_xboole_0(k1_xboole_0, B_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_215])).
% 2.96/1.45  tff(c_250, plain, (![B_86]: (k3_xboole_0(k1_xboole_0, B_86)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_215])).
% 2.96/1.45  tff(c_14, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.96/1.45  tff(c_272, plain, (![B_87]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_87))), inference(superposition, [status(thm), theory('equality')], [c_250, c_14])).
% 2.96/1.45  tff(c_16, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.96/1.45  tff(c_286, plain, (![B_11]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k3_xboole_0(k1_xboole_0, B_11))), inference(superposition, [status(thm), theory('equality')], [c_272, c_16])).
% 2.96/1.45  tff(c_302, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_230, c_286])).
% 2.96/1.45  tff(c_255, plain, (![B_86]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_86))), inference(superposition, [status(thm), theory('equality')], [c_250, c_14])).
% 2.96/1.45  tff(c_305, plain, (![B_86]: (k4_xboole_0(k1_xboole_0, B_86)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_302, c_255])).
% 2.96/1.45  tff(c_102, plain, (![A_63, B_64]: (r1_xboole_0(A_63, B_64) | k4_xboole_0(A_63, B_64)!=A_63)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.96/1.45  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.96/1.45  tff(c_189, plain, (![B_79, A_80]: (r1_xboole_0(B_79, A_80) | k4_xboole_0(A_80, B_79)!=A_80)), inference(resolution, [status(thm)], [c_102, c_2])).
% 2.96/1.45  tff(c_18, plain, (![A_12, B_13]: (k4_xboole_0(A_12, B_13)=A_12 | ~r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.96/1.45  tff(c_442, plain, (![B_105, A_106]: (k4_xboole_0(B_105, A_106)=B_105 | k4_xboole_0(A_106, B_105)!=A_106)), inference(resolution, [status(thm)], [c_189, c_18])).
% 2.96/1.45  tff(c_450, plain, (![B_107]: (k4_xboole_0(B_107, k1_xboole_0)=B_107)), inference(superposition, [status(thm), theory('equality')], [c_305, c_442])).
% 2.96/1.45  tff(c_462, plain, (![B_107]: (k4_xboole_0(B_107, B_107)=k3_xboole_0(B_107, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_450, c_16])).
% 2.96/1.45  tff(c_477, plain, (![B_108]: (k4_xboole_0(B_108, B_108)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_462])).
% 2.96/1.45  tff(c_56, plain, (![A_36, B_37]: (~r2_hidden(A_36, B_37) | ~r1_xboole_0(k1_tarski(A_36), B_37))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.96/1.45  tff(c_199, plain, (![A_36, A_80]: (~r2_hidden(A_36, A_80) | k4_xboole_0(A_80, k1_tarski(A_36))!=A_80)), inference(resolution, [status(thm)], [c_189, c_56])).
% 2.96/1.45  tff(c_489, plain, (![A_36]: (~r2_hidden(A_36, k1_tarski(A_36)) | k1_tarski(A_36)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_477, c_199])).
% 2.96/1.45  tff(c_509, plain, (![A_36]: (k1_tarski(A_36)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_149, c_489])).
% 2.96/1.45  tff(c_62, plain, (![A_42]: (k1_setfam_1(k1_tarski(A_42))=A_42)), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.96/1.45  tff(c_52, plain, (![A_31, B_32]: (k1_enumset1(A_31, A_31, B_32)=k2_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.96/1.45  tff(c_54, plain, (![A_33, B_34, C_35]: (k2_enumset1(A_33, A_33, B_34, C_35)=k1_enumset1(A_33, B_34, C_35))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.96/1.45  tff(c_428, plain, (![A_100, B_101, C_102, D_103]: (k2_xboole_0(k1_enumset1(A_100, B_101, C_102), k1_tarski(D_103))=k2_enumset1(A_100, B_101, C_102, D_103))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.96/1.45  tff(c_437, plain, (![A_31, B_32, D_103]: (k2_xboole_0(k2_tarski(A_31, B_32), k1_tarski(D_103))=k2_enumset1(A_31, A_31, B_32, D_103))), inference(superposition, [status(thm), theory('equality')], [c_52, c_428])).
% 2.96/1.45  tff(c_768, plain, (![A_132, B_133, D_134]: (k2_xboole_0(k2_tarski(A_132, B_133), k1_tarski(D_134))=k1_enumset1(A_132, B_133, D_134))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_437])).
% 2.96/1.45  tff(c_777, plain, (![A_30, D_134]: (k2_xboole_0(k1_tarski(A_30), k1_tarski(D_134))=k1_enumset1(A_30, A_30, D_134))), inference(superposition, [status(thm), theory('equality')], [c_50, c_768])).
% 2.96/1.45  tff(c_780, plain, (![A_30, D_134]: (k2_xboole_0(k1_tarski(A_30), k1_tarski(D_134))=k2_tarski(A_30, D_134))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_777])).
% 2.96/1.45  tff(c_516, plain, (![A_110, B_111]: (k3_xboole_0(k1_setfam_1(A_110), k1_setfam_1(B_111))=k1_setfam_1(k2_xboole_0(A_110, B_111)) | k1_xboole_0=B_111 | k1_xboole_0=A_110)), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.96/1.45  tff(c_537, plain, (![A_110, A_42]: (k1_setfam_1(k2_xboole_0(A_110, k1_tarski(A_42)))=k3_xboole_0(k1_setfam_1(A_110), A_42) | k1_tarski(A_42)=k1_xboole_0 | k1_xboole_0=A_110)), inference(superposition, [status(thm), theory('equality')], [c_62, c_516])).
% 2.96/1.45  tff(c_858, plain, (![A_144, A_145]: (k1_setfam_1(k2_xboole_0(A_144, k1_tarski(A_145)))=k3_xboole_0(k1_setfam_1(A_144), A_145) | k1_xboole_0=A_144)), inference(negUnitSimplification, [status(thm)], [c_509, c_537])).
% 2.96/1.45  tff(c_881, plain, (![A_30, D_134]: (k3_xboole_0(k1_setfam_1(k1_tarski(A_30)), D_134)=k1_setfam_1(k2_tarski(A_30, D_134)) | k1_tarski(A_30)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_780, c_858])).
% 2.96/1.45  tff(c_901, plain, (![A_30, D_134]: (k1_setfam_1(k2_tarski(A_30, D_134))=k3_xboole_0(A_30, D_134) | k1_tarski(A_30)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_881])).
% 2.96/1.45  tff(c_902, plain, (![A_30, D_134]: (k1_setfam_1(k2_tarski(A_30, D_134))=k3_xboole_0(A_30, D_134))), inference(negUnitSimplification, [status(thm)], [c_509, c_901])).
% 2.96/1.45  tff(c_64, plain, (k1_setfam_1(k2_tarski('#skF_3', '#skF_4'))!=k3_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.96/1.45  tff(c_908, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_902, c_64])).
% 2.96/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.45  
% 2.96/1.45  Inference rules
% 2.96/1.45  ----------------------
% 2.96/1.45  #Ref     : 0
% 2.96/1.45  #Sup     : 194
% 2.96/1.45  #Fact    : 0
% 2.96/1.45  #Define  : 0
% 2.96/1.45  #Split   : 0
% 2.96/1.45  #Chain   : 0
% 2.96/1.45  #Close   : 0
% 2.96/1.45  
% 2.96/1.45  Ordering : KBO
% 2.96/1.45  
% 2.96/1.45  Simplification rules
% 2.96/1.45  ----------------------
% 2.96/1.45  #Subsume      : 15
% 2.96/1.45  #Demod        : 117
% 2.96/1.45  #Tautology    : 131
% 2.96/1.45  #SimpNegUnit  : 8
% 2.96/1.45  #BackRed      : 2
% 2.96/1.45  
% 2.96/1.45  #Partial instantiations: 0
% 2.96/1.45  #Strategies tried      : 1
% 2.96/1.45  
% 2.96/1.46  Timing (in seconds)
% 2.96/1.46  ----------------------
% 2.96/1.46  Preprocessing        : 0.33
% 2.96/1.46  Parsing              : 0.17
% 2.96/1.46  CNF conversion       : 0.03
% 2.96/1.46  Main loop            : 0.32
% 2.96/1.46  Inferencing          : 0.12
% 2.96/1.46  Reduction            : 0.11
% 2.96/1.46  Demodulation         : 0.08
% 2.96/1.46  BG Simplification    : 0.02
% 2.96/1.46  Subsumption          : 0.05
% 2.96/1.46  Abstraction          : 0.02
% 2.96/1.46  MUC search           : 0.00
% 2.96/1.46  Cooper               : 0.00
% 2.96/1.46  Total                : 0.68
% 2.96/1.46  Index Insertion      : 0.00
% 2.96/1.46  Index Deletion       : 0.00
% 2.96/1.46  Index Matching       : 0.00
% 2.96/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
