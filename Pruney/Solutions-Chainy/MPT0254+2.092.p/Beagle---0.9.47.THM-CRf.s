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
% DateTime   : Thu Dec  3 09:51:31 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 233 expanded)
%              Number of leaves         :   41 (  97 expanded)
%              Depth                    :   12
%              Number of atoms          :   72 ( 223 expanded)
%              Number of equality atoms :   50 ( 193 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_57,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_63,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_59,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_82,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_84,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_20,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_70,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_371,plain,(
    ! [A_98,B_99] : k5_xboole_0(A_98,k3_xboole_0(A_98,B_99)) = k4_xboole_0(A_98,B_99) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_391,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_371])).

tff(c_779,plain,(
    ! [A_128,B_129,C_130] : k5_xboole_0(k5_xboole_0(A_128,B_129),C_130) = k5_xboole_0(A_128,k5_xboole_0(B_129,C_130)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_28,plain,(
    ! [A_24,B_25] : k5_xboole_0(k5_xboole_0(A_24,B_25),k3_xboole_0(A_24,B_25)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_792,plain,(
    ! [A_128,B_129] : k5_xboole_0(A_128,k5_xboole_0(B_129,k3_xboole_0(A_128,B_129))) = k2_xboole_0(A_128,B_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_779,c_28])).

tff(c_1483,plain,(
    ! [A_166,B_167] : k5_xboole_0(A_166,k4_xboole_0(B_167,A_166)) = k2_xboole_0(A_166,B_167) ),
    inference(demodulation,[status(thm),theory(equality)],[c_391,c_792])).

tff(c_205,plain,(
    ! [B_80,A_81] : k5_xboole_0(B_80,A_81) = k5_xboole_0(A_81,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_221,plain,(
    ! [A_81] : k5_xboole_0(k1_xboole_0,A_81) = A_81 ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_20])).

tff(c_26,plain,(
    ! [A_23] : k5_xboole_0(A_23,A_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_860,plain,(
    ! [A_23,C_130] : k5_xboole_0(A_23,k5_xboole_0(A_23,C_130)) = k5_xboole_0(k1_xboole_0,C_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_779])).

tff(c_880,plain,(
    ! [A_23,C_130] : k5_xboole_0(A_23,k5_xboole_0(A_23,C_130)) = C_130 ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_860])).

tff(c_1645,plain,(
    ! [A_179,B_180] : k5_xboole_0(A_179,k2_xboole_0(A_179,B_180)) = k4_xboole_0(B_180,A_179) ),
    inference(superposition,[status(thm),theory(equality)],[c_1483,c_880])).

tff(c_1703,plain,(
    k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) = k4_xboole_0('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_1645])).

tff(c_1713,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1703])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_883,plain,(
    ! [A_131,C_132] : k5_xboole_0(A_131,k5_xboole_0(A_131,C_132)) = C_132 ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_860])).

tff(c_935,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_883])).

tff(c_18,plain,(
    ! [A_16,B_17] : r1_tarski(k4_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_361,plain,(
    ! [A_96,B_97] :
      ( k3_xboole_0(A_96,B_97) = A_96
      | ~ r1_tarski(A_96,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1317,plain,(
    ! [A_149,B_150] : k3_xboole_0(k4_xboole_0(A_149,B_150),A_149) = k4_xboole_0(A_149,B_150) ),
    inference(resolution,[status(thm)],[c_18,c_361])).

tff(c_1326,plain,(
    ! [A_149,B_150] : k5_xboole_0(k5_xboole_0(k4_xboole_0(A_149,B_150),A_149),k4_xboole_0(A_149,B_150)) = k2_xboole_0(k4_xboole_0(A_149,B_150),A_149) ),
    inference(superposition,[status(thm),theory(equality)],[c_1317,c_28])).

tff(c_1374,plain,(
    ! [A_149,B_150] : k2_xboole_0(k4_xboole_0(A_149,B_150),A_149) = A_149 ),
    inference(demodulation,[status(thm),theory(equality)],[c_935,c_4,c_4,c_1326])).

tff(c_1729,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1713,c_1374])).

tff(c_1787,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1729,c_70])).

tff(c_22,plain,(
    ! [A_19] : r1_xboole_0(A_19,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_14,plain,(
    ! [A_14] : k3_xboole_0(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_444,plain,(
    ! [A_103,B_104,C_105] :
      ( ~ r1_xboole_0(A_103,B_104)
      | ~ r2_hidden(C_105,k3_xboole_0(A_103,B_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_456,plain,(
    ! [A_14,C_105] :
      ( ~ r1_xboole_0(A_14,k1_xboole_0)
      | ~ r2_hidden(C_105,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_444])).

tff(c_458,plain,(
    ! [C_105] : ~ r2_hidden(C_105,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_456])).

tff(c_1802,plain,(
    ! [C_105] : ~ r2_hidden(C_105,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1787,c_458])).

tff(c_606,plain,(
    ! [A_119,B_120] : k5_xboole_0(k5_xboole_0(A_119,B_120),k3_xboole_0(A_119,B_120)) = k2_xboole_0(A_119,B_120) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_660,plain,(
    ! [A_14] : k5_xboole_0(k5_xboole_0(A_14,k1_xboole_0),k1_xboole_0) = k2_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_606])).

tff(c_674,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_660])).

tff(c_1870,plain,(
    ! [A_194] : k2_xboole_0(A_194,'#skF_5') = A_194 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1787,c_674])).

tff(c_1876,plain,(
    k1_tarski('#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1870,c_1729])).

tff(c_54,plain,(
    ! [A_33] : k2_tarski(A_33,A_33) = k1_tarski(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_303,plain,(
    ! [A_86,B_87] : k1_enumset1(A_86,A_86,B_87) = k2_tarski(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_32,plain,(
    ! [E_32,A_26,B_27] : r2_hidden(E_32,k1_enumset1(A_26,B_27,E_32)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_321,plain,(
    ! [B_88,A_89] : r2_hidden(B_88,k2_tarski(A_89,B_88)) ),
    inference(superposition,[status(thm),theory(equality)],[c_303,c_32])).

tff(c_324,plain,(
    ! [A_33] : r2_hidden(A_33,k1_tarski(A_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_321])).

tff(c_1920,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1876,c_324])).

tff(c_1924,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1802,c_1920])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n018.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 18:37:12 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.19/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.51  
% 3.19/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.51  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.19/1.51  
% 3.19/1.51  %Foreground sorts:
% 3.19/1.51  
% 3.19/1.51  
% 3.19/1.51  %Background operators:
% 3.19/1.51  
% 3.19/1.51  
% 3.19/1.51  %Foreground operators:
% 3.19/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.19/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.19/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.19/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.19/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.19/1.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.19/1.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.19/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.19/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.19/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.19/1.51  tff('#skF_5', type, '#skF_5': $i).
% 3.19/1.51  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.19/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.19/1.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.19/1.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.19/1.51  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.19/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.19/1.51  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.19/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.19/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.19/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.19/1.51  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.19/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.19/1.51  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.19/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.19/1.51  
% 3.55/1.53  tff(f_57, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.55/1.53  tff(f_100, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.55/1.53  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.55/1.53  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.55/1.53  tff(f_61, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.55/1.53  tff(f_65, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 3.55/1.53  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.55/1.53  tff(f_63, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.55/1.53  tff(f_55, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.55/1.53  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.55/1.53  tff(f_59, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.55/1.53  tff(f_51, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.55/1.53  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.55/1.53  tff(f_82, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.55/1.53  tff(f_84, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.55/1.53  tff(f_80, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.55/1.53  tff(c_20, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.55/1.53  tff(c_70, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.55/1.53  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.55/1.53  tff(c_371, plain, (![A_98, B_99]: (k5_xboole_0(A_98, k3_xboole_0(A_98, B_99))=k4_xboole_0(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.55/1.53  tff(c_391, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_371])).
% 3.55/1.53  tff(c_779, plain, (![A_128, B_129, C_130]: (k5_xboole_0(k5_xboole_0(A_128, B_129), C_130)=k5_xboole_0(A_128, k5_xboole_0(B_129, C_130)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.55/1.53  tff(c_28, plain, (![A_24, B_25]: (k5_xboole_0(k5_xboole_0(A_24, B_25), k3_xboole_0(A_24, B_25))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.55/1.53  tff(c_792, plain, (![A_128, B_129]: (k5_xboole_0(A_128, k5_xboole_0(B_129, k3_xboole_0(A_128, B_129)))=k2_xboole_0(A_128, B_129))), inference(superposition, [status(thm), theory('equality')], [c_779, c_28])).
% 3.55/1.53  tff(c_1483, plain, (![A_166, B_167]: (k5_xboole_0(A_166, k4_xboole_0(B_167, A_166))=k2_xboole_0(A_166, B_167))), inference(demodulation, [status(thm), theory('equality')], [c_391, c_792])).
% 3.55/1.53  tff(c_205, plain, (![B_80, A_81]: (k5_xboole_0(B_80, A_81)=k5_xboole_0(A_81, B_80))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.55/1.53  tff(c_221, plain, (![A_81]: (k5_xboole_0(k1_xboole_0, A_81)=A_81)), inference(superposition, [status(thm), theory('equality')], [c_205, c_20])).
% 3.55/1.53  tff(c_26, plain, (![A_23]: (k5_xboole_0(A_23, A_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.55/1.53  tff(c_860, plain, (![A_23, C_130]: (k5_xboole_0(A_23, k5_xboole_0(A_23, C_130))=k5_xboole_0(k1_xboole_0, C_130))), inference(superposition, [status(thm), theory('equality')], [c_26, c_779])).
% 3.55/1.53  tff(c_880, plain, (![A_23, C_130]: (k5_xboole_0(A_23, k5_xboole_0(A_23, C_130))=C_130)), inference(demodulation, [status(thm), theory('equality')], [c_221, c_860])).
% 3.55/1.53  tff(c_1645, plain, (![A_179, B_180]: (k5_xboole_0(A_179, k2_xboole_0(A_179, B_180))=k4_xboole_0(B_180, A_179))), inference(superposition, [status(thm), theory('equality')], [c_1483, c_880])).
% 3.55/1.53  tff(c_1703, plain, (k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)=k4_xboole_0('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_1645])).
% 3.55/1.53  tff(c_1713, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_4'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1703])).
% 3.55/1.53  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.55/1.53  tff(c_883, plain, (![A_131, C_132]: (k5_xboole_0(A_131, k5_xboole_0(A_131, C_132))=C_132)), inference(demodulation, [status(thm), theory('equality')], [c_221, c_860])).
% 3.55/1.53  tff(c_935, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_883])).
% 3.55/1.53  tff(c_18, plain, (![A_16, B_17]: (r1_tarski(k4_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.55/1.53  tff(c_361, plain, (![A_96, B_97]: (k3_xboole_0(A_96, B_97)=A_96 | ~r1_tarski(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.55/1.53  tff(c_1317, plain, (![A_149, B_150]: (k3_xboole_0(k4_xboole_0(A_149, B_150), A_149)=k4_xboole_0(A_149, B_150))), inference(resolution, [status(thm)], [c_18, c_361])).
% 3.55/1.53  tff(c_1326, plain, (![A_149, B_150]: (k5_xboole_0(k5_xboole_0(k4_xboole_0(A_149, B_150), A_149), k4_xboole_0(A_149, B_150))=k2_xboole_0(k4_xboole_0(A_149, B_150), A_149))), inference(superposition, [status(thm), theory('equality')], [c_1317, c_28])).
% 3.55/1.53  tff(c_1374, plain, (![A_149, B_150]: (k2_xboole_0(k4_xboole_0(A_149, B_150), A_149)=A_149)), inference(demodulation, [status(thm), theory('equality')], [c_935, c_4, c_4, c_1326])).
% 3.55/1.53  tff(c_1729, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1713, c_1374])).
% 3.55/1.53  tff(c_1787, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1729, c_70])).
% 3.55/1.53  tff(c_22, plain, (![A_19]: (r1_xboole_0(A_19, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.55/1.53  tff(c_14, plain, (![A_14]: (k3_xboole_0(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.55/1.53  tff(c_444, plain, (![A_103, B_104, C_105]: (~r1_xboole_0(A_103, B_104) | ~r2_hidden(C_105, k3_xboole_0(A_103, B_104)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.55/1.53  tff(c_456, plain, (![A_14, C_105]: (~r1_xboole_0(A_14, k1_xboole_0) | ~r2_hidden(C_105, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_444])).
% 3.55/1.53  tff(c_458, plain, (![C_105]: (~r2_hidden(C_105, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_456])).
% 3.55/1.53  tff(c_1802, plain, (![C_105]: (~r2_hidden(C_105, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1787, c_458])).
% 3.55/1.53  tff(c_606, plain, (![A_119, B_120]: (k5_xboole_0(k5_xboole_0(A_119, B_120), k3_xboole_0(A_119, B_120))=k2_xboole_0(A_119, B_120))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.55/1.53  tff(c_660, plain, (![A_14]: (k5_xboole_0(k5_xboole_0(A_14, k1_xboole_0), k1_xboole_0)=k2_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_606])).
% 3.55/1.53  tff(c_674, plain, (![A_14]: (k2_xboole_0(A_14, k1_xboole_0)=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_660])).
% 3.55/1.53  tff(c_1870, plain, (![A_194]: (k2_xboole_0(A_194, '#skF_5')=A_194)), inference(demodulation, [status(thm), theory('equality')], [c_1787, c_674])).
% 3.55/1.53  tff(c_1876, plain, (k1_tarski('#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1870, c_1729])).
% 3.55/1.53  tff(c_54, plain, (![A_33]: (k2_tarski(A_33, A_33)=k1_tarski(A_33))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.55/1.53  tff(c_303, plain, (![A_86, B_87]: (k1_enumset1(A_86, A_86, B_87)=k2_tarski(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.55/1.53  tff(c_32, plain, (![E_32, A_26, B_27]: (r2_hidden(E_32, k1_enumset1(A_26, B_27, E_32)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.55/1.53  tff(c_321, plain, (![B_88, A_89]: (r2_hidden(B_88, k2_tarski(A_89, B_88)))), inference(superposition, [status(thm), theory('equality')], [c_303, c_32])).
% 3.55/1.53  tff(c_324, plain, (![A_33]: (r2_hidden(A_33, k1_tarski(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_321])).
% 3.55/1.53  tff(c_1920, plain, (r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1876, c_324])).
% 3.55/1.53  tff(c_1924, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1802, c_1920])).
% 3.55/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.53  
% 3.55/1.53  Inference rules
% 3.55/1.53  ----------------------
% 3.55/1.53  #Ref     : 0
% 3.55/1.53  #Sup     : 453
% 3.55/1.53  #Fact    : 0
% 3.55/1.53  #Define  : 0
% 3.55/1.53  #Split   : 0
% 3.55/1.53  #Chain   : 0
% 3.55/1.53  #Close   : 0
% 3.55/1.53  
% 3.55/1.53  Ordering : KBO
% 3.55/1.53  
% 3.55/1.53  Simplification rules
% 3.55/1.53  ----------------------
% 3.55/1.53  #Subsume      : 15
% 3.55/1.53  #Demod        : 266
% 3.55/1.53  #Tautology    : 305
% 3.55/1.53  #SimpNegUnit  : 3
% 3.55/1.53  #BackRed      : 22
% 3.55/1.53  
% 3.55/1.53  #Partial instantiations: 0
% 3.55/1.53  #Strategies tried      : 1
% 3.55/1.53  
% 3.55/1.53  Timing (in seconds)
% 3.55/1.53  ----------------------
% 3.55/1.53  Preprocessing        : 0.32
% 3.55/1.53  Parsing              : 0.17
% 3.55/1.53  CNF conversion       : 0.02
% 3.55/1.53  Main loop            : 0.46
% 3.55/1.53  Inferencing          : 0.16
% 3.55/1.53  Reduction            : 0.18
% 3.55/1.53  Demodulation         : 0.15
% 3.55/1.53  BG Simplification    : 0.02
% 3.55/1.53  Subsumption          : 0.07
% 3.55/1.53  Abstraction          : 0.03
% 3.55/1.53  MUC search           : 0.00
% 3.55/1.53  Cooper               : 0.00
% 3.55/1.53  Total                : 0.82
% 3.55/1.53  Index Insertion      : 0.00
% 3.55/1.53  Index Deletion       : 0.00
% 3.55/1.53  Index Matching       : 0.00
% 3.55/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
