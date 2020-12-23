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
% DateTime   : Thu Dec  3 09:49:34 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 102 expanded)
%              Number of leaves         :   41 (  51 expanded)
%              Depth                    :   15
%              Number of atoms          :   83 ( 110 expanded)
%              Number of equality atoms :   61 (  83 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_64,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_68,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_70,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_72,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_74,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_76,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_60,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_58,plain,(
    '#skF_6' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_46,plain,(
    ! [A_32,B_33,C_34] : k2_enumset1(A_32,A_32,B_33,C_34) = k1_enumset1(A_32,B_33,C_34) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_44,plain,(
    ! [A_30,B_31] : k1_enumset1(A_30,A_30,B_31) = k2_tarski(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_48,plain,(
    ! [A_35,B_36,C_37,D_38] : k3_enumset1(A_35,A_35,B_36,C_37,D_38) = k2_enumset1(A_35,B_36,C_37,D_38) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_50,plain,(
    ! [E_43,D_42,A_39,C_41,B_40] : k4_enumset1(A_39,A_39,B_40,C_41,D_42,E_43) = k3_enumset1(A_39,B_40,C_41,D_42,E_43) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_52,plain,(
    ! [C_46,E_48,F_49,A_44,B_45,D_47] : k5_enumset1(A_44,A_44,B_45,C_46,D_47,E_48,F_49) = k4_enumset1(A_44,B_45,C_46,D_47,E_48,F_49) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_54,plain,(
    ! [A_50,B_51,G_56,E_54,C_52,D_53,F_55] : k6_enumset1(A_50,A_50,B_51,C_52,D_53,E_54,F_55,G_56) = k5_enumset1(A_50,B_51,C_52,D_53,E_54,F_55,G_56) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_567,plain,(
    ! [D_170,H_171,F_173,B_174,E_175,A_169,G_168,C_172] : k2_xboole_0(k5_enumset1(A_169,B_174,C_172,D_170,E_175,F_173,G_168),k1_tarski(H_171)) = k6_enumset1(A_169,B_174,C_172,D_170,E_175,F_173,G_168,H_171) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_576,plain,(
    ! [C_46,H_171,E_48,F_49,A_44,B_45,D_47] : k6_enumset1(A_44,A_44,B_45,C_46,D_47,E_48,F_49,H_171) = k2_xboole_0(k4_enumset1(A_44,B_45,C_46,D_47,E_48,F_49),k1_tarski(H_171)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_567])).

tff(c_580,plain,(
    ! [D_179,A_182,F_177,C_180,H_178,E_176,B_181] : k2_xboole_0(k4_enumset1(A_182,B_181,C_180,D_179,E_176,F_177),k1_tarski(H_178)) = k5_enumset1(A_182,B_181,C_180,D_179,E_176,F_177,H_178) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_576])).

tff(c_589,plain,(
    ! [E_43,D_42,H_178,A_39,C_41,B_40] : k5_enumset1(A_39,A_39,B_40,C_41,D_42,E_43,H_178) = k2_xboole_0(k3_enumset1(A_39,B_40,C_41,D_42,E_43),k1_tarski(H_178)) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_580])).

tff(c_593,plain,(
    ! [E_188,D_187,A_183,H_185,B_184,C_186] : k2_xboole_0(k3_enumset1(A_183,B_184,C_186,D_187,E_188),k1_tarski(H_185)) = k4_enumset1(A_183,B_184,C_186,D_187,E_188,H_185) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_589])).

tff(c_602,plain,(
    ! [A_35,B_36,C_37,D_38,H_185] : k4_enumset1(A_35,A_35,B_36,C_37,D_38,H_185) = k2_xboole_0(k2_enumset1(A_35,B_36,C_37,D_38),k1_tarski(H_185)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_593])).

tff(c_606,plain,(
    ! [H_190,D_192,C_191,A_189,B_193] : k2_xboole_0(k2_enumset1(A_189,B_193,C_191,D_192),k1_tarski(H_190)) = k3_enumset1(A_189,B_193,C_191,D_192,H_190) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_602])).

tff(c_615,plain,(
    ! [A_32,B_33,C_34,H_190] : k3_enumset1(A_32,A_32,B_33,C_34,H_190) = k2_xboole_0(k1_enumset1(A_32,B_33,C_34),k1_tarski(H_190)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_606])).

tff(c_619,plain,(
    ! [A_194,B_195,C_196,H_197] : k2_xboole_0(k1_enumset1(A_194,B_195,C_196),k1_tarski(H_197)) = k2_enumset1(A_194,B_195,C_196,H_197) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_615])).

tff(c_628,plain,(
    ! [A_30,B_31,H_197] : k2_xboole_0(k2_tarski(A_30,B_31),k1_tarski(H_197)) = k2_enumset1(A_30,A_30,B_31,H_197) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_619])).

tff(c_632,plain,(
    ! [A_198,B_199,H_200] : k2_xboole_0(k2_tarski(A_198,B_199),k1_tarski(H_200)) = k1_enumset1(A_198,B_199,H_200) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_628])).

tff(c_10,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_56,plain,(
    ! [A_57,B_58] : r1_tarski(k1_tarski(A_57),k2_tarski(A_57,B_58)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_62,plain,(
    r1_tarski(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_162,plain,(
    ! [A_81,B_82] :
      ( k3_xboole_0(A_81,B_82) = A_81
      | ~ r1_tarski(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_172,plain,(
    k3_xboole_0(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_5','#skF_6')) = k2_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_162])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_194,plain,(
    ! [A_86,B_87,C_88] :
      ( r1_tarski(A_86,B_87)
      | ~ r1_tarski(A_86,k3_xboole_0(B_87,C_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_344,plain,(
    ! [A_104,B_105,A_106] :
      ( r1_tarski(A_104,B_105)
      | ~ r1_tarski(A_104,k3_xboole_0(A_106,B_105)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_194])).

tff(c_399,plain,(
    ! [A_116] :
      ( r1_tarski(A_116,k2_tarski('#skF_5','#skF_6'))
      | ~ r1_tarski(A_116,k2_tarski('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_344])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_409,plain,(
    ! [A_120] :
      ( k3_xboole_0(A_120,k2_tarski('#skF_5','#skF_6')) = A_120
      | ~ r1_tarski(A_120,k2_tarski('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_399,c_8])).

tff(c_419,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_5','#skF_6')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_409])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_429,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_419,c_4])).

tff(c_435,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_429])).

tff(c_14,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_440,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_6'),k1_tarski('#skF_3')) = k5_xboole_0(k2_tarski('#skF_5','#skF_6'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_14])).

tff(c_443,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_6'),k1_tarski('#skF_3')) = k2_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_440])).

tff(c_638,plain,(
    k1_enumset1('#skF_5','#skF_6','#skF_3') = k2_tarski('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_632,c_443])).

tff(c_18,plain,(
    ! [E_20,A_14,B_15] : r2_hidden(E_20,k1_enumset1(A_14,B_15,E_20)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_713,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_638,c_18])).

tff(c_458,plain,(
    ! [E_122,C_123,B_124,A_125] :
      ( E_122 = C_123
      | E_122 = B_124
      | E_122 = A_125
      | ~ r2_hidden(E_122,k1_enumset1(A_125,B_124,C_123)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_461,plain,(
    ! [E_122,B_31,A_30] :
      ( E_122 = B_31
      | E_122 = A_30
      | E_122 = A_30
      | ~ r2_hidden(E_122,k2_tarski(A_30,B_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_458])).

tff(c_723,plain,
    ( '#skF_6' = '#skF_3'
    | '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_713,c_461])).

tff(c_727,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_60,c_58,c_723])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:53:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.50  
% 2.77/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.50  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 2.77/1.50  
% 2.77/1.50  %Foreground sorts:
% 2.77/1.50  
% 2.77/1.50  
% 2.77/1.50  %Background operators:
% 2.77/1.50  
% 2.77/1.50  
% 2.77/1.50  %Foreground operators:
% 2.77/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.77/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.77/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.77/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.77/1.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.77/1.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.77/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.77/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.77/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.77/1.50  tff('#skF_5', type, '#skF_5': $i).
% 2.77/1.50  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.77/1.50  tff('#skF_6', type, '#skF_6': $i).
% 2.77/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.77/1.50  tff('#skF_3', type, '#skF_3': $i).
% 2.77/1.50  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.77/1.50  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.77/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.50  tff('#skF_4', type, '#skF_4': $i).
% 2.77/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.77/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.77/1.50  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.77/1.50  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.77/1.50  
% 3.15/1.52  tff(f_86, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 3.15/1.52  tff(f_66, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.15/1.52  tff(f_64, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.15/1.52  tff(f_68, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.15/1.52  tff(f_70, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 3.15/1.52  tff(f_72, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 3.15/1.52  tff(f_74, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 3.15/1.52  tff(f_60, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_enumset1)).
% 3.15/1.52  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.15/1.52  tff(f_41, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.15/1.52  tff(f_76, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 3.15/1.52  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.15/1.52  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.15/1.52  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 3.15/1.52  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.15/1.52  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.15/1.52  tff(f_58, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.15/1.52  tff(c_60, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.15/1.52  tff(c_58, plain, ('#skF_6'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.15/1.52  tff(c_46, plain, (![A_32, B_33, C_34]: (k2_enumset1(A_32, A_32, B_33, C_34)=k1_enumset1(A_32, B_33, C_34))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.15/1.52  tff(c_44, plain, (![A_30, B_31]: (k1_enumset1(A_30, A_30, B_31)=k2_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.15/1.52  tff(c_48, plain, (![A_35, B_36, C_37, D_38]: (k3_enumset1(A_35, A_35, B_36, C_37, D_38)=k2_enumset1(A_35, B_36, C_37, D_38))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.15/1.52  tff(c_50, plain, (![E_43, D_42, A_39, C_41, B_40]: (k4_enumset1(A_39, A_39, B_40, C_41, D_42, E_43)=k3_enumset1(A_39, B_40, C_41, D_42, E_43))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.15/1.52  tff(c_52, plain, (![C_46, E_48, F_49, A_44, B_45, D_47]: (k5_enumset1(A_44, A_44, B_45, C_46, D_47, E_48, F_49)=k4_enumset1(A_44, B_45, C_46, D_47, E_48, F_49))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.15/1.52  tff(c_54, plain, (![A_50, B_51, G_56, E_54, C_52, D_53, F_55]: (k6_enumset1(A_50, A_50, B_51, C_52, D_53, E_54, F_55, G_56)=k5_enumset1(A_50, B_51, C_52, D_53, E_54, F_55, G_56))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.15/1.52  tff(c_567, plain, (![D_170, H_171, F_173, B_174, E_175, A_169, G_168, C_172]: (k2_xboole_0(k5_enumset1(A_169, B_174, C_172, D_170, E_175, F_173, G_168), k1_tarski(H_171))=k6_enumset1(A_169, B_174, C_172, D_170, E_175, F_173, G_168, H_171))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.15/1.52  tff(c_576, plain, (![C_46, H_171, E_48, F_49, A_44, B_45, D_47]: (k6_enumset1(A_44, A_44, B_45, C_46, D_47, E_48, F_49, H_171)=k2_xboole_0(k4_enumset1(A_44, B_45, C_46, D_47, E_48, F_49), k1_tarski(H_171)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_567])).
% 3.15/1.52  tff(c_580, plain, (![D_179, A_182, F_177, C_180, H_178, E_176, B_181]: (k2_xboole_0(k4_enumset1(A_182, B_181, C_180, D_179, E_176, F_177), k1_tarski(H_178))=k5_enumset1(A_182, B_181, C_180, D_179, E_176, F_177, H_178))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_576])).
% 3.15/1.52  tff(c_589, plain, (![E_43, D_42, H_178, A_39, C_41, B_40]: (k5_enumset1(A_39, A_39, B_40, C_41, D_42, E_43, H_178)=k2_xboole_0(k3_enumset1(A_39, B_40, C_41, D_42, E_43), k1_tarski(H_178)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_580])).
% 3.15/1.52  tff(c_593, plain, (![E_188, D_187, A_183, H_185, B_184, C_186]: (k2_xboole_0(k3_enumset1(A_183, B_184, C_186, D_187, E_188), k1_tarski(H_185))=k4_enumset1(A_183, B_184, C_186, D_187, E_188, H_185))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_589])).
% 3.15/1.52  tff(c_602, plain, (![A_35, B_36, C_37, D_38, H_185]: (k4_enumset1(A_35, A_35, B_36, C_37, D_38, H_185)=k2_xboole_0(k2_enumset1(A_35, B_36, C_37, D_38), k1_tarski(H_185)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_593])).
% 3.15/1.52  tff(c_606, plain, (![H_190, D_192, C_191, A_189, B_193]: (k2_xboole_0(k2_enumset1(A_189, B_193, C_191, D_192), k1_tarski(H_190))=k3_enumset1(A_189, B_193, C_191, D_192, H_190))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_602])).
% 3.15/1.52  tff(c_615, plain, (![A_32, B_33, C_34, H_190]: (k3_enumset1(A_32, A_32, B_33, C_34, H_190)=k2_xboole_0(k1_enumset1(A_32, B_33, C_34), k1_tarski(H_190)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_606])).
% 3.15/1.52  tff(c_619, plain, (![A_194, B_195, C_196, H_197]: (k2_xboole_0(k1_enumset1(A_194, B_195, C_196), k1_tarski(H_197))=k2_enumset1(A_194, B_195, C_196, H_197))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_615])).
% 3.15/1.52  tff(c_628, plain, (![A_30, B_31, H_197]: (k2_xboole_0(k2_tarski(A_30, B_31), k1_tarski(H_197))=k2_enumset1(A_30, A_30, B_31, H_197))), inference(superposition, [status(thm), theory('equality')], [c_44, c_619])).
% 3.15/1.52  tff(c_632, plain, (![A_198, B_199, H_200]: (k2_xboole_0(k2_tarski(A_198, B_199), k1_tarski(H_200))=k1_enumset1(A_198, B_199, H_200))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_628])).
% 3.15/1.52  tff(c_10, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.15/1.52  tff(c_12, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.15/1.52  tff(c_56, plain, (![A_57, B_58]: (r1_tarski(k1_tarski(A_57), k2_tarski(A_57, B_58)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.15/1.52  tff(c_62, plain, (r1_tarski(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.15/1.52  tff(c_162, plain, (![A_81, B_82]: (k3_xboole_0(A_81, B_82)=A_81 | ~r1_tarski(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.15/1.52  tff(c_172, plain, (k3_xboole_0(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_5', '#skF_6'))=k2_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_62, c_162])).
% 3.15/1.52  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.15/1.52  tff(c_194, plain, (![A_86, B_87, C_88]: (r1_tarski(A_86, B_87) | ~r1_tarski(A_86, k3_xboole_0(B_87, C_88)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.15/1.52  tff(c_344, plain, (![A_104, B_105, A_106]: (r1_tarski(A_104, B_105) | ~r1_tarski(A_104, k3_xboole_0(A_106, B_105)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_194])).
% 3.15/1.52  tff(c_399, plain, (![A_116]: (r1_tarski(A_116, k2_tarski('#skF_5', '#skF_6')) | ~r1_tarski(A_116, k2_tarski('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_172, c_344])).
% 3.15/1.52  tff(c_8, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.15/1.52  tff(c_409, plain, (![A_120]: (k3_xboole_0(A_120, k2_tarski('#skF_5', '#skF_6'))=A_120 | ~r1_tarski(A_120, k2_tarski('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_399, c_8])).
% 3.15/1.52  tff(c_419, plain, (k3_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_5', '#skF_6'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_56, c_409])).
% 3.15/1.52  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.15/1.52  tff(c_429, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_419, c_4])).
% 3.15/1.52  tff(c_435, plain, (k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_429])).
% 3.15/1.52  tff(c_14, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k4_xboole_0(B_13, A_12))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.15/1.52  tff(c_440, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), k1_tarski('#skF_3'))=k5_xboole_0(k2_tarski('#skF_5', '#skF_6'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_435, c_14])).
% 3.15/1.52  tff(c_443, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), k1_tarski('#skF_3'))=k2_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_440])).
% 3.15/1.52  tff(c_638, plain, (k1_enumset1('#skF_5', '#skF_6', '#skF_3')=k2_tarski('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_632, c_443])).
% 3.15/1.52  tff(c_18, plain, (![E_20, A_14, B_15]: (r2_hidden(E_20, k1_enumset1(A_14, B_15, E_20)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.15/1.52  tff(c_713, plain, (r2_hidden('#skF_3', k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_638, c_18])).
% 3.15/1.52  tff(c_458, plain, (![E_122, C_123, B_124, A_125]: (E_122=C_123 | E_122=B_124 | E_122=A_125 | ~r2_hidden(E_122, k1_enumset1(A_125, B_124, C_123)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.15/1.52  tff(c_461, plain, (![E_122, B_31, A_30]: (E_122=B_31 | E_122=A_30 | E_122=A_30 | ~r2_hidden(E_122, k2_tarski(A_30, B_31)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_458])).
% 3.15/1.52  tff(c_723, plain, ('#skF_6'='#skF_3' | '#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_713, c_461])).
% 3.15/1.52  tff(c_727, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_60, c_58, c_723])).
% 3.15/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.52  
% 3.15/1.52  Inference rules
% 3.15/1.52  ----------------------
% 3.15/1.52  #Ref     : 0
% 3.15/1.52  #Sup     : 165
% 3.15/1.52  #Fact    : 0
% 3.15/1.52  #Define  : 0
% 3.15/1.52  #Split   : 0
% 3.15/1.52  #Chain   : 0
% 3.15/1.52  #Close   : 0
% 3.15/1.52  
% 3.15/1.52  Ordering : KBO
% 3.15/1.52  
% 3.15/1.52  Simplification rules
% 3.15/1.52  ----------------------
% 3.15/1.52  #Subsume      : 4
% 3.15/1.52  #Demod        : 43
% 3.15/1.52  #Tautology    : 115
% 3.15/1.52  #SimpNegUnit  : 1
% 3.15/1.52  #BackRed      : 0
% 3.15/1.52  
% 3.15/1.52  #Partial instantiations: 0
% 3.15/1.52  #Strategies tried      : 1
% 3.15/1.52  
% 3.15/1.52  Timing (in seconds)
% 3.15/1.52  ----------------------
% 3.15/1.52  Preprocessing        : 0.35
% 3.15/1.52  Parsing              : 0.19
% 3.15/1.52  CNF conversion       : 0.03
% 3.15/1.52  Main loop            : 0.34
% 3.15/1.52  Inferencing          : 0.13
% 3.15/1.52  Reduction            : 0.11
% 3.15/1.52  Demodulation         : 0.08
% 3.15/1.52  BG Simplification    : 0.02
% 3.15/1.52  Subsumption          : 0.06
% 3.15/1.52  Abstraction          : 0.02
% 3.15/1.52  MUC search           : 0.00
% 3.15/1.52  Cooper               : 0.00
% 3.15/1.52  Total                : 0.73
% 3.15/1.52  Index Insertion      : 0.00
% 3.15/1.52  Index Deletion       : 0.00
% 3.15/1.52  Index Matching       : 0.00
% 3.15/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
