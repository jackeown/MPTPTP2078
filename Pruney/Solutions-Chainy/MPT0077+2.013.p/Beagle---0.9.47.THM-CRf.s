%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:37 EST 2020

% Result     : Theorem 17.99s
% Output     : CNFRefutation 18.17s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 324 expanded)
%              Number of leaves         :   32 ( 115 expanded)
%              Depth                    :   13
%              Number of atoms          :  186 ( 571 expanded)
%              Number of equality atoms :   54 ( 128 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_100,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
            & r1_xboole_0(A,B)
            & r1_xboole_0(A,C) )
        & ~ ( ~ ( r1_xboole_0(A,B)
                & r1_xboole_0(A,C) )
            & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_67,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_69,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_83,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_74222,plain,(
    ! [A_1096,B_1097] :
      ( r1_xboole_0(A_1096,B_1097)
      | k3_xboole_0(A_1096,B_1097) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_74352,plain,(
    ! [B_1109,A_1110] :
      ( r1_xboole_0(B_1109,A_1110)
      | k3_xboole_0(A_1110,B_1109) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_74222,c_8])).

tff(c_69890,plain,(
    ! [A_959,B_960] :
      ( r1_xboole_0(A_959,B_960)
      | k3_xboole_0(A_959,B_960) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_69901,plain,(
    ! [B_960,A_959] :
      ( r1_xboole_0(B_960,A_959)
      | k3_xboole_0(A_959,B_960) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_69890,c_8])).

tff(c_250,plain,(
    ! [A_56,B_57] :
      ( r1_xboole_0(A_56,B_57)
      | k3_xboole_0(A_56,B_57) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_257,plain,(
    ! [B_57,A_56] :
      ( r1_xboole_0(B_57,A_56)
      | k3_xboole_0(A_56,B_57) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_250,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_46,plain,
    ( r1_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5'))
    | ~ r1_xboole_0('#skF_6',k2_xboole_0('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_49,plain,
    ( r1_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5'))
    | ~ r1_xboole_0('#skF_6',k2_xboole_0('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_46])).

tff(c_570,plain,(
    ~ r1_xboole_0('#skF_6',k2_xboole_0('#skF_8','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_49])).

tff(c_577,plain,(
    k3_xboole_0(k2_xboole_0('#skF_8','#skF_7'),'#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_257,c_570])).

tff(c_38,plain,
    ( r1_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5'))
    | r1_xboole_0('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_225,plain,(
    r1_xboole_0('#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_231,plain,(
    k3_xboole_0('#skF_6','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_225,c_4])).

tff(c_899,plain,(
    ! [A_86,B_87] : k2_xboole_0(k3_xboole_0(A_86,B_87),k4_xboole_0(A_86,B_87)) = A_86 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_962,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_6','#skF_8')) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_899])).

tff(c_24,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_267,plain,(
    ! [A_60,B_61] : k4_xboole_0(k2_xboole_0(A_60,B_61),B_61) = k4_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_274,plain,(
    ! [A_60] : k4_xboole_0(A_60,k1_xboole_0) = k2_xboole_0(A_60,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_24])).

tff(c_293,plain,(
    ! [A_62] : k2_xboole_0(A_62,k1_xboole_0) = A_62 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_274])).

tff(c_311,plain,(
    ! [A_62] : k2_xboole_0(k1_xboole_0,A_62) = A_62 ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_2])).

tff(c_1159,plain,(
    k4_xboole_0('#skF_6','#skF_8') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_962,c_311])).

tff(c_42,plain,
    ( r1_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5'))
    | r1_xboole_0('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_114,plain,(
    r1_xboole_0('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_120,plain,(
    k3_xboole_0('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_114,c_4])).

tff(c_977,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_6','#skF_7')) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_899])).

tff(c_1235,plain,(
    k4_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_977,c_311])).

tff(c_1468,plain,(
    ! [A_105,B_106,C_107] : k4_xboole_0(k4_xboole_0(A_105,B_106),C_107) = k4_xboole_0(A_105,k2_xboole_0(B_106,C_107)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_57091,plain,(
    ! [C_703] : k4_xboole_0('#skF_6',k2_xboole_0('#skF_7',C_703)) = k4_xboole_0('#skF_6',C_703) ),
    inference(superposition,[status(thm),theory(equality)],[c_1235,c_1468])).

tff(c_397,plain,(
    ! [A_65,B_66,C_67] :
      ( ~ r1_xboole_0(A_65,B_66)
      | ~ r2_hidden(C_67,k3_xboole_0(A_65,B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_403,plain,(
    ! [C_67] :
      ( ~ r1_xboole_0('#skF_6','#skF_8')
      | ~ r2_hidden(C_67,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_397])).

tff(c_417,plain,(
    ! [C_67] : ~ r2_hidden(C_67,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_403])).

tff(c_64,plain,(
    ! [B_41,A_42] : k2_xboole_0(B_41,A_42) = k2_xboole_0(A_42,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    ! [A_32,B_33] : r1_tarski(A_32,k2_xboole_0(A_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_79,plain,(
    ! [A_42,B_41] : r1_tarski(A_42,k2_xboole_0(B_41,A_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_36])).

tff(c_139,plain,(
    ! [A_49,B_50] :
      ( k4_xboole_0(A_49,B_50) = k1_xboole_0
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_153,plain,(
    ! [A_42,B_41] : k4_xboole_0(A_42,k2_xboole_0(B_41,A_42)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_79,c_139])).

tff(c_22,plain,(
    ! [A_17,B_18] : k2_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1503,plain,(
    ! [C_107,A_105,B_106] : k2_xboole_0(C_107,k4_xboole_0(A_105,k2_xboole_0(B_106,C_107))) = k2_xboole_0(C_107,k4_xboole_0(A_105,B_106)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1468,c_22])).

tff(c_28,plain,(
    ! [A_22,B_23,C_24] : k4_xboole_0(k4_xboole_0(A_22,B_23),C_24) = k4_xboole_0(A_22,k2_xboole_0(B_23,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_30,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k4_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1547,plain,(
    ! [A_105,B_106,B_26] : k4_xboole_0(A_105,k2_xboole_0(B_106,k4_xboole_0(k4_xboole_0(A_105,B_106),B_26))) = k3_xboole_0(k4_xboole_0(A_105,B_106),B_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1468])).

tff(c_10975,plain,(
    ! [A_259,B_260,B_261] : k4_xboole_0(A_259,k2_xboole_0(B_260,k4_xboole_0(A_259,k2_xboole_0(B_260,B_261)))) = k3_xboole_0(k4_xboole_0(A_259,B_260),B_261) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1547])).

tff(c_11178,plain,(
    ! [A_105,B_106] : k4_xboole_0(A_105,k2_xboole_0(B_106,k4_xboole_0(A_105,B_106))) = k3_xboole_0(k4_xboole_0(A_105,B_106),B_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_1503,c_10975])).

tff(c_11323,plain,(
    ! [A_262,B_263] : k3_xboole_0(k4_xboole_0(A_262,B_263),B_263) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_22,c_11178])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_1'(A_7,B_8),k3_xboole_0(A_7,B_8))
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_11373,plain,(
    ! [A_262,B_263] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_262,B_263),B_263),k1_xboole_0)
      | r1_xboole_0(k4_xboole_0(A_262,B_263),B_263) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11323,c_10])).

tff(c_11527,plain,(
    ! [A_264,B_265] : r1_xboole_0(k4_xboole_0(A_264,B_265),B_265) ),
    inference(negUnitSimplification,[status(thm)],[c_417,c_11373])).

tff(c_11610,plain,(
    ! [B_265,A_264] : r1_xboole_0(B_265,k4_xboole_0(A_264,B_265)) ),
    inference(resolution,[status(thm)],[c_11527,c_8])).

tff(c_58336,plain,(
    ! [C_706] : r1_xboole_0(k2_xboole_0('#skF_7',C_706),k4_xboole_0('#skF_6',C_706)) ),
    inference(superposition,[status(thm),theory(equality)],[c_57091,c_11610])).

tff(c_58450,plain,(
    r1_xboole_0(k2_xboole_0('#skF_7','#skF_8'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1159,c_58336])).

tff(c_58502,plain,(
    r1_xboole_0(k2_xboole_0('#skF_8','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_58450])).

tff(c_58512,plain,(
    k3_xboole_0(k2_xboole_0('#skF_8','#skF_7'),'#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58502,c_4])).

tff(c_58525,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_577,c_58512])).

tff(c_58527,plain,(
    r1_xboole_0('#skF_6',k2_xboole_0('#skF_8','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_48,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_6',k2_xboole_0('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_50,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_6',k2_xboole_0('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_48])).

tff(c_58543,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58527,c_50])).

tff(c_58544,plain,(
    ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_58543])).

tff(c_58551,plain,(
    k3_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_257,c_58544])).

tff(c_58526,plain,(
    r1_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_58534,plain,(
    r1_xboole_0(k2_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_58526,c_8])).

tff(c_59111,plain,(
    ! [A_722,C_723,B_724] :
      ( r1_xboole_0(A_722,C_723)
      | ~ r1_xboole_0(B_724,C_723)
      | ~ r1_tarski(A_722,B_724) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_63698,plain,(
    ! [A_825] :
      ( r1_xboole_0(A_825,'#skF_3')
      | ~ r1_tarski(A_825,k2_xboole_0('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_58534,c_59111])).

tff(c_63749,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_63698])).

tff(c_63766,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_63749,c_4])).

tff(c_63773,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58551,c_63766])).

tff(c_63774,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_58543])).

tff(c_63782,plain,(
    k3_xboole_0('#skF_5','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_257,c_63774])).

tff(c_64264,plain,(
    ! [A_841,C_842,B_843] :
      ( r1_xboole_0(A_841,C_842)
      | ~ r1_xboole_0(B_843,C_842)
      | ~ r1_tarski(A_841,B_843) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_69802,plain,(
    ! [A_958] :
      ( r1_xboole_0(A_958,'#skF_3')
      | ~ r1_tarski(A_958,k2_xboole_0('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_58534,c_64264])).

tff(c_69852,plain,(
    r1_xboole_0('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_79,c_69802])).

tff(c_69861,plain,(
    k3_xboole_0('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_69852,c_4])).

tff(c_69868,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63782,c_69861])).

tff(c_69870,plain,(
    ~ r1_xboole_0('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_40,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_xboole_0('#skF_3','#skF_4')
    | r1_xboole_0('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_70045,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_69870,c_40])).

tff(c_70046,plain,(
    ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_70045])).

tff(c_70053,plain,(
    k3_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_69901,c_70046])).

tff(c_69869,plain,(
    r1_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_69877,plain,(
    r1_xboole_0(k2_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_69869,c_8])).

tff(c_70669,plain,(
    ! [A_990,C_991,B_992] :
      ( r1_xboole_0(A_990,C_991)
      | ~ r1_xboole_0(B_992,C_991)
      | ~ r1_tarski(A_990,B_992) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_72251,plain,(
    ! [A_1037] :
      ( r1_xboole_0(A_1037,'#skF_3')
      | ~ r1_tarski(A_1037,k2_xboole_0('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_69877,c_70669])).

tff(c_72291,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_72251])).

tff(c_72308,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_72291,c_4])).

tff(c_72315,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70053,c_72308])).

tff(c_72316,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_70045])).

tff(c_72324,plain,(
    k3_xboole_0('#skF_5','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_69901,c_72316])).

tff(c_72888,plain,(
    ! [A_1056,C_1057,B_1058] :
      ( r1_xboole_0(A_1056,C_1057)
      | ~ r1_xboole_0(B_1058,C_1057)
      | ~ r1_tarski(A_1056,B_1058) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_74140,plain,(
    ! [A_1093] :
      ( r1_xboole_0(A_1093,'#skF_3')
      | ~ r1_tarski(A_1093,k2_xboole_0('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_69877,c_72888])).

tff(c_74179,plain,(
    r1_xboole_0('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_79,c_74140])).

tff(c_74188,plain,(
    k3_xboole_0('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_74179,c_4])).

tff(c_74195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72324,c_74188])).

tff(c_74197,plain,(
    ~ r1_xboole_0('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_44,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_xboole_0('#skF_3','#skF_4')
    | r1_xboole_0('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_74346,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_74197,c_44])).

tff(c_74347,plain,(
    ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_74346])).

tff(c_74364,plain,(
    k3_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_74352,c_74347])).

tff(c_74196,plain,(
    r1_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_74204,plain,(
    r1_xboole_0(k2_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_74196,c_8])).

tff(c_75231,plain,(
    ! [A_1140,C_1141,B_1142] :
      ( r1_xboole_0(A_1140,C_1141)
      | ~ r1_xboole_0(B_1142,C_1141)
      | ~ r1_tarski(A_1140,B_1142) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_75545,plain,(
    ! [A_1156] :
      ( r1_xboole_0(A_1156,'#skF_3')
      | ~ r1_tarski(A_1156,k2_xboole_0('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_74204,c_75231])).

tff(c_75580,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_75545])).

tff(c_75597,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_75580,c_4])).

tff(c_75604,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74364,c_75597])).

tff(c_75605,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_74346])).

tff(c_76380,plain,(
    ! [A_1181,C_1182,B_1183] :
      ( r1_xboole_0(A_1181,C_1182)
      | ~ r1_xboole_0(B_1183,C_1182)
      | ~ r1_tarski(A_1181,B_1183) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_76876,plain,(
    ! [A_1201] :
      ( r1_xboole_0(A_1201,'#skF_3')
      | ~ r1_tarski(A_1201,k2_xboole_0('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_74204,c_76380])).

tff(c_76910,plain,(
    r1_xboole_0('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_79,c_76876])).

tff(c_76921,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_76910,c_8])).

tff(c_76927,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75605,c_76921])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:10:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.99/10.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.99/10.26  
% 17.99/10.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.99/10.26  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_1
% 17.99/10.26  
% 17.99/10.26  %Foreground sorts:
% 17.99/10.26  
% 17.99/10.26  
% 17.99/10.26  %Background operators:
% 17.99/10.26  
% 17.99/10.26  
% 17.99/10.26  %Foreground operators:
% 17.99/10.26  tff('#skF_2', type, '#skF_2': $i > $i).
% 17.99/10.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.99/10.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.99/10.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 17.99/10.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.99/10.26  tff('#skF_7', type, '#skF_7': $i).
% 17.99/10.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.99/10.26  tff('#skF_5', type, '#skF_5': $i).
% 17.99/10.26  tff('#skF_6', type, '#skF_6': $i).
% 17.99/10.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 17.99/10.26  tff('#skF_3', type, '#skF_3': $i).
% 17.99/10.26  tff('#skF_8', type, '#skF_8': $i).
% 17.99/10.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.99/10.26  tff('#skF_4', type, '#skF_4': $i).
% 17.99/10.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.99/10.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 17.99/10.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 17.99/10.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 17.99/10.26  
% 18.17/10.29  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 18.17/10.29  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 18.17/10.29  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 18.17/10.29  tff(f_100, negated_conjecture, ~(![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 18.17/10.29  tff(f_75, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 18.17/10.29  tff(f_67, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 18.17/10.29  tff(f_69, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 18.17/10.29  tff(f_71, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 18.17/10.29  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 18.17/10.29  tff(f_83, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 18.17/10.29  tff(f_61, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 18.17/10.29  tff(f_65, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 18.17/10.29  tff(f_73, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 18.17/10.29  tff(f_81, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 18.17/10.29  tff(c_74222, plain, (![A_1096, B_1097]: (r1_xboole_0(A_1096, B_1097) | k3_xboole_0(A_1096, B_1097)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.17/10.29  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 18.17/10.29  tff(c_74352, plain, (![B_1109, A_1110]: (r1_xboole_0(B_1109, A_1110) | k3_xboole_0(A_1110, B_1109)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_74222, c_8])).
% 18.17/10.29  tff(c_69890, plain, (![A_959, B_960]: (r1_xboole_0(A_959, B_960) | k3_xboole_0(A_959, B_960)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.17/10.29  tff(c_69901, plain, (![B_960, A_959]: (r1_xboole_0(B_960, A_959) | k3_xboole_0(A_959, B_960)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_69890, c_8])).
% 18.17/10.29  tff(c_250, plain, (![A_56, B_57]: (r1_xboole_0(A_56, B_57) | k3_xboole_0(A_56, B_57)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.17/10.29  tff(c_257, plain, (![B_57, A_56]: (r1_xboole_0(B_57, A_56) | k3_xboole_0(A_56, B_57)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_250, c_8])).
% 18.17/10.29  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 18.17/10.29  tff(c_46, plain, (r1_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5')) | ~r1_xboole_0('#skF_6', k2_xboole_0('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 18.17/10.29  tff(c_49, plain, (r1_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5')) | ~r1_xboole_0('#skF_6', k2_xboole_0('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_46])).
% 18.17/10.29  tff(c_570, plain, (~r1_xboole_0('#skF_6', k2_xboole_0('#skF_8', '#skF_7'))), inference(splitLeft, [status(thm)], [c_49])).
% 18.17/10.29  tff(c_577, plain, (k3_xboole_0(k2_xboole_0('#skF_8', '#skF_7'), '#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_257, c_570])).
% 18.17/10.29  tff(c_38, plain, (r1_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5')) | r1_xboole_0('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_100])).
% 18.17/10.29  tff(c_225, plain, (r1_xboole_0('#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_38])).
% 18.17/10.29  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.17/10.29  tff(c_231, plain, (k3_xboole_0('#skF_6', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_225, c_4])).
% 18.17/10.29  tff(c_899, plain, (![A_86, B_87]: (k2_xboole_0(k3_xboole_0(A_86, B_87), k4_xboole_0(A_86, B_87))=A_86)), inference(cnfTransformation, [status(thm)], [f_75])).
% 18.17/10.29  tff(c_962, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_6', '#skF_8'))='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_231, c_899])).
% 18.17/10.29  tff(c_24, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_67])).
% 18.17/10.29  tff(c_267, plain, (![A_60, B_61]: (k4_xboole_0(k2_xboole_0(A_60, B_61), B_61)=k4_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_69])).
% 18.17/10.29  tff(c_274, plain, (![A_60]: (k4_xboole_0(A_60, k1_xboole_0)=k2_xboole_0(A_60, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_267, c_24])).
% 18.17/10.29  tff(c_293, plain, (![A_62]: (k2_xboole_0(A_62, k1_xboole_0)=A_62)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_274])).
% 18.17/10.29  tff(c_311, plain, (![A_62]: (k2_xboole_0(k1_xboole_0, A_62)=A_62)), inference(superposition, [status(thm), theory('equality')], [c_293, c_2])).
% 18.17/10.29  tff(c_1159, plain, (k4_xboole_0('#skF_6', '#skF_8')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_962, c_311])).
% 18.17/10.29  tff(c_42, plain, (r1_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5')) | r1_xboole_0('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_100])).
% 18.17/10.29  tff(c_114, plain, (r1_xboole_0('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_42])).
% 18.17/10.29  tff(c_120, plain, (k3_xboole_0('#skF_6', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_114, c_4])).
% 18.17/10.29  tff(c_977, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_6', '#skF_7'))='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_120, c_899])).
% 18.17/10.29  tff(c_1235, plain, (k4_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_977, c_311])).
% 18.17/10.29  tff(c_1468, plain, (![A_105, B_106, C_107]: (k4_xboole_0(k4_xboole_0(A_105, B_106), C_107)=k4_xboole_0(A_105, k2_xboole_0(B_106, C_107)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 18.17/10.29  tff(c_57091, plain, (![C_703]: (k4_xboole_0('#skF_6', k2_xboole_0('#skF_7', C_703))=k4_xboole_0('#skF_6', C_703))), inference(superposition, [status(thm), theory('equality')], [c_1235, c_1468])).
% 18.17/10.29  tff(c_397, plain, (![A_65, B_66, C_67]: (~r1_xboole_0(A_65, B_66) | ~r2_hidden(C_67, k3_xboole_0(A_65, B_66)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 18.17/10.29  tff(c_403, plain, (![C_67]: (~r1_xboole_0('#skF_6', '#skF_8') | ~r2_hidden(C_67, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_231, c_397])).
% 18.17/10.29  tff(c_417, plain, (![C_67]: (~r2_hidden(C_67, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_225, c_403])).
% 18.17/10.29  tff(c_64, plain, (![B_41, A_42]: (k2_xboole_0(B_41, A_42)=k2_xboole_0(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_27])).
% 18.17/10.29  tff(c_36, plain, (![A_32, B_33]: (r1_tarski(A_32, k2_xboole_0(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 18.17/10.29  tff(c_79, plain, (![A_42, B_41]: (r1_tarski(A_42, k2_xboole_0(B_41, A_42)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_36])).
% 18.17/10.29  tff(c_139, plain, (![A_49, B_50]: (k4_xboole_0(A_49, B_50)=k1_xboole_0 | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_61])).
% 18.17/10.29  tff(c_153, plain, (![A_42, B_41]: (k4_xboole_0(A_42, k2_xboole_0(B_41, A_42))=k1_xboole_0)), inference(resolution, [status(thm)], [c_79, c_139])).
% 18.17/10.29  tff(c_22, plain, (![A_17, B_18]: (k2_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 18.17/10.29  tff(c_1503, plain, (![C_107, A_105, B_106]: (k2_xboole_0(C_107, k4_xboole_0(A_105, k2_xboole_0(B_106, C_107)))=k2_xboole_0(C_107, k4_xboole_0(A_105, B_106)))), inference(superposition, [status(thm), theory('equality')], [c_1468, c_22])).
% 18.17/10.29  tff(c_28, plain, (![A_22, B_23, C_24]: (k4_xboole_0(k4_xboole_0(A_22, B_23), C_24)=k4_xboole_0(A_22, k2_xboole_0(B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 18.17/10.29  tff(c_30, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k4_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_73])).
% 18.17/10.29  tff(c_1547, plain, (![A_105, B_106, B_26]: (k4_xboole_0(A_105, k2_xboole_0(B_106, k4_xboole_0(k4_xboole_0(A_105, B_106), B_26)))=k3_xboole_0(k4_xboole_0(A_105, B_106), B_26))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1468])).
% 18.17/10.29  tff(c_10975, plain, (![A_259, B_260, B_261]: (k4_xboole_0(A_259, k2_xboole_0(B_260, k4_xboole_0(A_259, k2_xboole_0(B_260, B_261))))=k3_xboole_0(k4_xboole_0(A_259, B_260), B_261))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1547])).
% 18.17/10.29  tff(c_11178, plain, (![A_105, B_106]: (k4_xboole_0(A_105, k2_xboole_0(B_106, k4_xboole_0(A_105, B_106)))=k3_xboole_0(k4_xboole_0(A_105, B_106), B_106))), inference(superposition, [status(thm), theory('equality')], [c_1503, c_10975])).
% 18.17/10.29  tff(c_11323, plain, (![A_262, B_263]: (k3_xboole_0(k4_xboole_0(A_262, B_263), B_263)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_153, c_22, c_11178])).
% 18.17/10.29  tff(c_10, plain, (![A_7, B_8]: (r2_hidden('#skF_1'(A_7, B_8), k3_xboole_0(A_7, B_8)) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 18.17/10.29  tff(c_11373, plain, (![A_262, B_263]: (r2_hidden('#skF_1'(k4_xboole_0(A_262, B_263), B_263), k1_xboole_0) | r1_xboole_0(k4_xboole_0(A_262, B_263), B_263))), inference(superposition, [status(thm), theory('equality')], [c_11323, c_10])).
% 18.17/10.29  tff(c_11527, plain, (![A_264, B_265]: (r1_xboole_0(k4_xboole_0(A_264, B_265), B_265))), inference(negUnitSimplification, [status(thm)], [c_417, c_11373])).
% 18.17/10.29  tff(c_11610, plain, (![B_265, A_264]: (r1_xboole_0(B_265, k4_xboole_0(A_264, B_265)))), inference(resolution, [status(thm)], [c_11527, c_8])).
% 18.17/10.29  tff(c_58336, plain, (![C_706]: (r1_xboole_0(k2_xboole_0('#skF_7', C_706), k4_xboole_0('#skF_6', C_706)))), inference(superposition, [status(thm), theory('equality')], [c_57091, c_11610])).
% 18.17/10.29  tff(c_58450, plain, (r1_xboole_0(k2_xboole_0('#skF_7', '#skF_8'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1159, c_58336])).
% 18.17/10.29  tff(c_58502, plain, (r1_xboole_0(k2_xboole_0('#skF_8', '#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_58450])).
% 18.17/10.29  tff(c_58512, plain, (k3_xboole_0(k2_xboole_0('#skF_8', '#skF_7'), '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_58502, c_4])).
% 18.17/10.29  tff(c_58525, plain, $false, inference(negUnitSimplification, [status(thm)], [c_577, c_58512])).
% 18.17/10.29  tff(c_58527, plain, (r1_xboole_0('#skF_6', k2_xboole_0('#skF_8', '#skF_7'))), inference(splitRight, [status(thm)], [c_49])).
% 18.17/10.29  tff(c_48, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_6', k2_xboole_0('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 18.17/10.29  tff(c_50, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_6', k2_xboole_0('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_48])).
% 18.17/10.29  tff(c_58543, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r1_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58527, c_50])).
% 18.17/10.29  tff(c_58544, plain, (~r1_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_58543])).
% 18.17/10.29  tff(c_58551, plain, (k3_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_257, c_58544])).
% 18.17/10.29  tff(c_58526, plain, (r1_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_49])).
% 18.17/10.29  tff(c_58534, plain, (r1_xboole_0(k2_xboole_0('#skF_4', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_58526, c_8])).
% 18.17/10.29  tff(c_59111, plain, (![A_722, C_723, B_724]: (r1_xboole_0(A_722, C_723) | ~r1_xboole_0(B_724, C_723) | ~r1_tarski(A_722, B_724))), inference(cnfTransformation, [status(thm)], [f_81])).
% 18.17/10.29  tff(c_63698, plain, (![A_825]: (r1_xboole_0(A_825, '#skF_3') | ~r1_tarski(A_825, k2_xboole_0('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_58534, c_59111])).
% 18.17/10.29  tff(c_63749, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_63698])).
% 18.17/10.29  tff(c_63766, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_63749, c_4])).
% 18.17/10.29  tff(c_63773, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58551, c_63766])).
% 18.17/10.29  tff(c_63774, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_58543])).
% 18.17/10.29  tff(c_63782, plain, (k3_xboole_0('#skF_5', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_257, c_63774])).
% 18.17/10.29  tff(c_64264, plain, (![A_841, C_842, B_843]: (r1_xboole_0(A_841, C_842) | ~r1_xboole_0(B_843, C_842) | ~r1_tarski(A_841, B_843))), inference(cnfTransformation, [status(thm)], [f_81])).
% 18.17/10.29  tff(c_69802, plain, (![A_958]: (r1_xboole_0(A_958, '#skF_3') | ~r1_tarski(A_958, k2_xboole_0('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_58534, c_64264])).
% 18.17/10.29  tff(c_69852, plain, (r1_xboole_0('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_79, c_69802])).
% 18.17/10.29  tff(c_69861, plain, (k3_xboole_0('#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_69852, c_4])).
% 18.17/10.29  tff(c_69868, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63782, c_69861])).
% 18.17/10.29  tff(c_69870, plain, (~r1_xboole_0('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_38])).
% 18.17/10.29  tff(c_40, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r1_xboole_0('#skF_3', '#skF_4') | r1_xboole_0('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_100])).
% 18.17/10.29  tff(c_70045, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r1_xboole_0('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_69870, c_40])).
% 18.17/10.29  tff(c_70046, plain, (~r1_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_70045])).
% 18.17/10.29  tff(c_70053, plain, (k3_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_69901, c_70046])).
% 18.17/10.29  tff(c_69869, plain, (r1_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_38])).
% 18.17/10.29  tff(c_69877, plain, (r1_xboole_0(k2_xboole_0('#skF_4', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_69869, c_8])).
% 18.17/10.29  tff(c_70669, plain, (![A_990, C_991, B_992]: (r1_xboole_0(A_990, C_991) | ~r1_xboole_0(B_992, C_991) | ~r1_tarski(A_990, B_992))), inference(cnfTransformation, [status(thm)], [f_81])).
% 18.17/10.29  tff(c_72251, plain, (![A_1037]: (r1_xboole_0(A_1037, '#skF_3') | ~r1_tarski(A_1037, k2_xboole_0('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_69877, c_70669])).
% 18.17/10.29  tff(c_72291, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_72251])).
% 18.17/10.29  tff(c_72308, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_72291, c_4])).
% 18.17/10.29  tff(c_72315, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70053, c_72308])).
% 18.17/10.29  tff(c_72316, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_70045])).
% 18.17/10.29  tff(c_72324, plain, (k3_xboole_0('#skF_5', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_69901, c_72316])).
% 18.17/10.29  tff(c_72888, plain, (![A_1056, C_1057, B_1058]: (r1_xboole_0(A_1056, C_1057) | ~r1_xboole_0(B_1058, C_1057) | ~r1_tarski(A_1056, B_1058))), inference(cnfTransformation, [status(thm)], [f_81])).
% 18.17/10.29  tff(c_74140, plain, (![A_1093]: (r1_xboole_0(A_1093, '#skF_3') | ~r1_tarski(A_1093, k2_xboole_0('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_69877, c_72888])).
% 18.17/10.29  tff(c_74179, plain, (r1_xboole_0('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_79, c_74140])).
% 18.17/10.29  tff(c_74188, plain, (k3_xboole_0('#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_74179, c_4])).
% 18.17/10.29  tff(c_74195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72324, c_74188])).
% 18.17/10.29  tff(c_74197, plain, (~r1_xboole_0('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_42])).
% 18.17/10.29  tff(c_44, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r1_xboole_0('#skF_3', '#skF_4') | r1_xboole_0('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_100])).
% 18.17/10.29  tff(c_74346, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r1_xboole_0('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_74197, c_44])).
% 18.17/10.29  tff(c_74347, plain, (~r1_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_74346])).
% 18.17/10.29  tff(c_74364, plain, (k3_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_74352, c_74347])).
% 18.17/10.29  tff(c_74196, plain, (r1_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_42])).
% 18.17/10.29  tff(c_74204, plain, (r1_xboole_0(k2_xboole_0('#skF_4', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_74196, c_8])).
% 18.17/10.29  tff(c_75231, plain, (![A_1140, C_1141, B_1142]: (r1_xboole_0(A_1140, C_1141) | ~r1_xboole_0(B_1142, C_1141) | ~r1_tarski(A_1140, B_1142))), inference(cnfTransformation, [status(thm)], [f_81])).
% 18.17/10.29  tff(c_75545, plain, (![A_1156]: (r1_xboole_0(A_1156, '#skF_3') | ~r1_tarski(A_1156, k2_xboole_0('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_74204, c_75231])).
% 18.17/10.29  tff(c_75580, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_75545])).
% 18.17/10.29  tff(c_75597, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_75580, c_4])).
% 18.17/10.29  tff(c_75604, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74364, c_75597])).
% 18.17/10.29  tff(c_75605, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_74346])).
% 18.17/10.29  tff(c_76380, plain, (![A_1181, C_1182, B_1183]: (r1_xboole_0(A_1181, C_1182) | ~r1_xboole_0(B_1183, C_1182) | ~r1_tarski(A_1181, B_1183))), inference(cnfTransformation, [status(thm)], [f_81])).
% 18.17/10.29  tff(c_76876, plain, (![A_1201]: (r1_xboole_0(A_1201, '#skF_3') | ~r1_tarski(A_1201, k2_xboole_0('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_74204, c_76380])).
% 18.17/10.29  tff(c_76910, plain, (r1_xboole_0('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_79, c_76876])).
% 18.17/10.29  tff(c_76921, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_76910, c_8])).
% 18.17/10.29  tff(c_76927, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75605, c_76921])).
% 18.17/10.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.17/10.29  
% 18.17/10.29  Inference rules
% 18.17/10.29  ----------------------
% 18.17/10.29  #Ref     : 1
% 18.17/10.29  #Sup     : 19710
% 18.17/10.29  #Fact    : 0
% 18.17/10.29  #Define  : 0
% 18.17/10.29  #Split   : 23
% 18.17/10.29  #Chain   : 0
% 18.17/10.29  #Close   : 0
% 18.17/10.29  
% 18.17/10.29  Ordering : KBO
% 18.17/10.29  
% 18.17/10.29  Simplification rules
% 18.17/10.29  ----------------------
% 18.17/10.29  #Subsume      : 2576
% 18.17/10.29  #Demod        : 17546
% 18.17/10.29  #Tautology    : 11991
% 18.17/10.29  #SimpNegUnit  : 275
% 18.17/10.29  #BackRed      : 30
% 18.17/10.29  
% 18.17/10.29  #Partial instantiations: 0
% 18.17/10.29  #Strategies tried      : 1
% 18.17/10.29  
% 18.17/10.29  Timing (in seconds)
% 18.17/10.29  ----------------------
% 18.17/10.29  Preprocessing        : 0.32
% 18.17/10.29  Parsing              : 0.17
% 18.17/10.29  CNF conversion       : 0.02
% 18.17/10.29  Main loop            : 9.12
% 18.17/10.29  Inferencing          : 1.34
% 18.17/10.29  Reduction            : 5.44
% 18.17/10.29  Demodulation         : 4.70
% 18.17/10.29  BG Simplification    : 0.14
% 18.17/10.29  Subsumption          : 1.74
% 18.17/10.29  Abstraction          : 0.24
% 18.17/10.29  MUC search           : 0.00
% 18.17/10.29  Cooper               : 0.00
% 18.17/10.29  Total                : 9.49
% 18.17/10.29  Index Insertion      : 0.00
% 18.17/10.29  Index Deletion       : 0.00
% 18.17/10.29  Index Matching       : 0.00
% 18.17/10.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
