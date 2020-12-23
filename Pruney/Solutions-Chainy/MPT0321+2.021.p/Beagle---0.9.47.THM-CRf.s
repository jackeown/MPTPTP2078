%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:16 EST 2020

% Result     : Theorem 41.79s
% Output     : CNFRefutation 41.99s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 588 expanded)
%              Number of leaves         :   42 ( 214 expanded)
%              Depth                    :   18
%              Number of atoms          :  232 ( 979 expanded)
%              Number of equality atoms :  157 ( 671 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_147,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_136,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k4_xboole_0(A,B),C) = k4_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k4_xboole_0(A,B)) = k4_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

tff(f_119,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_99,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_95,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_101,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_97,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_132,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_83,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_93,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k4_xboole_0(B,A)
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

tff(f_130,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
          | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
        & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(c_82,plain,
    ( '#skF_7' != '#skF_9'
    | '#skF_6' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_89,plain,(
    '#skF_6' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_84,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_80,plain,(
    ! [C_59,A_57,B_58] : k4_xboole_0(k2_zfmisc_1(C_59,A_57),k2_zfmisc_1(C_59,B_58)) = k2_zfmisc_1(C_59,k4_xboole_0(A_57,B_58)) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_88,plain,(
    k2_zfmisc_1('#skF_6','#skF_7') = k2_zfmisc_1('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_1930,plain,(
    ! [A_183,C_184,B_185] : k4_xboole_0(k2_zfmisc_1(A_183,C_184),k2_zfmisc_1(B_185,C_184)) = k2_zfmisc_1(k4_xboole_0(A_183,B_185),C_184) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_4813,plain,(
    ! [B_280] : k4_xboole_0(k2_zfmisc_1('#skF_8','#skF_9'),k2_zfmisc_1(B_280,'#skF_7')) = k2_zfmisc_1(k4_xboole_0('#skF_6',B_280),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_1930])).

tff(c_4909,plain,(
    k2_zfmisc_1(k4_xboole_0('#skF_6','#skF_8'),'#skF_7') = k2_zfmisc_1('#skF_8',k4_xboole_0('#skF_9','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_4813])).

tff(c_66,plain,(
    ! [B_49,A_48] :
      ( k1_xboole_0 = B_49
      | k1_xboole_0 = A_48
      | k2_zfmisc_1(A_48,B_49) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_11582,plain,
    ( k1_xboole_0 = '#skF_7'
    | k4_xboole_0('#skF_6','#skF_8') = k1_xboole_0
    | k2_zfmisc_1('#skF_8',k4_xboole_0('#skF_9','#skF_7')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4909,c_66])).

tff(c_11615,plain,
    ( k4_xboole_0('#skF_6','#skF_8') = k1_xboole_0
    | k2_zfmisc_1('#skF_8',k4_xboole_0('#skF_9','#skF_7')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_11582])).

tff(c_12119,plain,(
    k2_zfmisc_1('#skF_8',k4_xboole_0('#skF_9','#skF_7')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_11615])).

tff(c_50,plain,(
    ! [A_33,B_34,C_35] : k4_xboole_0(k4_xboole_0(A_33,B_34),C_35) = k4_xboole_0(A_33,k2_xboole_0(B_34,C_35)) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1324,plain,(
    ! [A_154,B_155,C_156] : k4_xboole_0(k4_xboole_0(A_154,B_155),C_156) = k4_xboole_0(A_154,k2_xboole_0(B_155,C_156)) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1375,plain,(
    ! [A_33,B_34,C_35,C_156] : k4_xboole_0(k4_xboole_0(A_33,k2_xboole_0(B_34,C_35)),C_156) = k4_xboole_0(k4_xboole_0(A_33,B_34),k2_xboole_0(C_35,C_156)) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_1324])).

tff(c_27481,plain,(
    ! [A_637,B_638,C_639,C_640] : k4_xboole_0(A_637,k2_xboole_0(k2_xboole_0(B_638,C_639),C_640)) = k4_xboole_0(A_637,k2_xboole_0(B_638,k2_xboole_0(C_639,C_640))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_1375])).

tff(c_46,plain,(
    ! [A_30,B_31] : r1_tarski(k4_xboole_0(A_30,B_31),A_30) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_275,plain,(
    ! [A_83,B_84] :
      ( k4_xboole_0(A_83,B_84) = k1_xboole_0
      | ~ r1_tarski(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_287,plain,(
    ! [A_30,B_31] : k4_xboole_0(k4_xboole_0(A_30,B_31),A_30) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_275])).

tff(c_1365,plain,(
    ! [C_156,B_155] : k4_xboole_0(C_156,k2_xboole_0(B_155,C_156)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1324,c_287])).

tff(c_38944,plain,(
    ! [C_736,B_737,C_738] : k4_xboole_0(C_736,k2_xboole_0(B_737,k2_xboole_0(C_738,C_736))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_27481,c_1365])).

tff(c_52,plain,(
    ! [A_36,B_37] : k4_xboole_0(A_36,k4_xboole_0(A_36,B_37)) = k3_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_252,plain,(
    ! [A_75,B_76] :
      ( r1_xboole_0(A_75,B_76)
      | k4_xboole_0(A_75,B_76) != A_75 ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_24,plain,(
    ! [B_12,A_11] :
      ( r1_xboole_0(B_12,A_11)
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_368,plain,(
    ! [B_91,A_92] :
      ( r1_xboole_0(B_91,A_92)
      | k4_xboole_0(A_92,B_91) != A_92 ) ),
    inference(resolution,[status(thm)],[c_252,c_24])).

tff(c_56,plain,(
    ! [A_39,B_40] :
      ( k4_xboole_0(A_39,B_40) = A_39
      | ~ r1_xboole_0(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_3344,plain,(
    ! [B_250,A_251] :
      ( k4_xboole_0(B_250,A_251) = B_250
      | k4_xboole_0(A_251,B_250) != A_251 ) ),
    inference(resolution,[status(thm)],[c_368,c_56])).

tff(c_3372,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(A_30,k4_xboole_0(A_30,B_31)) = A_30
      | k4_xboole_0(A_30,B_31) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_3344])).

tff(c_3381,plain,(
    ! [A_30,B_31] :
      ( k3_xboole_0(A_30,B_31) = A_30
      | k4_xboole_0(A_30,B_31) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3372])).

tff(c_39429,plain,(
    ! [C_736,B_737,C_738] : k3_xboole_0(C_736,k2_xboole_0(B_737,k2_xboole_0(C_738,C_736))) = C_736 ),
    inference(superposition,[status(thm),theory(equality)],[c_38944,c_3381])).

tff(c_48,plain,(
    ! [A_32] : k4_xboole_0(A_32,k1_xboole_0) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_158,plain,(
    ! [A_66,B_67] : r1_tarski(k4_xboole_0(A_66,B_67),A_66) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_161,plain,(
    ! [A_32] : r1_tarski(A_32,A_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_158])).

tff(c_286,plain,(
    ! [A_32] : k4_xboole_0(A_32,A_32) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_161,c_275])).

tff(c_30,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_3'(A_13,B_14),A_13)
      | r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_255,plain,(
    ! [B_76,A_75] :
      ( r1_xboole_0(B_76,A_75)
      | k4_xboole_0(A_75,B_76) != A_75 ) ),
    inference(resolution,[status(thm)],[c_252,c_24])).

tff(c_441,plain,(
    ! [A_104,B_105] : k4_xboole_0(A_104,k4_xboole_0(A_104,B_105)) = k3_xboole_0(A_104,B_105) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_472,plain,(
    ! [A_32] : k4_xboole_0(A_32,k1_xboole_0) = k3_xboole_0(A_32,A_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_441])).

tff(c_491,plain,(
    ! [A_106] : k3_xboole_0(A_106,A_106) = A_106 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_472])).

tff(c_34,plain,(
    ! [A_18,B_19,C_22] :
      ( ~ r1_xboole_0(A_18,B_19)
      | ~ r2_hidden(C_22,k3_xboole_0(A_18,B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_775,plain,(
    ! [A_124,C_125] :
      ( ~ r1_xboole_0(A_124,A_124)
      | ~ r2_hidden(C_125,A_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_491,c_34])).

tff(c_784,plain,(
    ! [C_125,A_75] :
      ( ~ r2_hidden(C_125,A_75)
      | k4_xboole_0(A_75,A_75) != A_75 ) ),
    inference(resolution,[status(thm)],[c_255,c_775])).

tff(c_795,plain,(
    ! [C_126,A_127] :
      ( ~ r2_hidden(C_126,A_127)
      | k1_xboole_0 != A_127 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_784])).

tff(c_851,plain,(
    ! [A_130,B_131] :
      ( k1_xboole_0 != A_130
      | r1_xboole_0(A_130,B_131) ) ),
    inference(resolution,[status(thm)],[c_30,c_795])).

tff(c_861,plain,(
    ! [A_130,B_131] :
      ( k4_xboole_0(A_130,B_131) = A_130
      | k1_xboole_0 != A_130 ) ),
    inference(resolution,[status(thm)],[c_851,c_56])).

tff(c_487,plain,(
    ! [A_32] : k3_xboole_0(A_32,A_32) = A_32 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_472])).

tff(c_76,plain,(
    ! [A_53,C_55,B_54,D_56] : k3_xboole_0(k2_zfmisc_1(A_53,C_55),k2_zfmisc_1(B_54,D_56)) = k2_zfmisc_1(k3_xboole_0(A_53,B_54),k3_xboole_0(C_55,D_56)) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1960,plain,(
    ! [A_183,C_184,B_185] : k4_xboole_0(k2_zfmisc_1(A_183,C_184),k2_zfmisc_1(k4_xboole_0(A_183,B_185),C_184)) = k3_xboole_0(k2_zfmisc_1(A_183,C_184),k2_zfmisc_1(B_185,C_184)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1930,c_52])).

tff(c_39454,plain,(
    ! [A_739,C_740,B_741] : k4_xboole_0(k2_zfmisc_1(A_739,C_740),k2_zfmisc_1(k4_xboole_0(A_739,B_741),C_740)) = k2_zfmisc_1(k3_xboole_0(A_739,B_741),C_740) ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_76,c_1960])).

tff(c_39883,plain,(
    ! [A_130,C_740,B_131] :
      ( k4_xboole_0(k2_zfmisc_1(A_130,C_740),k2_zfmisc_1(A_130,C_740)) = k2_zfmisc_1(k3_xboole_0(A_130,B_131),C_740)
      | k1_xboole_0 != A_130 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_861,c_39454])).

tff(c_110359,plain,(
    ! [A_1150,B_1151,C_1152] :
      ( k2_zfmisc_1(k3_xboole_0(A_1150,B_1151),C_1152) = k1_xboole_0
      | k1_xboole_0 != A_1150 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_39883])).

tff(c_110897,plain,(
    ! [C_1153,C_1154] :
      ( k2_zfmisc_1(C_1153,C_1154) = k1_xboole_0
      | k1_xboole_0 != C_1153 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39429,c_110359])).

tff(c_111532,plain,
    ( k2_zfmisc_1('#skF_8',k4_xboole_0('#skF_9','#skF_7')) = k1_xboole_0
    | k4_xboole_0('#skF_6','#skF_8') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4909,c_110897])).

tff(c_111711,plain,(
    k4_xboole_0('#skF_6','#skF_8') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_12119,c_111532])).

tff(c_110895,plain,(
    ! [C_1152] : k2_zfmisc_1(k1_xboole_0,C_1152) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_39429,c_110359])).

tff(c_28,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_3'(A_13,B_14),B_14)
      | r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_752,plain,(
    ! [A_122,B_123] :
      ( r2_hidden('#skF_3'(A_122,B_123),A_122)
      | r1_xboole_0(A_122,B_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_21285,plain,(
    ! [A_561,B_562,B_563] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_561,B_562),B_563),B_562)
      | r1_xboole_0(k4_xboole_0(A_561,B_562),B_563) ) ),
    inference(resolution,[status(thm)],[c_752,c_6])).

tff(c_21433,plain,(
    ! [A_564,B_565] : r1_xboole_0(k4_xboole_0(A_564,B_565),B_565) ),
    inference(resolution,[status(thm)],[c_28,c_21285])).

tff(c_36,plain,(
    ! [A_23] :
      ( r2_hidden('#skF_5'(A_23),A_23)
      | k1_xboole_0 = A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_415,plain,(
    ! [A_100,B_101,C_102] :
      ( ~ r1_xboole_0(A_100,B_101)
      | ~ r2_hidden(C_102,k3_xboole_0(A_100,B_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2283,plain,(
    ! [A_204,B_205,C_206] :
      ( ~ r1_xboole_0(A_204,B_205)
      | ~ r2_hidden(C_206,k3_xboole_0(B_205,A_204)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_415])).

tff(c_2329,plain,(
    ! [A_204,B_205] :
      ( ~ r1_xboole_0(A_204,B_205)
      | k3_xboole_0(B_205,A_204) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_36,c_2283])).

tff(c_21543,plain,(
    ! [B_565,A_564] : k3_xboole_0(B_565,k4_xboole_0(A_564,B_565)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_21433,c_2329])).

tff(c_1998,plain,(
    ! [B_185] : k4_xboole_0(k2_zfmisc_1('#skF_8','#skF_9'),k2_zfmisc_1(B_185,'#skF_7')) = k2_zfmisc_1(k4_xboole_0('#skF_6',B_185),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_1930])).

tff(c_4880,plain,(
    ! [B_280] : k4_xboole_0(k2_zfmisc_1('#skF_8','#skF_9'),k2_zfmisc_1(k4_xboole_0('#skF_6',B_280),'#skF_7')) = k3_xboole_0(k2_zfmisc_1('#skF_8','#skF_9'),k2_zfmisc_1(B_280,'#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4813,c_52])).

tff(c_131153,plain,(
    ! [B_1289] : k2_zfmisc_1(k3_xboole_0('#skF_8',B_1289),k3_xboole_0('#skF_9','#skF_7')) = k2_zfmisc_1(k3_xboole_0('#skF_6',B_1289),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1998,c_76,c_4880])).

tff(c_131397,plain,(
    ! [A_564] : k2_zfmisc_1(k3_xboole_0('#skF_6',k4_xboole_0(A_564,'#skF_8')),'#skF_7') = k2_zfmisc_1(k1_xboole_0,k3_xboole_0('#skF_9','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_21543,c_131153])).

tff(c_131794,plain,(
    ! [A_1292] : k2_zfmisc_1(k3_xboole_0('#skF_6',k4_xboole_0(A_1292,'#skF_8')),'#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_110895,c_131397])).

tff(c_131978,plain,(
    ! [A_1292] :
      ( k1_xboole_0 = '#skF_7'
      | k3_xboole_0('#skF_6',k4_xboole_0(A_1292,'#skF_8')) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131794,c_66])).

tff(c_132191,plain,(
    ! [A_1293] : k3_xboole_0('#skF_6',k4_xboole_0(A_1293,'#skF_8')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_131978])).

tff(c_469,plain,(
    ! [A_30,B_31] : k4_xboole_0(k4_xboole_0(A_30,B_31),k1_xboole_0) = k3_xboole_0(k4_xboole_0(A_30,B_31),A_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_441])).

tff(c_3124,plain,(
    ! [A_243,B_244] : k3_xboole_0(k4_xboole_0(A_243,B_244),A_243) = k4_xboole_0(A_243,B_244) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_469])).

tff(c_3184,plain,(
    ! [A_243,B_244] : k3_xboole_0(A_243,k4_xboole_0(A_243,B_244)) = k4_xboole_0(A_243,B_244) ),
    inference(superposition,[status(thm),theory(equality)],[c_3124,c_2])).

tff(c_132533,plain,(
    k4_xboole_0('#skF_6','#skF_8') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_132191,c_3184])).

tff(c_132815,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111711,c_132533])).

tff(c_132816,plain,(
    k4_xboole_0('#skF_6','#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_11615])).

tff(c_44,plain,(
    ! [B_29,A_28] :
      ( B_29 = A_28
      | k4_xboole_0(B_29,A_28) != k4_xboole_0(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_132898,plain,
    ( '#skF_6' = '#skF_8'
    | k4_xboole_0('#skF_8','#skF_6') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_132816,c_44])).

tff(c_132956,plain,(
    k4_xboole_0('#skF_8','#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_132898])).

tff(c_86,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_376,plain,(
    ! [B_93,A_94] :
      ( k1_xboole_0 = B_93
      | k1_xboole_0 = A_94
      | k2_zfmisc_1(A_94,B_93) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_382,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_376])).

tff(c_388,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_84,c_382])).

tff(c_132817,plain,(
    k2_zfmisc_1('#skF_8',k4_xboole_0('#skF_9','#skF_7')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_11615])).

tff(c_133618,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') = k1_xboole_0
    | k1_xboole_0 != '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_861,c_132817])).

tff(c_133649,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_388,c_133618])).

tff(c_2036,plain,(
    ! [C_187,A_188,B_189] : k4_xboole_0(k2_zfmisc_1(C_187,A_188),k2_zfmisc_1(C_187,B_189)) = k2_zfmisc_1(C_187,k4_xboole_0(A_188,B_189)) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_2905,plain,(
    ! [B_240] : k4_xboole_0(k2_zfmisc_1('#skF_8','#skF_9'),k2_zfmisc_1('#skF_6',B_240)) = k2_zfmisc_1('#skF_6',k4_xboole_0('#skF_7',B_240)) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_2036])).

tff(c_78,plain,(
    ! [A_57,C_59,B_58] : k4_xboole_0(k2_zfmisc_1(A_57,C_59),k2_zfmisc_1(B_58,C_59)) = k2_zfmisc_1(k4_xboole_0(A_57,B_58),C_59) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_2912,plain,(
    k2_zfmisc_1(k4_xboole_0('#skF_8','#skF_6'),'#skF_9') = k2_zfmisc_1('#skF_6',k4_xboole_0('#skF_7','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2905,c_78])).

tff(c_172204,plain,
    ( k1_xboole_0 = '#skF_9'
    | k4_xboole_0('#skF_8','#skF_6') = k1_xboole_0
    | k2_zfmisc_1('#skF_6',k4_xboole_0('#skF_7','#skF_9')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2912,c_66])).

tff(c_172244,plain,(
    k2_zfmisc_1('#skF_6',k4_xboole_0('#skF_7','#skF_9')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_132956,c_133649,c_172204])).

tff(c_132945,plain,(
    k3_xboole_0('#skF_6','#skF_8') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_132816,c_3381])).

tff(c_133122,plain,(
    k3_xboole_0('#skF_8','#skF_6') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_132945])).

tff(c_648,plain,(
    ! [A_116,B_117] :
      ( r2_hidden('#skF_3'(A_116,B_117),B_117)
      | r1_xboole_0(A_116,B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_136280,plain,(
    ! [A_1322,A_1323,B_1324] :
      ( ~ r2_hidden('#skF_3'(A_1322,k4_xboole_0(A_1323,B_1324)),B_1324)
      | r1_xboole_0(A_1322,k4_xboole_0(A_1323,B_1324)) ) ),
    inference(resolution,[status(thm)],[c_648,c_6])).

tff(c_136441,plain,(
    ! [A_1325,A_1326] : r1_xboole_0(A_1325,k4_xboole_0(A_1326,A_1325)) ),
    inference(resolution,[status(thm)],[c_30,c_136280])).

tff(c_136563,plain,(
    ! [A_1325,A_1326] : k4_xboole_0(A_1325,k4_xboole_0(A_1326,A_1325)) = A_1325 ),
    inference(resolution,[status(thm)],[c_136441,c_56])).

tff(c_3424,plain,(
    ! [A_254] : k4_xboole_0(k2_zfmisc_1(A_254,'#skF_7'),k2_zfmisc_1('#skF_8','#skF_9')) = k2_zfmisc_1(k4_xboole_0(A_254,'#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_1930])).

tff(c_3488,plain,(
    k2_zfmisc_1(k4_xboole_0('#skF_8','#skF_6'),'#skF_7') = k2_zfmisc_1('#skF_8',k4_xboole_0('#skF_7','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_3424])).

tff(c_136732,plain,(
    ! [A_1329,A_1330] : k3_xboole_0(k4_xboole_0(A_1329,A_1330),A_1330) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_136441,c_2329])).

tff(c_180332,plain,(
    ! [B_1763] : k3_xboole_0(k2_zfmisc_1(k4_xboole_0('#skF_6',B_1763),'#skF_7'),k2_zfmisc_1(B_1763,'#skF_7')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1998,c_136732])).

tff(c_180556,plain,(
    k3_xboole_0(k2_zfmisc_1(k4_xboole_0('#skF_6',k4_xboole_0('#skF_8','#skF_6')),'#skF_7'),k2_zfmisc_1('#skF_8',k4_xboole_0('#skF_7','#skF_9'))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3488,c_180332])).

tff(c_180741,plain,(
    k2_zfmisc_1('#skF_6',k4_xboole_0('#skF_7','#skF_9')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_133122,c_2,c_3184,c_76,c_136563,c_180556])).

tff(c_180743,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_172244,c_180741])).

tff(c_180744,plain,(
    '#skF_7' != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_180745,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_180746,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_180745,c_86])).

tff(c_70,plain,(
    ! [B_49] : k2_zfmisc_1(k1_xboole_0,B_49) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_180820,plain,(
    ! [A_1770,B_1771] : r1_tarski(k4_xboole_0(A_1770,B_1771),A_1770) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_180826,plain,(
    ! [A_32] : r1_tarski(A_32,A_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_180820])).

tff(c_180937,plain,(
    ! [A_1787,B_1788] :
      ( k4_xboole_0(A_1787,B_1788) = k1_xboole_0
      | ~ r1_tarski(A_1787,B_1788) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_180948,plain,(
    ! [A_32] : k4_xboole_0(A_32,A_32) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_180826,c_180937])).

tff(c_182662,plain,(
    ! [C_1887,A_1888,B_1889] : k4_xboole_0(k2_zfmisc_1(C_1887,A_1888),k2_zfmisc_1(C_1887,B_1889)) = k2_zfmisc_1(C_1887,k4_xboole_0(A_1888,B_1889)) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_180815,plain,(
    k2_zfmisc_1('#skF_8','#skF_7') = k2_zfmisc_1('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_180745,c_88])).

tff(c_182369,plain,(
    ! [A_1879,C_1880,B_1881] : k4_xboole_0(k2_zfmisc_1(A_1879,C_1880),k2_zfmisc_1(B_1881,C_1880)) = k2_zfmisc_1(k4_xboole_0(A_1879,B_1881),C_1880) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_182431,plain,(
    ! [B_1881] : k4_xboole_0(k2_zfmisc_1('#skF_8','#skF_9'),k2_zfmisc_1(B_1881,'#skF_7')) = k2_zfmisc_1(k4_xboole_0('#skF_8',B_1881),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_180815,c_182369])).

tff(c_182669,plain,(
    k2_zfmisc_1(k4_xboole_0('#skF_8','#skF_8'),'#skF_7') = k2_zfmisc_1('#skF_8',k4_xboole_0('#skF_9','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_182662,c_182431])).

tff(c_182757,plain,(
    k2_zfmisc_1('#skF_8',k4_xboole_0('#skF_9','#skF_7')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_180948,c_182669])).

tff(c_182797,plain,
    ( k4_xboole_0('#skF_9','#skF_7') = k1_xboole_0
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_182757,c_66])).

tff(c_182815,plain,(
    k4_xboole_0('#skF_9','#skF_7') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_180746,c_182797])).

tff(c_183174,plain,(
    ! [A_1901,B_1902,C_1903] :
      ( ~ r1_tarski(k2_zfmisc_1(A_1901,B_1902),k2_zfmisc_1(A_1901,C_1903))
      | r1_tarski(B_1902,C_1903)
      | k1_xboole_0 = A_1901 ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_183187,plain,(
    ! [C_1903] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_8','#skF_9'),k2_zfmisc_1('#skF_8',C_1903))
      | r1_tarski('#skF_7',C_1903)
      | k1_xboole_0 = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180815,c_183174])).

tff(c_183968,plain,(
    ! [C_1946] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_8','#skF_9'),k2_zfmisc_1('#skF_8',C_1946))
      | r1_tarski('#skF_7',C_1946) ) ),
    inference(negUnitSimplification,[status(thm)],[c_180746,c_183187])).

tff(c_183989,plain,(
    r1_tarski('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_180826,c_183968])).

tff(c_40,plain,(
    ! [A_25,B_26] :
      ( k4_xboole_0(A_25,B_26) = k1_xboole_0
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_183995,plain,(
    k4_xboole_0('#skF_7','#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_183989,c_40])).

tff(c_184015,plain,
    ( '#skF_7' = '#skF_9'
    | k4_xboole_0('#skF_9','#skF_7') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_183995,c_44])).

tff(c_184050,plain,(
    '#skF_7' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_182815,c_184015])).

tff(c_184052,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_180744,c_184050])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:51:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 41.79/31.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 41.79/31.10  
% 41.79/31.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 41.79/31.10  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4
% 41.79/31.10  
% 41.79/31.10  %Foreground sorts:
% 41.79/31.10  
% 41.79/31.10  
% 41.79/31.10  %Background operators:
% 41.79/31.10  
% 41.79/31.10  
% 41.79/31.10  %Foreground operators:
% 41.79/31.10  tff('#skF_5', type, '#skF_5': $i > $i).
% 41.79/31.10  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 41.79/31.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 41.79/31.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 41.79/31.10  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 41.79/31.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 41.79/31.10  tff('#skF_7', type, '#skF_7': $i).
% 41.79/31.10  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 41.79/31.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 41.79/31.10  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 41.79/31.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 41.79/31.10  tff('#skF_6', type, '#skF_6': $i).
% 41.79/31.10  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 41.79/31.10  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 41.79/31.10  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 41.79/31.10  tff('#skF_9', type, '#skF_9': $i).
% 41.79/31.10  tff('#skF_8', type, '#skF_8': $i).
% 41.79/31.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 41.79/31.10  tff(k3_tarski, type, k3_tarski: $i > $i).
% 41.79/31.10  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 41.79/31.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 41.79/31.10  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 41.79/31.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 41.79/31.10  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 41.79/31.10  
% 41.99/31.13  tff(f_147, negated_conjecture, ~(![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 41.99/31.13  tff(f_136, axiom, (![A, B, C]: ((k2_zfmisc_1(k4_xboole_0(A, B), C) = k4_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k4_xboole_0(A, B)) = k4_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 41.99/31.13  tff(f_119, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 41.99/31.13  tff(f_99, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 41.99/31.13  tff(f_95, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 41.99/31.13  tff(f_87, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 41.99/31.13  tff(f_101, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 41.99/31.13  tff(f_107, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 41.99/31.13  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 41.99/31.13  tff(f_97, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 41.99/31.13  tff(f_61, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 41.99/31.13  tff(f_75, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 41.99/31.13  tff(f_132, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 41.99/31.13  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 41.99/31.13  tff(f_83, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 41.99/31.13  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 41.99/31.13  tff(f_93, axiom, (![A, B]: ((k4_xboole_0(A, B) = k4_xboole_0(B, A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_xboole_1)).
% 41.99/31.13  tff(f_130, axiom, (![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 41.99/31.13  tff(c_82, plain, ('#skF_7'!='#skF_9' | '#skF_6'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_147])).
% 41.99/31.13  tff(c_89, plain, ('#skF_6'!='#skF_8'), inference(splitLeft, [status(thm)], [c_82])).
% 41.99/31.13  tff(c_84, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_147])).
% 41.99/31.13  tff(c_80, plain, (![C_59, A_57, B_58]: (k4_xboole_0(k2_zfmisc_1(C_59, A_57), k2_zfmisc_1(C_59, B_58))=k2_zfmisc_1(C_59, k4_xboole_0(A_57, B_58)))), inference(cnfTransformation, [status(thm)], [f_136])).
% 41.99/31.13  tff(c_88, plain, (k2_zfmisc_1('#skF_6', '#skF_7')=k2_zfmisc_1('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_147])).
% 41.99/31.13  tff(c_1930, plain, (![A_183, C_184, B_185]: (k4_xboole_0(k2_zfmisc_1(A_183, C_184), k2_zfmisc_1(B_185, C_184))=k2_zfmisc_1(k4_xboole_0(A_183, B_185), C_184))), inference(cnfTransformation, [status(thm)], [f_136])).
% 41.99/31.13  tff(c_4813, plain, (![B_280]: (k4_xboole_0(k2_zfmisc_1('#skF_8', '#skF_9'), k2_zfmisc_1(B_280, '#skF_7'))=k2_zfmisc_1(k4_xboole_0('#skF_6', B_280), '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_1930])).
% 41.99/31.13  tff(c_4909, plain, (k2_zfmisc_1(k4_xboole_0('#skF_6', '#skF_8'), '#skF_7')=k2_zfmisc_1('#skF_8', k4_xboole_0('#skF_9', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_80, c_4813])).
% 41.99/31.13  tff(c_66, plain, (![B_49, A_48]: (k1_xboole_0=B_49 | k1_xboole_0=A_48 | k2_zfmisc_1(A_48, B_49)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_119])).
% 41.99/31.13  tff(c_11582, plain, (k1_xboole_0='#skF_7' | k4_xboole_0('#skF_6', '#skF_8')=k1_xboole_0 | k2_zfmisc_1('#skF_8', k4_xboole_0('#skF_9', '#skF_7'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4909, c_66])).
% 41.99/31.13  tff(c_11615, plain, (k4_xboole_0('#skF_6', '#skF_8')=k1_xboole_0 | k2_zfmisc_1('#skF_8', k4_xboole_0('#skF_9', '#skF_7'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_84, c_11582])).
% 41.99/31.13  tff(c_12119, plain, (k2_zfmisc_1('#skF_8', k4_xboole_0('#skF_9', '#skF_7'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_11615])).
% 41.99/31.13  tff(c_50, plain, (![A_33, B_34, C_35]: (k4_xboole_0(k4_xboole_0(A_33, B_34), C_35)=k4_xboole_0(A_33, k2_xboole_0(B_34, C_35)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 41.99/31.13  tff(c_1324, plain, (![A_154, B_155, C_156]: (k4_xboole_0(k4_xboole_0(A_154, B_155), C_156)=k4_xboole_0(A_154, k2_xboole_0(B_155, C_156)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 41.99/31.13  tff(c_1375, plain, (![A_33, B_34, C_35, C_156]: (k4_xboole_0(k4_xboole_0(A_33, k2_xboole_0(B_34, C_35)), C_156)=k4_xboole_0(k4_xboole_0(A_33, B_34), k2_xboole_0(C_35, C_156)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_1324])).
% 41.99/31.13  tff(c_27481, plain, (![A_637, B_638, C_639, C_640]: (k4_xboole_0(A_637, k2_xboole_0(k2_xboole_0(B_638, C_639), C_640))=k4_xboole_0(A_637, k2_xboole_0(B_638, k2_xboole_0(C_639, C_640))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_1375])).
% 41.99/31.13  tff(c_46, plain, (![A_30, B_31]: (r1_tarski(k4_xboole_0(A_30, B_31), A_30))), inference(cnfTransformation, [status(thm)], [f_95])).
% 41.99/31.13  tff(c_275, plain, (![A_83, B_84]: (k4_xboole_0(A_83, B_84)=k1_xboole_0 | ~r1_tarski(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_87])).
% 41.99/31.13  tff(c_287, plain, (![A_30, B_31]: (k4_xboole_0(k4_xboole_0(A_30, B_31), A_30)=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_275])).
% 41.99/31.13  tff(c_1365, plain, (![C_156, B_155]: (k4_xboole_0(C_156, k2_xboole_0(B_155, C_156))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1324, c_287])).
% 41.99/31.13  tff(c_38944, plain, (![C_736, B_737, C_738]: (k4_xboole_0(C_736, k2_xboole_0(B_737, k2_xboole_0(C_738, C_736)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_27481, c_1365])).
% 41.99/31.13  tff(c_52, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k4_xboole_0(A_36, B_37))=k3_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_101])).
% 41.99/31.13  tff(c_252, plain, (![A_75, B_76]: (r1_xboole_0(A_75, B_76) | k4_xboole_0(A_75, B_76)!=A_75)), inference(cnfTransformation, [status(thm)], [f_107])).
% 41.99/31.13  tff(c_24, plain, (![B_12, A_11]: (r1_xboole_0(B_12, A_11) | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 41.99/31.13  tff(c_368, plain, (![B_91, A_92]: (r1_xboole_0(B_91, A_92) | k4_xboole_0(A_92, B_91)!=A_92)), inference(resolution, [status(thm)], [c_252, c_24])).
% 41.99/31.13  tff(c_56, plain, (![A_39, B_40]: (k4_xboole_0(A_39, B_40)=A_39 | ~r1_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_107])).
% 41.99/31.13  tff(c_3344, plain, (![B_250, A_251]: (k4_xboole_0(B_250, A_251)=B_250 | k4_xboole_0(A_251, B_250)!=A_251)), inference(resolution, [status(thm)], [c_368, c_56])).
% 41.99/31.13  tff(c_3372, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k4_xboole_0(A_30, B_31))=A_30 | k4_xboole_0(A_30, B_31)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_287, c_3344])).
% 41.99/31.13  tff(c_3381, plain, (![A_30, B_31]: (k3_xboole_0(A_30, B_31)=A_30 | k4_xboole_0(A_30, B_31)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_3372])).
% 41.99/31.13  tff(c_39429, plain, (![C_736, B_737, C_738]: (k3_xboole_0(C_736, k2_xboole_0(B_737, k2_xboole_0(C_738, C_736)))=C_736)), inference(superposition, [status(thm), theory('equality')], [c_38944, c_3381])).
% 41.99/31.13  tff(c_48, plain, (![A_32]: (k4_xboole_0(A_32, k1_xboole_0)=A_32)), inference(cnfTransformation, [status(thm)], [f_97])).
% 41.99/31.13  tff(c_158, plain, (![A_66, B_67]: (r1_tarski(k4_xboole_0(A_66, B_67), A_66))), inference(cnfTransformation, [status(thm)], [f_95])).
% 41.99/31.13  tff(c_161, plain, (![A_32]: (r1_tarski(A_32, A_32))), inference(superposition, [status(thm), theory('equality')], [c_48, c_158])).
% 41.99/31.13  tff(c_286, plain, (![A_32]: (k4_xboole_0(A_32, A_32)=k1_xboole_0)), inference(resolution, [status(thm)], [c_161, c_275])).
% 41.99/31.13  tff(c_30, plain, (![A_13, B_14]: (r2_hidden('#skF_3'(A_13, B_14), A_13) | r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 41.99/31.13  tff(c_255, plain, (![B_76, A_75]: (r1_xboole_0(B_76, A_75) | k4_xboole_0(A_75, B_76)!=A_75)), inference(resolution, [status(thm)], [c_252, c_24])).
% 41.99/31.13  tff(c_441, plain, (![A_104, B_105]: (k4_xboole_0(A_104, k4_xboole_0(A_104, B_105))=k3_xboole_0(A_104, B_105))), inference(cnfTransformation, [status(thm)], [f_101])).
% 41.99/31.13  tff(c_472, plain, (![A_32]: (k4_xboole_0(A_32, k1_xboole_0)=k3_xboole_0(A_32, A_32))), inference(superposition, [status(thm), theory('equality')], [c_286, c_441])).
% 41.99/31.13  tff(c_491, plain, (![A_106]: (k3_xboole_0(A_106, A_106)=A_106)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_472])).
% 41.99/31.13  tff(c_34, plain, (![A_18, B_19, C_22]: (~r1_xboole_0(A_18, B_19) | ~r2_hidden(C_22, k3_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 41.99/31.13  tff(c_775, plain, (![A_124, C_125]: (~r1_xboole_0(A_124, A_124) | ~r2_hidden(C_125, A_124))), inference(superposition, [status(thm), theory('equality')], [c_491, c_34])).
% 41.99/31.13  tff(c_784, plain, (![C_125, A_75]: (~r2_hidden(C_125, A_75) | k4_xboole_0(A_75, A_75)!=A_75)), inference(resolution, [status(thm)], [c_255, c_775])).
% 41.99/31.13  tff(c_795, plain, (![C_126, A_127]: (~r2_hidden(C_126, A_127) | k1_xboole_0!=A_127)), inference(demodulation, [status(thm), theory('equality')], [c_286, c_784])).
% 41.99/31.13  tff(c_851, plain, (![A_130, B_131]: (k1_xboole_0!=A_130 | r1_xboole_0(A_130, B_131))), inference(resolution, [status(thm)], [c_30, c_795])).
% 41.99/31.13  tff(c_861, plain, (![A_130, B_131]: (k4_xboole_0(A_130, B_131)=A_130 | k1_xboole_0!=A_130)), inference(resolution, [status(thm)], [c_851, c_56])).
% 41.99/31.13  tff(c_487, plain, (![A_32]: (k3_xboole_0(A_32, A_32)=A_32)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_472])).
% 41.99/31.13  tff(c_76, plain, (![A_53, C_55, B_54, D_56]: (k3_xboole_0(k2_zfmisc_1(A_53, C_55), k2_zfmisc_1(B_54, D_56))=k2_zfmisc_1(k3_xboole_0(A_53, B_54), k3_xboole_0(C_55, D_56)))), inference(cnfTransformation, [status(thm)], [f_132])).
% 41.99/31.13  tff(c_1960, plain, (![A_183, C_184, B_185]: (k4_xboole_0(k2_zfmisc_1(A_183, C_184), k2_zfmisc_1(k4_xboole_0(A_183, B_185), C_184))=k3_xboole_0(k2_zfmisc_1(A_183, C_184), k2_zfmisc_1(B_185, C_184)))), inference(superposition, [status(thm), theory('equality')], [c_1930, c_52])).
% 41.99/31.13  tff(c_39454, plain, (![A_739, C_740, B_741]: (k4_xboole_0(k2_zfmisc_1(A_739, C_740), k2_zfmisc_1(k4_xboole_0(A_739, B_741), C_740))=k2_zfmisc_1(k3_xboole_0(A_739, B_741), C_740))), inference(demodulation, [status(thm), theory('equality')], [c_487, c_76, c_1960])).
% 41.99/31.13  tff(c_39883, plain, (![A_130, C_740, B_131]: (k4_xboole_0(k2_zfmisc_1(A_130, C_740), k2_zfmisc_1(A_130, C_740))=k2_zfmisc_1(k3_xboole_0(A_130, B_131), C_740) | k1_xboole_0!=A_130)), inference(superposition, [status(thm), theory('equality')], [c_861, c_39454])).
% 41.99/31.13  tff(c_110359, plain, (![A_1150, B_1151, C_1152]: (k2_zfmisc_1(k3_xboole_0(A_1150, B_1151), C_1152)=k1_xboole_0 | k1_xboole_0!=A_1150)), inference(demodulation, [status(thm), theory('equality')], [c_286, c_39883])).
% 41.99/31.13  tff(c_110897, plain, (![C_1153, C_1154]: (k2_zfmisc_1(C_1153, C_1154)=k1_xboole_0 | k1_xboole_0!=C_1153)), inference(superposition, [status(thm), theory('equality')], [c_39429, c_110359])).
% 41.99/31.13  tff(c_111532, plain, (k2_zfmisc_1('#skF_8', k4_xboole_0('#skF_9', '#skF_7'))=k1_xboole_0 | k4_xboole_0('#skF_6', '#skF_8')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4909, c_110897])).
% 41.99/31.13  tff(c_111711, plain, (k4_xboole_0('#skF_6', '#skF_8')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_12119, c_111532])).
% 41.99/31.13  tff(c_110895, plain, (![C_1152]: (k2_zfmisc_1(k1_xboole_0, C_1152)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_39429, c_110359])).
% 41.99/31.13  tff(c_28, plain, (![A_13, B_14]: (r2_hidden('#skF_3'(A_13, B_14), B_14) | r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 41.99/31.13  tff(c_752, plain, (![A_122, B_123]: (r2_hidden('#skF_3'(A_122, B_123), A_122) | r1_xboole_0(A_122, B_123))), inference(cnfTransformation, [status(thm)], [f_61])).
% 41.99/31.13  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 41.99/31.13  tff(c_21285, plain, (![A_561, B_562, B_563]: (~r2_hidden('#skF_3'(k4_xboole_0(A_561, B_562), B_563), B_562) | r1_xboole_0(k4_xboole_0(A_561, B_562), B_563))), inference(resolution, [status(thm)], [c_752, c_6])).
% 41.99/31.13  tff(c_21433, plain, (![A_564, B_565]: (r1_xboole_0(k4_xboole_0(A_564, B_565), B_565))), inference(resolution, [status(thm)], [c_28, c_21285])).
% 41.99/31.13  tff(c_36, plain, (![A_23]: (r2_hidden('#skF_5'(A_23), A_23) | k1_xboole_0=A_23)), inference(cnfTransformation, [status(thm)], [f_83])).
% 41.99/31.13  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 41.99/31.13  tff(c_415, plain, (![A_100, B_101, C_102]: (~r1_xboole_0(A_100, B_101) | ~r2_hidden(C_102, k3_xboole_0(A_100, B_101)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 41.99/31.13  tff(c_2283, plain, (![A_204, B_205, C_206]: (~r1_xboole_0(A_204, B_205) | ~r2_hidden(C_206, k3_xboole_0(B_205, A_204)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_415])).
% 41.99/31.13  tff(c_2329, plain, (![A_204, B_205]: (~r1_xboole_0(A_204, B_205) | k3_xboole_0(B_205, A_204)=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_2283])).
% 41.99/31.13  tff(c_21543, plain, (![B_565, A_564]: (k3_xboole_0(B_565, k4_xboole_0(A_564, B_565))=k1_xboole_0)), inference(resolution, [status(thm)], [c_21433, c_2329])).
% 41.99/31.13  tff(c_1998, plain, (![B_185]: (k4_xboole_0(k2_zfmisc_1('#skF_8', '#skF_9'), k2_zfmisc_1(B_185, '#skF_7'))=k2_zfmisc_1(k4_xboole_0('#skF_6', B_185), '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_1930])).
% 41.99/31.13  tff(c_4880, plain, (![B_280]: (k4_xboole_0(k2_zfmisc_1('#skF_8', '#skF_9'), k2_zfmisc_1(k4_xboole_0('#skF_6', B_280), '#skF_7'))=k3_xboole_0(k2_zfmisc_1('#skF_8', '#skF_9'), k2_zfmisc_1(B_280, '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_4813, c_52])).
% 41.99/31.13  tff(c_131153, plain, (![B_1289]: (k2_zfmisc_1(k3_xboole_0('#skF_8', B_1289), k3_xboole_0('#skF_9', '#skF_7'))=k2_zfmisc_1(k3_xboole_0('#skF_6', B_1289), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1998, c_76, c_4880])).
% 41.99/31.13  tff(c_131397, plain, (![A_564]: (k2_zfmisc_1(k3_xboole_0('#skF_6', k4_xboole_0(A_564, '#skF_8')), '#skF_7')=k2_zfmisc_1(k1_xboole_0, k3_xboole_0('#skF_9', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_21543, c_131153])).
% 41.99/31.13  tff(c_131794, plain, (![A_1292]: (k2_zfmisc_1(k3_xboole_0('#skF_6', k4_xboole_0(A_1292, '#skF_8')), '#skF_7')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_110895, c_131397])).
% 41.99/31.13  tff(c_131978, plain, (![A_1292]: (k1_xboole_0='#skF_7' | k3_xboole_0('#skF_6', k4_xboole_0(A_1292, '#skF_8'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_131794, c_66])).
% 41.99/31.13  tff(c_132191, plain, (![A_1293]: (k3_xboole_0('#skF_6', k4_xboole_0(A_1293, '#skF_8'))=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_84, c_131978])).
% 41.99/31.13  tff(c_469, plain, (![A_30, B_31]: (k4_xboole_0(k4_xboole_0(A_30, B_31), k1_xboole_0)=k3_xboole_0(k4_xboole_0(A_30, B_31), A_30))), inference(superposition, [status(thm), theory('equality')], [c_287, c_441])).
% 41.99/31.13  tff(c_3124, plain, (![A_243, B_244]: (k3_xboole_0(k4_xboole_0(A_243, B_244), A_243)=k4_xboole_0(A_243, B_244))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_469])).
% 41.99/31.13  tff(c_3184, plain, (![A_243, B_244]: (k3_xboole_0(A_243, k4_xboole_0(A_243, B_244))=k4_xboole_0(A_243, B_244))), inference(superposition, [status(thm), theory('equality')], [c_3124, c_2])).
% 41.99/31.13  tff(c_132533, plain, (k4_xboole_0('#skF_6', '#skF_8')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_132191, c_3184])).
% 41.99/31.13  tff(c_132815, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111711, c_132533])).
% 41.99/31.13  tff(c_132816, plain, (k4_xboole_0('#skF_6', '#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_11615])).
% 41.99/31.13  tff(c_44, plain, (![B_29, A_28]: (B_29=A_28 | k4_xboole_0(B_29, A_28)!=k4_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_93])).
% 41.99/31.13  tff(c_132898, plain, ('#skF_6'='#skF_8' | k4_xboole_0('#skF_8', '#skF_6')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_132816, c_44])).
% 41.99/31.13  tff(c_132956, plain, (k4_xboole_0('#skF_8', '#skF_6')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_89, c_132898])).
% 41.99/31.13  tff(c_86, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_147])).
% 41.99/31.13  tff(c_376, plain, (![B_93, A_94]: (k1_xboole_0=B_93 | k1_xboole_0=A_94 | k2_zfmisc_1(A_94, B_93)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_119])).
% 41.99/31.13  tff(c_382, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_88, c_376])).
% 41.99/31.13  tff(c_388, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_86, c_84, c_382])).
% 41.99/31.13  tff(c_132817, plain, (k2_zfmisc_1('#skF_8', k4_xboole_0('#skF_9', '#skF_7'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_11615])).
% 41.99/31.13  tff(c_133618, plain, (k2_zfmisc_1('#skF_8', '#skF_9')=k1_xboole_0 | k1_xboole_0!='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_861, c_132817])).
% 41.99/31.13  tff(c_133649, plain, (k1_xboole_0!='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_388, c_133618])).
% 41.99/31.13  tff(c_2036, plain, (![C_187, A_188, B_189]: (k4_xboole_0(k2_zfmisc_1(C_187, A_188), k2_zfmisc_1(C_187, B_189))=k2_zfmisc_1(C_187, k4_xboole_0(A_188, B_189)))), inference(cnfTransformation, [status(thm)], [f_136])).
% 41.99/31.13  tff(c_2905, plain, (![B_240]: (k4_xboole_0(k2_zfmisc_1('#skF_8', '#skF_9'), k2_zfmisc_1('#skF_6', B_240))=k2_zfmisc_1('#skF_6', k4_xboole_0('#skF_7', B_240)))), inference(superposition, [status(thm), theory('equality')], [c_88, c_2036])).
% 41.99/31.13  tff(c_78, plain, (![A_57, C_59, B_58]: (k4_xboole_0(k2_zfmisc_1(A_57, C_59), k2_zfmisc_1(B_58, C_59))=k2_zfmisc_1(k4_xboole_0(A_57, B_58), C_59))), inference(cnfTransformation, [status(thm)], [f_136])).
% 41.99/31.13  tff(c_2912, plain, (k2_zfmisc_1(k4_xboole_0('#skF_8', '#skF_6'), '#skF_9')=k2_zfmisc_1('#skF_6', k4_xboole_0('#skF_7', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_2905, c_78])).
% 41.99/31.13  tff(c_172204, plain, (k1_xboole_0='#skF_9' | k4_xboole_0('#skF_8', '#skF_6')=k1_xboole_0 | k2_zfmisc_1('#skF_6', k4_xboole_0('#skF_7', '#skF_9'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2912, c_66])).
% 41.99/31.13  tff(c_172244, plain, (k2_zfmisc_1('#skF_6', k4_xboole_0('#skF_7', '#skF_9'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_132956, c_133649, c_172204])).
% 41.99/31.13  tff(c_132945, plain, (k3_xboole_0('#skF_6', '#skF_8')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_132816, c_3381])).
% 41.99/31.13  tff(c_133122, plain, (k3_xboole_0('#skF_8', '#skF_6')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_2, c_132945])).
% 41.99/31.13  tff(c_648, plain, (![A_116, B_117]: (r2_hidden('#skF_3'(A_116, B_117), B_117) | r1_xboole_0(A_116, B_117))), inference(cnfTransformation, [status(thm)], [f_61])).
% 41.99/31.13  tff(c_136280, plain, (![A_1322, A_1323, B_1324]: (~r2_hidden('#skF_3'(A_1322, k4_xboole_0(A_1323, B_1324)), B_1324) | r1_xboole_0(A_1322, k4_xboole_0(A_1323, B_1324)))), inference(resolution, [status(thm)], [c_648, c_6])).
% 41.99/31.13  tff(c_136441, plain, (![A_1325, A_1326]: (r1_xboole_0(A_1325, k4_xboole_0(A_1326, A_1325)))), inference(resolution, [status(thm)], [c_30, c_136280])).
% 41.99/31.13  tff(c_136563, plain, (![A_1325, A_1326]: (k4_xboole_0(A_1325, k4_xboole_0(A_1326, A_1325))=A_1325)), inference(resolution, [status(thm)], [c_136441, c_56])).
% 41.99/31.13  tff(c_3424, plain, (![A_254]: (k4_xboole_0(k2_zfmisc_1(A_254, '#skF_7'), k2_zfmisc_1('#skF_8', '#skF_9'))=k2_zfmisc_1(k4_xboole_0(A_254, '#skF_6'), '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_1930])).
% 41.99/31.13  tff(c_3488, plain, (k2_zfmisc_1(k4_xboole_0('#skF_8', '#skF_6'), '#skF_7')=k2_zfmisc_1('#skF_8', k4_xboole_0('#skF_7', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_80, c_3424])).
% 41.99/31.13  tff(c_136732, plain, (![A_1329, A_1330]: (k3_xboole_0(k4_xboole_0(A_1329, A_1330), A_1330)=k1_xboole_0)), inference(resolution, [status(thm)], [c_136441, c_2329])).
% 41.99/31.13  tff(c_180332, plain, (![B_1763]: (k3_xboole_0(k2_zfmisc_1(k4_xboole_0('#skF_6', B_1763), '#skF_7'), k2_zfmisc_1(B_1763, '#skF_7'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1998, c_136732])).
% 41.99/31.13  tff(c_180556, plain, (k3_xboole_0(k2_zfmisc_1(k4_xboole_0('#skF_6', k4_xboole_0('#skF_8', '#skF_6')), '#skF_7'), k2_zfmisc_1('#skF_8', k4_xboole_0('#skF_7', '#skF_9')))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3488, c_180332])).
% 41.99/31.13  tff(c_180741, plain, (k2_zfmisc_1('#skF_6', k4_xboole_0('#skF_7', '#skF_9'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_133122, c_2, c_3184, c_76, c_136563, c_180556])).
% 41.99/31.13  tff(c_180743, plain, $false, inference(negUnitSimplification, [status(thm)], [c_172244, c_180741])).
% 41.99/31.13  tff(c_180744, plain, ('#skF_7'!='#skF_9'), inference(splitRight, [status(thm)], [c_82])).
% 41.99/31.13  tff(c_180745, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_82])).
% 41.99/31.13  tff(c_180746, plain, (k1_xboole_0!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_180745, c_86])).
% 41.99/31.13  tff(c_70, plain, (![B_49]: (k2_zfmisc_1(k1_xboole_0, B_49)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_119])).
% 41.99/31.13  tff(c_180820, plain, (![A_1770, B_1771]: (r1_tarski(k4_xboole_0(A_1770, B_1771), A_1770))), inference(cnfTransformation, [status(thm)], [f_95])).
% 41.99/31.13  tff(c_180826, plain, (![A_32]: (r1_tarski(A_32, A_32))), inference(superposition, [status(thm), theory('equality')], [c_48, c_180820])).
% 41.99/31.13  tff(c_180937, plain, (![A_1787, B_1788]: (k4_xboole_0(A_1787, B_1788)=k1_xboole_0 | ~r1_tarski(A_1787, B_1788))), inference(cnfTransformation, [status(thm)], [f_87])).
% 41.99/31.13  tff(c_180948, plain, (![A_32]: (k4_xboole_0(A_32, A_32)=k1_xboole_0)), inference(resolution, [status(thm)], [c_180826, c_180937])).
% 41.99/31.13  tff(c_182662, plain, (![C_1887, A_1888, B_1889]: (k4_xboole_0(k2_zfmisc_1(C_1887, A_1888), k2_zfmisc_1(C_1887, B_1889))=k2_zfmisc_1(C_1887, k4_xboole_0(A_1888, B_1889)))), inference(cnfTransformation, [status(thm)], [f_136])).
% 41.99/31.13  tff(c_180815, plain, (k2_zfmisc_1('#skF_8', '#skF_7')=k2_zfmisc_1('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_180745, c_88])).
% 41.99/31.13  tff(c_182369, plain, (![A_1879, C_1880, B_1881]: (k4_xboole_0(k2_zfmisc_1(A_1879, C_1880), k2_zfmisc_1(B_1881, C_1880))=k2_zfmisc_1(k4_xboole_0(A_1879, B_1881), C_1880))), inference(cnfTransformation, [status(thm)], [f_136])).
% 41.99/31.13  tff(c_182431, plain, (![B_1881]: (k4_xboole_0(k2_zfmisc_1('#skF_8', '#skF_9'), k2_zfmisc_1(B_1881, '#skF_7'))=k2_zfmisc_1(k4_xboole_0('#skF_8', B_1881), '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_180815, c_182369])).
% 41.99/31.13  tff(c_182669, plain, (k2_zfmisc_1(k4_xboole_0('#skF_8', '#skF_8'), '#skF_7')=k2_zfmisc_1('#skF_8', k4_xboole_0('#skF_9', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_182662, c_182431])).
% 41.99/31.13  tff(c_182757, plain, (k2_zfmisc_1('#skF_8', k4_xboole_0('#skF_9', '#skF_7'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_70, c_180948, c_182669])).
% 41.99/31.13  tff(c_182797, plain, (k4_xboole_0('#skF_9', '#skF_7')=k1_xboole_0 | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_182757, c_66])).
% 41.99/31.13  tff(c_182815, plain, (k4_xboole_0('#skF_9', '#skF_7')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_180746, c_182797])).
% 41.99/31.13  tff(c_183174, plain, (![A_1901, B_1902, C_1903]: (~r1_tarski(k2_zfmisc_1(A_1901, B_1902), k2_zfmisc_1(A_1901, C_1903)) | r1_tarski(B_1902, C_1903) | k1_xboole_0=A_1901)), inference(cnfTransformation, [status(thm)], [f_130])).
% 41.99/31.13  tff(c_183187, plain, (![C_1903]: (~r1_tarski(k2_zfmisc_1('#skF_8', '#skF_9'), k2_zfmisc_1('#skF_8', C_1903)) | r1_tarski('#skF_7', C_1903) | k1_xboole_0='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_180815, c_183174])).
% 41.99/31.13  tff(c_183968, plain, (![C_1946]: (~r1_tarski(k2_zfmisc_1('#skF_8', '#skF_9'), k2_zfmisc_1('#skF_8', C_1946)) | r1_tarski('#skF_7', C_1946))), inference(negUnitSimplification, [status(thm)], [c_180746, c_183187])).
% 41.99/31.13  tff(c_183989, plain, (r1_tarski('#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_180826, c_183968])).
% 41.99/31.13  tff(c_40, plain, (![A_25, B_26]: (k4_xboole_0(A_25, B_26)=k1_xboole_0 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_87])).
% 41.99/31.13  tff(c_183995, plain, (k4_xboole_0('#skF_7', '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_183989, c_40])).
% 41.99/31.13  tff(c_184015, plain, ('#skF_7'='#skF_9' | k4_xboole_0('#skF_9', '#skF_7')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_183995, c_44])).
% 41.99/31.13  tff(c_184050, plain, ('#skF_7'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_182815, c_184015])).
% 41.99/31.13  tff(c_184052, plain, $false, inference(negUnitSimplification, [status(thm)], [c_180744, c_184050])).
% 41.99/31.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 41.99/31.13  
% 41.99/31.13  Inference rules
% 41.99/31.13  ----------------------
% 41.99/31.13  #Ref     : 10
% 41.99/31.13  #Sup     : 47390
% 41.99/31.13  #Fact    : 0
% 41.99/31.13  #Define  : 0
% 41.99/31.13  #Split   : 22
% 41.99/31.13  #Chain   : 0
% 41.99/31.13  #Close   : 0
% 41.99/31.13  
% 41.99/31.13  Ordering : KBO
% 41.99/31.13  
% 41.99/31.13  Simplification rules
% 41.99/31.13  ----------------------
% 41.99/31.13  #Subsume      : 9375
% 41.99/31.13  #Demod        : 45318
% 41.99/31.13  #Tautology    : 21089
% 41.99/31.13  #SimpNegUnit  : 1218
% 41.99/31.13  #BackRed      : 31
% 41.99/31.13  
% 41.99/31.13  #Partial instantiations: 0
% 41.99/31.13  #Strategies tried      : 1
% 41.99/31.13  
% 41.99/31.13  Timing (in seconds)
% 41.99/31.13  ----------------------
% 41.99/31.13  Preprocessing        : 0.35
% 41.99/31.13  Parsing              : 0.18
% 41.99/31.13  CNF conversion       : 0.03
% 41.99/31.13  Main loop            : 29.99
% 41.99/31.13  Inferencing          : 2.81
% 41.99/31.13  Reduction            : 18.50
% 41.99/31.13  Demodulation         : 16.44
% 41.99/31.13  BG Simplification    : 0.37
% 41.99/31.13  Subsumption          : 7.10
% 41.99/31.13  Abstraction          : 0.58
% 41.99/31.13  MUC search           : 0.00
% 41.99/31.13  Cooper               : 0.00
% 41.99/31.13  Total                : 30.39
% 41.99/31.13  Index Insertion      : 0.00
% 41.99/31.13  Index Deletion       : 0.00
% 41.99/31.13  Index Matching       : 0.00
% 41.99/31.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
