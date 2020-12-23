%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:20 EST 2020

% Result     : Theorem 20.16s
% Output     : CNFRefutation 20.16s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 464 expanded)
%              Number of leaves         :   23 ( 162 expanded)
%              Depth                    :   28
%              Number of atoms          :  154 (1054 expanded)
%              Number of equality atoms :   60 ( 299 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(B,C) )
     => ( A = k1_xboole_0
        | r1_tarski(B,k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(k1_setfam_1(B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_setfam_1)).

tff(c_46,plain,(
    k1_setfam_1(k1_tarski('#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_16,plain,(
    ! [C_12] : r2_hidden(C_12,k1_tarski(C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_118,plain,(
    ! [A_47,B_48,C_49] :
      ( r2_hidden(A_47,B_48)
      | ~ r2_hidden(A_47,k4_xboole_0(B_48,k1_tarski(C_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2483,plain,(
    ! [B_2072,C_2073,B_2074] :
      ( r2_hidden('#skF_1'(k4_xboole_0(B_2072,k1_tarski(C_2073)),B_2074),B_2072)
      | r1_tarski(k4_xboole_0(B_2072,k1_tarski(C_2073)),B_2074) ) ),
    inference(resolution,[status(thm)],[c_6,c_118])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2507,plain,(
    ! [B_2075,C_2076] : r1_tarski(k4_xboole_0(B_2075,k1_tarski(C_2076)),B_2075) ),
    inference(resolution,[status(thm)],[c_2483,c_4])).

tff(c_32,plain,(
    ! [B_15] : r1_tarski(k1_xboole_0,k1_tarski(B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_92,plain,(
    ! [C_40,B_41,A_42] :
      ( r2_hidden(C_40,B_41)
      | ~ r2_hidden(C_40,A_42)
      | ~ r1_tarski(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_426,plain,(
    ! [A_84,B_85,B_86] :
      ( r2_hidden('#skF_1'(A_84,B_85),B_86)
      | ~ r1_tarski(A_84,B_86)
      | r1_tarski(A_84,B_85) ) ),
    inference(resolution,[status(thm)],[c_6,c_92])).

tff(c_14,plain,(
    ! [C_12,A_8] :
      ( C_12 = A_8
      | ~ r2_hidden(C_12,k1_tarski(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_533,plain,(
    ! [A_97,A_98,B_99] :
      ( A_97 = '#skF_1'(A_98,B_99)
      | ~ r1_tarski(A_98,k1_tarski(A_97))
      | r1_tarski(A_98,B_99) ) ),
    inference(resolution,[status(thm)],[c_426,c_14])).

tff(c_586,plain,(
    ! [B_102,B_103] :
      ( B_102 = '#skF_1'(k1_xboole_0,B_103)
      | r1_tarski(k1_xboole_0,B_103) ) ),
    inference(resolution,[status(thm)],[c_32,c_533])).

tff(c_80,plain,(
    ! [A_38,B_39] :
      ( r2_hidden('#skF_1'(A_38,B_39),A_38)
      | r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_154,plain,(
    ! [A_57,B_58] :
      ( '#skF_1'(k1_tarski(A_57),B_58) = A_57
      | r1_tarski(k1_tarski(A_57),B_58) ) ),
    inference(resolution,[status(thm)],[c_80,c_14])).

tff(c_68,plain,(
    ! [B_33,A_34] :
      ( B_33 = A_34
      | ~ r1_tarski(B_33,A_34)
      | ~ r1_tarski(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_73,plain,(
    ! [B_15] :
      ( k1_tarski(B_15) = k1_xboole_0
      | ~ r1_tarski(k1_tarski(B_15),k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_32,c_68])).

tff(c_211,plain,(
    ! [A_64] :
      ( k1_tarski(A_64) = k1_xboole_0
      | '#skF_1'(k1_tarski(A_64),k1_xboole_0) = A_64 ) ),
    inference(resolution,[status(thm)],[c_154,c_73])).

tff(c_292,plain,(
    ! [A_72] :
      ( ~ r2_hidden(A_72,k1_xboole_0)
      | r1_tarski(k1_tarski(A_72),k1_xboole_0)
      | k1_tarski(A_72) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_4])).

tff(c_329,plain,(
    ! [A_75] :
      ( ~ r2_hidden(A_75,k1_xboole_0)
      | k1_tarski(A_75) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_292,c_73])).

tff(c_341,plain,(
    ! [B_76] :
      ( k1_tarski('#skF_1'(k1_xboole_0,B_76)) = k1_xboole_0
      | r1_tarski(k1_xboole_0,B_76) ) ),
    inference(resolution,[status(thm)],[c_6,c_329])).

tff(c_36,plain,(
    ! [C_18,B_17] : ~ r2_hidden(C_18,k4_xboole_0(B_17,k1_tarski(C_18))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_372,plain,(
    ! [B_76,B_17] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0,B_76),k4_xboole_0(B_17,k1_xboole_0))
      | r1_tarski(k1_xboole_0,B_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_36])).

tff(c_466,plain,(
    ! [B_17,B_85] :
      ( ~ r1_tarski(k1_xboole_0,k4_xboole_0(B_17,k1_xboole_0))
      | r1_tarski(k1_xboole_0,B_85) ) ),
    inference(resolution,[status(thm)],[c_426,c_372])).

tff(c_475,plain,(
    ! [B_17] : ~ r1_tarski(k1_xboole_0,k4_xboole_0(B_17,k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_466])).

tff(c_989,plain,(
    ! [B_734] : '#skF_1'(k1_xboole_0,k4_xboole_0(B_734,k1_xboole_0)) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_586,c_475])).

tff(c_981,plain,(
    ! [B_102,B_17] : B_102 = '#skF_1'(k1_xboole_0,k4_xboole_0(B_17,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_586,c_475])).

tff(c_1521,plain,(
    ! [B_1365] : B_1365 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_989,c_981])).

tff(c_1662,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_1521,c_46])).

tff(c_1676,plain,(
    ! [B_2026] : r1_tarski(k1_xboole_0,B_2026) ),
    inference(splitRight,[status(thm)],[c_466])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1698,plain,(
    ! [B_2026] :
      ( k1_xboole_0 = B_2026
      | ~ r1_tarski(B_2026,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1676,c_8])).

tff(c_2545,plain,(
    ! [C_2077] : k4_xboole_0(k1_xboole_0,k1_tarski(C_2077)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2507,c_1698])).

tff(c_2567,plain,(
    ! [C_2077] : ~ r2_hidden(C_2077,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2545,c_36])).

tff(c_28,plain,(
    ! [B_15,A_14] :
      ( k1_tarski(B_15) = A_14
      | k1_xboole_0 = A_14
      | ~ r1_tarski(A_14,k1_tarski(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2543,plain,(
    ! [B_15,C_2076] :
      ( k4_xboole_0(k1_tarski(B_15),k1_tarski(C_2076)) = k1_tarski(B_15)
      | k4_xboole_0(k1_tarski(B_15),k1_tarski(C_2076)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2507,c_28])).

tff(c_6294,plain,(
    ! [B_2210,C_2211] :
      ( k4_xboole_0(k1_tarski(B_2210),k1_tarski(C_2211)) = k1_xboole_0
      | k1_tarski(B_2210) != k1_xboole_0 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_2543])).

tff(c_34,plain,(
    ! [A_16,B_17,C_18] :
      ( r2_hidden(A_16,k4_xboole_0(B_17,k1_tarski(C_18)))
      | C_18 = A_16
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6362,plain,(
    ! [A_16,C_2211,B_2210] :
      ( r2_hidden(A_16,k1_xboole_0)
      | C_2211 = A_16
      | ~ r2_hidden(A_16,k1_tarski(B_2210))
      | k1_tarski(B_2210) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6294,c_34])).

tff(c_6388,plain,(
    ! [C_2212,A_2213,B_2214] :
      ( C_2212 = A_2213
      | ~ r2_hidden(A_2213,k1_tarski(B_2214))
      | k1_tarski(B_2214) != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_2567,c_6362])).

tff(c_7235,plain,(
    ! [C_2229,B_2230,B_2231] :
      ( C_2229 = '#skF_1'(k1_tarski(B_2230),B_2231)
      | k1_tarski(B_2230) != k1_xboole_0
      | r1_tarski(k1_tarski(B_2230),B_2231) ) ),
    inference(resolution,[status(thm)],[c_6,c_6388])).

tff(c_98,plain,(
    ! [C_12,B_41] :
      ( r2_hidden(C_12,B_41)
      | ~ r1_tarski(k1_tarski(C_12),B_41) ) ),
    inference(resolution,[status(thm)],[c_16,c_92])).

tff(c_8464,plain,(
    ! [B_3912,B_3913,C_3914] :
      ( r2_hidden(B_3912,B_3913)
      | C_3914 = '#skF_1'(k1_tarski(B_3912),B_3913)
      | k1_tarski(B_3912) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_7235,c_98])).

tff(c_13608,plain,(
    ! [C_6821,B_6822,B_6823] :
      ( r2_hidden(C_6821,'#skF_1'(k1_tarski(B_6822),B_6823))
      | r2_hidden(B_6822,B_6823)
      | k1_tarski(B_6822) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8464,c_16])).

tff(c_9630,plain,(
    ! [C_18,B_3912,B_3913] :
      ( ~ r2_hidden(C_18,'#skF_1'(k1_tarski(B_3912),B_3913))
      | r2_hidden(B_3912,B_3913)
      | k1_tarski(B_3912) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8464,c_36])).

tff(c_14065,plain,(
    ! [B_6882,B_6883] :
      ( r2_hidden(B_6882,B_6883)
      | k1_tarski(B_6882) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_13608,c_9630])).

tff(c_14211,plain,(
    ! [B_6882] : k1_tarski(B_6882) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14065,c_36])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_309,plain,(
    ! [A_73,B_74] :
      ( r2_hidden('#skF_4'(A_73,B_74),A_73)
      | r1_tarski(B_74,k1_setfam_1(A_73))
      | k1_xboole_0 = A_73 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_328,plain,(
    ! [A_8,B_74] :
      ( '#skF_4'(k1_tarski(A_8),B_74) = A_8
      | r1_tarski(B_74,k1_setfam_1(k1_tarski(A_8)))
      | k1_tarski(A_8) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_309,c_14])).

tff(c_14217,plain,(
    ! [A_6899,B_6900] :
      ( '#skF_4'(k1_tarski(A_6899),B_6900) = A_6899
      | r1_tarski(B_6900,k1_setfam_1(k1_tarski(A_6899))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14211,c_328])).

tff(c_124,plain,(
    ! [B_50,C_51,A_52] :
      ( r1_tarski(k1_setfam_1(B_50),C_51)
      | ~ r1_tarski(A_52,C_51)
      | ~ r2_hidden(A_52,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_131,plain,(
    ! [B_53,B_54] :
      ( r1_tarski(k1_setfam_1(B_53),B_54)
      | ~ r2_hidden(B_54,B_53) ) ),
    inference(resolution,[status(thm)],[c_12,c_124])).

tff(c_142,plain,(
    ! [B_53,B_54] :
      ( k1_setfam_1(B_53) = B_54
      | ~ r1_tarski(B_54,k1_setfam_1(B_53))
      | ~ r2_hidden(B_54,B_53) ) ),
    inference(resolution,[status(thm)],[c_131,c_8])).

tff(c_116454,plain,(
    ! [A_26692,B_26693] :
      ( k1_setfam_1(k1_tarski(A_26692)) = B_26693
      | ~ r2_hidden(B_26693,k1_tarski(A_26692))
      | '#skF_4'(k1_tarski(A_26692),B_26693) = A_26692 ) ),
    inference(resolution,[status(thm)],[c_14217,c_142])).

tff(c_116708,plain,(
    ! [C_26764] :
      ( k1_setfam_1(k1_tarski(C_26764)) = C_26764
      | '#skF_4'(k1_tarski(C_26764),C_26764) = C_26764 ) ),
    inference(resolution,[status(thm)],[c_16,c_116454])).

tff(c_117710,plain,(
    '#skF_4'(k1_tarski('#skF_5'),'#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_116708,c_46])).

tff(c_40,plain,(
    ! [B_20,A_19] :
      ( ~ r1_tarski(B_20,'#skF_4'(A_19,B_20))
      | r1_tarski(B_20,k1_setfam_1(A_19))
      | k1_xboole_0 = A_19 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_117798,plain,
    ( ~ r1_tarski('#skF_5','#skF_5')
    | r1_tarski('#skF_5',k1_setfam_1(k1_tarski('#skF_5')))
    | k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_117710,c_40])).

tff(c_117972,plain,
    ( r1_tarski('#skF_5',k1_setfam_1(k1_tarski('#skF_5')))
    | k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_117798])).

tff(c_117973,plain,(
    r1_tarski('#skF_5',k1_setfam_1(k1_tarski('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_14211,c_117972])).

tff(c_118004,plain,
    ( k1_setfam_1(k1_tarski('#skF_5')) = '#skF_5'
    | ~ r2_hidden('#skF_5',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_117973,c_142])).

tff(c_118240,plain,(
    k1_setfam_1(k1_tarski('#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_118004])).

tff(c_118242,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_118240])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:03:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.16/11.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.16/11.22  
% 20.16/11.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.16/11.22  %$ r2_hidden > r1_tarski > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 20.16/11.22  
% 20.16/11.22  %Foreground sorts:
% 20.16/11.22  
% 20.16/11.22  
% 20.16/11.22  %Background operators:
% 20.16/11.22  
% 20.16/11.22  
% 20.16/11.22  %Foreground operators:
% 20.16/11.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.16/11.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 20.16/11.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 20.16/11.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 20.16/11.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 20.16/11.22  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 20.16/11.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.16/11.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 20.16/11.22  tff('#skF_5', type, '#skF_5': $i).
% 20.16/11.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.16/11.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.16/11.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 20.16/11.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 20.16/11.22  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 20.16/11.22  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 20.16/11.22  
% 20.16/11.24  tff(f_78, negated_conjecture, ~(![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 20.16/11.24  tff(f_45, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 20.16/11.24  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 20.16/11.24  tff(f_60, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 20.16/11.24  tff(f_53, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 20.16/11.24  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 20.16/11.24  tff(f_69, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(B, C))) => ((A = k1_xboole_0) | r1_tarski(B, k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_setfam_1)).
% 20.16/11.24  tff(f_75, axiom, (![A, B, C]: ((r2_hidden(A, B) & r1_tarski(A, C)) => r1_tarski(k1_setfam_1(B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_setfam_1)).
% 20.16/11.24  tff(c_46, plain, (k1_setfam_1(k1_tarski('#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_78])).
% 20.16/11.24  tff(c_16, plain, (![C_12]: (r2_hidden(C_12, k1_tarski(C_12)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 20.16/11.24  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 20.16/11.24  tff(c_118, plain, (![A_47, B_48, C_49]: (r2_hidden(A_47, B_48) | ~r2_hidden(A_47, k4_xboole_0(B_48, k1_tarski(C_49))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 20.16/11.24  tff(c_2483, plain, (![B_2072, C_2073, B_2074]: (r2_hidden('#skF_1'(k4_xboole_0(B_2072, k1_tarski(C_2073)), B_2074), B_2072) | r1_tarski(k4_xboole_0(B_2072, k1_tarski(C_2073)), B_2074))), inference(resolution, [status(thm)], [c_6, c_118])).
% 20.16/11.24  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 20.16/11.24  tff(c_2507, plain, (![B_2075, C_2076]: (r1_tarski(k4_xboole_0(B_2075, k1_tarski(C_2076)), B_2075))), inference(resolution, [status(thm)], [c_2483, c_4])).
% 20.16/11.24  tff(c_32, plain, (![B_15]: (r1_tarski(k1_xboole_0, k1_tarski(B_15)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 20.16/11.24  tff(c_92, plain, (![C_40, B_41, A_42]: (r2_hidden(C_40, B_41) | ~r2_hidden(C_40, A_42) | ~r1_tarski(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_32])).
% 20.16/11.24  tff(c_426, plain, (![A_84, B_85, B_86]: (r2_hidden('#skF_1'(A_84, B_85), B_86) | ~r1_tarski(A_84, B_86) | r1_tarski(A_84, B_85))), inference(resolution, [status(thm)], [c_6, c_92])).
% 20.16/11.24  tff(c_14, plain, (![C_12, A_8]: (C_12=A_8 | ~r2_hidden(C_12, k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 20.16/11.24  tff(c_533, plain, (![A_97, A_98, B_99]: (A_97='#skF_1'(A_98, B_99) | ~r1_tarski(A_98, k1_tarski(A_97)) | r1_tarski(A_98, B_99))), inference(resolution, [status(thm)], [c_426, c_14])).
% 20.16/11.24  tff(c_586, plain, (![B_102, B_103]: (B_102='#skF_1'(k1_xboole_0, B_103) | r1_tarski(k1_xboole_0, B_103))), inference(resolution, [status(thm)], [c_32, c_533])).
% 20.16/11.24  tff(c_80, plain, (![A_38, B_39]: (r2_hidden('#skF_1'(A_38, B_39), A_38) | r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_32])).
% 20.16/11.24  tff(c_154, plain, (![A_57, B_58]: ('#skF_1'(k1_tarski(A_57), B_58)=A_57 | r1_tarski(k1_tarski(A_57), B_58))), inference(resolution, [status(thm)], [c_80, c_14])).
% 20.16/11.24  tff(c_68, plain, (![B_33, A_34]: (B_33=A_34 | ~r1_tarski(B_33, A_34) | ~r1_tarski(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_38])).
% 20.16/11.24  tff(c_73, plain, (![B_15]: (k1_tarski(B_15)=k1_xboole_0 | ~r1_tarski(k1_tarski(B_15), k1_xboole_0))), inference(resolution, [status(thm)], [c_32, c_68])).
% 20.16/11.24  tff(c_211, plain, (![A_64]: (k1_tarski(A_64)=k1_xboole_0 | '#skF_1'(k1_tarski(A_64), k1_xboole_0)=A_64)), inference(resolution, [status(thm)], [c_154, c_73])).
% 20.16/11.24  tff(c_292, plain, (![A_72]: (~r2_hidden(A_72, k1_xboole_0) | r1_tarski(k1_tarski(A_72), k1_xboole_0) | k1_tarski(A_72)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_211, c_4])).
% 20.16/11.24  tff(c_329, plain, (![A_75]: (~r2_hidden(A_75, k1_xboole_0) | k1_tarski(A_75)=k1_xboole_0)), inference(resolution, [status(thm)], [c_292, c_73])).
% 20.16/11.24  tff(c_341, plain, (![B_76]: (k1_tarski('#skF_1'(k1_xboole_0, B_76))=k1_xboole_0 | r1_tarski(k1_xboole_0, B_76))), inference(resolution, [status(thm)], [c_6, c_329])).
% 20.16/11.24  tff(c_36, plain, (![C_18, B_17]: (~r2_hidden(C_18, k4_xboole_0(B_17, k1_tarski(C_18))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 20.16/11.24  tff(c_372, plain, (![B_76, B_17]: (~r2_hidden('#skF_1'(k1_xboole_0, B_76), k4_xboole_0(B_17, k1_xboole_0)) | r1_tarski(k1_xboole_0, B_76))), inference(superposition, [status(thm), theory('equality')], [c_341, c_36])).
% 20.16/11.24  tff(c_466, plain, (![B_17, B_85]: (~r1_tarski(k1_xboole_0, k4_xboole_0(B_17, k1_xboole_0)) | r1_tarski(k1_xboole_0, B_85))), inference(resolution, [status(thm)], [c_426, c_372])).
% 20.16/11.24  tff(c_475, plain, (![B_17]: (~r1_tarski(k1_xboole_0, k4_xboole_0(B_17, k1_xboole_0)))), inference(splitLeft, [status(thm)], [c_466])).
% 20.16/11.24  tff(c_989, plain, (![B_734]: ('#skF_1'(k1_xboole_0, k4_xboole_0(B_734, k1_xboole_0))='#skF_5')), inference(resolution, [status(thm)], [c_586, c_475])).
% 20.16/11.24  tff(c_981, plain, (![B_102, B_17]: (B_102='#skF_1'(k1_xboole_0, k4_xboole_0(B_17, k1_xboole_0)))), inference(resolution, [status(thm)], [c_586, c_475])).
% 20.16/11.24  tff(c_1521, plain, (![B_1365]: (B_1365='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_989, c_981])).
% 20.16/11.24  tff(c_1662, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_1521, c_46])).
% 20.16/11.24  tff(c_1676, plain, (![B_2026]: (r1_tarski(k1_xboole_0, B_2026))), inference(splitRight, [status(thm)], [c_466])).
% 20.16/11.24  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 20.16/11.24  tff(c_1698, plain, (![B_2026]: (k1_xboole_0=B_2026 | ~r1_tarski(B_2026, k1_xboole_0))), inference(resolution, [status(thm)], [c_1676, c_8])).
% 20.16/11.24  tff(c_2545, plain, (![C_2077]: (k4_xboole_0(k1_xboole_0, k1_tarski(C_2077))=k1_xboole_0)), inference(resolution, [status(thm)], [c_2507, c_1698])).
% 20.16/11.24  tff(c_2567, plain, (![C_2077]: (~r2_hidden(C_2077, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2545, c_36])).
% 20.16/11.24  tff(c_28, plain, (![B_15, A_14]: (k1_tarski(B_15)=A_14 | k1_xboole_0=A_14 | ~r1_tarski(A_14, k1_tarski(B_15)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 20.16/11.24  tff(c_2543, plain, (![B_15, C_2076]: (k4_xboole_0(k1_tarski(B_15), k1_tarski(C_2076))=k1_tarski(B_15) | k4_xboole_0(k1_tarski(B_15), k1_tarski(C_2076))=k1_xboole_0)), inference(resolution, [status(thm)], [c_2507, c_28])).
% 20.16/11.24  tff(c_6294, plain, (![B_2210, C_2211]: (k4_xboole_0(k1_tarski(B_2210), k1_tarski(C_2211))=k1_xboole_0 | k1_tarski(B_2210)!=k1_xboole_0)), inference(factorization, [status(thm), theory('equality')], [c_2543])).
% 20.16/11.24  tff(c_34, plain, (![A_16, B_17, C_18]: (r2_hidden(A_16, k4_xboole_0(B_17, k1_tarski(C_18))) | C_18=A_16 | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_60])).
% 20.16/11.24  tff(c_6362, plain, (![A_16, C_2211, B_2210]: (r2_hidden(A_16, k1_xboole_0) | C_2211=A_16 | ~r2_hidden(A_16, k1_tarski(B_2210)) | k1_tarski(B_2210)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6294, c_34])).
% 20.16/11.24  tff(c_6388, plain, (![C_2212, A_2213, B_2214]: (C_2212=A_2213 | ~r2_hidden(A_2213, k1_tarski(B_2214)) | k1_tarski(B_2214)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_2567, c_6362])).
% 20.16/11.24  tff(c_7235, plain, (![C_2229, B_2230, B_2231]: (C_2229='#skF_1'(k1_tarski(B_2230), B_2231) | k1_tarski(B_2230)!=k1_xboole_0 | r1_tarski(k1_tarski(B_2230), B_2231))), inference(resolution, [status(thm)], [c_6, c_6388])).
% 20.16/11.24  tff(c_98, plain, (![C_12, B_41]: (r2_hidden(C_12, B_41) | ~r1_tarski(k1_tarski(C_12), B_41))), inference(resolution, [status(thm)], [c_16, c_92])).
% 20.16/11.24  tff(c_8464, plain, (![B_3912, B_3913, C_3914]: (r2_hidden(B_3912, B_3913) | C_3914='#skF_1'(k1_tarski(B_3912), B_3913) | k1_tarski(B_3912)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_7235, c_98])).
% 20.16/11.24  tff(c_13608, plain, (![C_6821, B_6822, B_6823]: (r2_hidden(C_6821, '#skF_1'(k1_tarski(B_6822), B_6823)) | r2_hidden(B_6822, B_6823) | k1_tarski(B_6822)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8464, c_16])).
% 20.16/11.24  tff(c_9630, plain, (![C_18, B_3912, B_3913]: (~r2_hidden(C_18, '#skF_1'(k1_tarski(B_3912), B_3913)) | r2_hidden(B_3912, B_3913) | k1_tarski(B_3912)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8464, c_36])).
% 20.16/11.24  tff(c_14065, plain, (![B_6882, B_6883]: (r2_hidden(B_6882, B_6883) | k1_tarski(B_6882)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_13608, c_9630])).
% 20.16/11.24  tff(c_14211, plain, (![B_6882]: (k1_tarski(B_6882)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_14065, c_36])).
% 20.16/11.24  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 20.16/11.24  tff(c_309, plain, (![A_73, B_74]: (r2_hidden('#skF_4'(A_73, B_74), A_73) | r1_tarski(B_74, k1_setfam_1(A_73)) | k1_xboole_0=A_73)), inference(cnfTransformation, [status(thm)], [f_69])).
% 20.16/11.24  tff(c_328, plain, (![A_8, B_74]: ('#skF_4'(k1_tarski(A_8), B_74)=A_8 | r1_tarski(B_74, k1_setfam_1(k1_tarski(A_8))) | k1_tarski(A_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_309, c_14])).
% 20.16/11.24  tff(c_14217, plain, (![A_6899, B_6900]: ('#skF_4'(k1_tarski(A_6899), B_6900)=A_6899 | r1_tarski(B_6900, k1_setfam_1(k1_tarski(A_6899))))), inference(negUnitSimplification, [status(thm)], [c_14211, c_328])).
% 20.16/11.24  tff(c_124, plain, (![B_50, C_51, A_52]: (r1_tarski(k1_setfam_1(B_50), C_51) | ~r1_tarski(A_52, C_51) | ~r2_hidden(A_52, B_50))), inference(cnfTransformation, [status(thm)], [f_75])).
% 20.16/11.24  tff(c_131, plain, (![B_53, B_54]: (r1_tarski(k1_setfam_1(B_53), B_54) | ~r2_hidden(B_54, B_53))), inference(resolution, [status(thm)], [c_12, c_124])).
% 20.16/11.24  tff(c_142, plain, (![B_53, B_54]: (k1_setfam_1(B_53)=B_54 | ~r1_tarski(B_54, k1_setfam_1(B_53)) | ~r2_hidden(B_54, B_53))), inference(resolution, [status(thm)], [c_131, c_8])).
% 20.16/11.24  tff(c_116454, plain, (![A_26692, B_26693]: (k1_setfam_1(k1_tarski(A_26692))=B_26693 | ~r2_hidden(B_26693, k1_tarski(A_26692)) | '#skF_4'(k1_tarski(A_26692), B_26693)=A_26692)), inference(resolution, [status(thm)], [c_14217, c_142])).
% 20.16/11.24  tff(c_116708, plain, (![C_26764]: (k1_setfam_1(k1_tarski(C_26764))=C_26764 | '#skF_4'(k1_tarski(C_26764), C_26764)=C_26764)), inference(resolution, [status(thm)], [c_16, c_116454])).
% 20.16/11.24  tff(c_117710, plain, ('#skF_4'(k1_tarski('#skF_5'), '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_116708, c_46])).
% 20.16/11.24  tff(c_40, plain, (![B_20, A_19]: (~r1_tarski(B_20, '#skF_4'(A_19, B_20)) | r1_tarski(B_20, k1_setfam_1(A_19)) | k1_xboole_0=A_19)), inference(cnfTransformation, [status(thm)], [f_69])).
% 20.16/11.24  tff(c_117798, plain, (~r1_tarski('#skF_5', '#skF_5') | r1_tarski('#skF_5', k1_setfam_1(k1_tarski('#skF_5'))) | k1_tarski('#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_117710, c_40])).
% 20.16/11.24  tff(c_117972, plain, (r1_tarski('#skF_5', k1_setfam_1(k1_tarski('#skF_5'))) | k1_tarski('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_117798])).
% 20.16/11.24  tff(c_117973, plain, (r1_tarski('#skF_5', k1_setfam_1(k1_tarski('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_14211, c_117972])).
% 20.16/11.24  tff(c_118004, plain, (k1_setfam_1(k1_tarski('#skF_5'))='#skF_5' | ~r2_hidden('#skF_5', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_117973, c_142])).
% 20.16/11.24  tff(c_118240, plain, (k1_setfam_1(k1_tarski('#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_118004])).
% 20.16/11.24  tff(c_118242, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_118240])).
% 20.16/11.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.16/11.24  
% 20.16/11.24  Inference rules
% 20.16/11.24  ----------------------
% 20.16/11.24  #Ref     : 2
% 20.16/11.24  #Sup     : 20276
% 20.16/11.24  #Fact    : 4
% 20.16/11.24  #Define  : 0
% 20.16/11.24  #Split   : 12
% 20.16/11.24  #Chain   : 0
% 20.16/11.24  #Close   : 0
% 20.16/11.24  
% 20.16/11.24  Ordering : KBO
% 20.16/11.24  
% 20.16/11.24  Simplification rules
% 20.16/11.24  ----------------------
% 20.16/11.24  #Subsume      : 7485
% 20.16/11.24  #Demod        : 8380
% 20.16/11.24  #Tautology    : 6662
% 20.16/11.24  #SimpNegUnit  : 853
% 20.16/11.24  #BackRed      : 11
% 20.16/11.24  
% 20.16/11.24  #Partial instantiations: 18230
% 20.16/11.24  #Strategies tried      : 1
% 20.16/11.24  
% 20.16/11.24  Timing (in seconds)
% 20.16/11.24  ----------------------
% 20.16/11.24  Preprocessing        : 0.31
% 20.16/11.24  Parsing              : 0.15
% 20.16/11.24  CNF conversion       : 0.02
% 20.16/11.24  Main loop            : 10.16
% 20.16/11.24  Inferencing          : 1.94
% 20.16/11.24  Reduction            : 2.48
% 20.16/11.24  Demodulation         : 1.55
% 20.16/11.24  BG Simplification    : 0.24
% 20.16/11.24  Subsumption          : 5.02
% 20.16/11.24  Abstraction          : 0.39
% 20.16/11.24  MUC search           : 0.00
% 20.16/11.24  Cooper               : 0.00
% 20.16/11.24  Total                : 10.51
% 20.16/11.24  Index Insertion      : 0.00
% 20.16/11.24  Index Deletion       : 0.00
% 20.16/11.24  Index Matching       : 0.00
% 20.16/11.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
