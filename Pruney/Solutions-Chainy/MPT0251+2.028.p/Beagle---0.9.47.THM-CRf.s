%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:50 EST 2020

% Result     : Theorem 38.67s
% Output     : CNFRefutation 38.67s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 269 expanded)
%              Number of leaves         :   38 ( 105 expanded)
%              Depth                    :   18
%              Number of atoms          :  135 ( 391 expanded)
%              Number of equality atoms :   56 ( 189 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_104,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_69,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_83,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_65,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_93,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_59,axiom,(
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

tff(f_73,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_85,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_70,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_38,plain,(
    ! [A_20] : k2_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_50,plain,(
    ! [B_30,A_29] : k2_tarski(B_30,A_29) = k2_tarski(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_34,plain,(
    ! [B_17] : r1_tarski(B_17,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_342,plain,(
    ! [A_81,C_82,B_83] :
      ( r2_hidden(A_81,C_82)
      | ~ r1_tarski(k2_tarski(A_81,B_83),C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_357,plain,(
    ! [A_84,B_85] : r2_hidden(A_84,k2_tarski(A_84,B_85)) ),
    inference(resolution,[status(thm)],[c_34,c_342])).

tff(c_363,plain,(
    ! [A_29,B_30] : r2_hidden(A_29,k2_tarski(B_30,A_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_357])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_134,plain,(
    ! [A_54,B_55] : k3_tarski(k2_tarski(A_54,B_55)) = k2_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_216,plain,(
    ! [B_74,A_75] : k3_tarski(k2_tarski(B_74,A_75)) = k2_xboole_0(A_75,B_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_134])).

tff(c_60,plain,(
    ! [A_41,B_42] : k3_tarski(k2_tarski(A_41,B_42)) = k2_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_243,plain,(
    ! [B_76,A_77] : k2_xboole_0(B_76,A_77) = k2_xboole_0(A_77,B_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_60])).

tff(c_259,plain,(
    ! [A_77] : k2_xboole_0(k1_xboole_0,A_77) = A_77 ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_38])).

tff(c_455,plain,(
    ! [A_106,B_107] : k2_xboole_0(A_106,k4_xboole_0(B_107,A_106)) = k2_xboole_0(A_106,B_107) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_462,plain,(
    ! [B_107] : k4_xboole_0(B_107,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_455,c_259])).

tff(c_490,plain,(
    ! [B_111] : k4_xboole_0(B_111,k1_xboole_0) = B_111 ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_462])).

tff(c_8,plain,(
    ! [D_10,B_6,A_5] :
      ( ~ r2_hidden(D_10,B_6)
      | ~ r2_hidden(D_10,k4_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_567,plain,(
    ! [D_116,B_117] :
      ( ~ r2_hidden(D_116,k1_xboole_0)
      | ~ r2_hidden(D_116,B_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_490,c_8])).

tff(c_579,plain,(
    ! [B_117] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0),B_117)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_567])).

tff(c_615,plain,(
    ! [B_119] : ~ r2_hidden('#skF_1'(k1_xboole_0),B_119) ),
    inference(splitLeft,[status(thm)],[c_579])).

tff(c_630,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_363,c_615])).

tff(c_631,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_579])).

tff(c_907,plain,(
    ! [A_151,B_152,C_153] :
      ( r2_hidden('#skF_2'(A_151,B_152,C_153),A_151)
      | r2_hidden('#skF_3'(A_151,B_152,C_153),C_153)
      | k4_xboole_0(A_151,B_152) = C_153 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_5,B_6,C_7] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6,C_7),B_6)
      | r2_hidden('#skF_3'(A_5,B_6,C_7),C_7)
      | k4_xboole_0(A_5,B_6) = C_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_985,plain,(
    ! [A_158,C_159] :
      ( r2_hidden('#skF_3'(A_158,A_158,C_159),C_159)
      | k4_xboole_0(A_158,A_158) = C_159 ) ),
    inference(resolution,[status(thm)],[c_907,c_20])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1015,plain,(
    ! [C_163,A_164] :
      ( ~ v1_xboole_0(C_163)
      | k4_xboole_0(A_164,A_164) = C_163 ) ),
    inference(resolution,[status(thm)],[c_985,c_2])).

tff(c_1018,plain,(
    ! [A_164] : k4_xboole_0(A_164,A_164) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_631,c_1015])).

tff(c_46,plain,(
    ! [A_25,B_26] :
      ( r1_xboole_0(A_25,B_26)
      | k4_xboole_0(A_25,B_26) != A_25 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_701,plain,(
    ! [A_125,B_126,C_127] :
      ( ~ r1_xboole_0(A_125,B_126)
      | ~ r2_hidden(C_127,B_126)
      | ~ r2_hidden(C_127,A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1232,plain,(
    ! [C_182,B_183,A_184] :
      ( ~ r2_hidden(C_182,B_183)
      | ~ r2_hidden(C_182,A_184)
      | k4_xboole_0(A_184,B_183) != A_184 ) ),
    inference(resolution,[status(thm)],[c_46,c_701])).

tff(c_2620,plain,(
    ! [A_280,A_281] :
      ( ~ r2_hidden('#skF_1'(A_280),A_281)
      | k4_xboole_0(A_281,A_280) != A_281
      | v1_xboole_0(A_280) ) ),
    inference(resolution,[status(thm)],[c_4,c_1232])).

tff(c_2642,plain,(
    ! [A_1] :
      ( k4_xboole_0(A_1,A_1) != A_1
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_2620])).

tff(c_2652,plain,(
    ! [A_282] :
      ( k1_xboole_0 != A_282
      | v1_xboole_0(A_282) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1018,c_2642])).

tff(c_474,plain,(
    ! [D_108,A_109,B_110] :
      ( r2_hidden(D_108,A_109)
      | ~ r2_hidden(D_108,k4_xboole_0(A_109,B_110)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1492,plain,(
    ! [A_199,B_200] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_199,B_200)),A_199)
      | v1_xboole_0(k4_xboole_0(A_199,B_200)) ) ),
    inference(resolution,[status(thm)],[c_4,c_474])).

tff(c_1535,plain,(
    ! [A_201,B_202] :
      ( ~ v1_xboole_0(A_201)
      | v1_xboole_0(k4_xboole_0(A_201,B_202)) ) ),
    inference(resolution,[status(thm)],[c_1492,c_2])).

tff(c_1003,plain,(
    ! [C_159,A_158] :
      ( ~ v1_xboole_0(C_159)
      | k4_xboole_0(A_158,A_158) = C_159 ) ),
    inference(resolution,[status(thm)],[c_985,c_2])).

tff(c_1019,plain,(
    ! [C_159] :
      ( ~ v1_xboole_0(C_159)
      | k1_xboole_0 = C_159 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1018,c_1003])).

tff(c_1552,plain,(
    ! [A_201,B_202] :
      ( k4_xboole_0(A_201,B_202) = k1_xboole_0
      | ~ v1_xboole_0(A_201) ) ),
    inference(resolution,[status(thm)],[c_1535,c_1019])).

tff(c_3515,plain,(
    ! [A_306,B_307] :
      ( k4_xboole_0(A_306,B_307) = k1_xboole_0
      | k1_xboole_0 != A_306 ) ),
    inference(resolution,[status(thm)],[c_2652,c_1552])).

tff(c_42,plain,(
    ! [A_23,B_24] : k2_xboole_0(A_23,k4_xboole_0(B_24,A_23)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3665,plain,(
    ! [B_307,A_306] :
      ( k2_xboole_0(B_307,k1_xboole_0) = k2_xboole_0(B_307,A_306)
      | k1_xboole_0 != A_306 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3515,c_42])).

tff(c_3777,plain,(
    ! [B_307] : k2_xboole_0(B_307,k1_xboole_0) = B_307 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_3665])).

tff(c_184,plain,(
    ! [A_63,B_64] :
      ( k3_xboole_0(A_63,B_64) = A_63
      | ~ r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_188,plain,(
    ! [B_17] : k3_xboole_0(B_17,B_17) = B_17 ),
    inference(resolution,[status(thm)],[c_34,c_184])).

tff(c_329,plain,(
    ! [A_79,B_80] : k5_xboole_0(A_79,k3_xboole_0(A_79,B_80)) = k4_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_338,plain,(
    ! [B_17] : k5_xboole_0(B_17,B_17) = k4_xboole_0(B_17,B_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_329])).

tff(c_52,plain,(
    ! [A_31] : k2_tarski(A_31,A_31) = k1_tarski(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_850,plain,(
    ! [A_142,B_143,C_144] :
      ( r1_tarski(k2_tarski(A_142,B_143),C_144)
      | ~ r2_hidden(B_143,C_144)
      | ~ r2_hidden(A_142,C_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_946,plain,(
    ! [A_154,C_155] :
      ( r1_tarski(k1_tarski(A_154),C_155)
      | ~ r2_hidden(A_154,C_155)
      | ~ r2_hidden(A_154,C_155) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_850])).

tff(c_40,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = A_21
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_958,plain,(
    ! [A_156,C_157] :
      ( k3_xboole_0(k1_tarski(A_156),C_157) = k1_tarski(A_156)
      | ~ r2_hidden(A_156,C_157) ) ),
    inference(resolution,[status(thm)],[c_946,c_40])).

tff(c_36,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k3_xboole_0(A_18,B_19)) = k4_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_964,plain,(
    ! [A_156,C_157] :
      ( k5_xboole_0(k1_tarski(A_156),k1_tarski(A_156)) = k4_xboole_0(k1_tarski(A_156),C_157)
      | ~ r2_hidden(A_156,C_157) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_958,c_36])).

tff(c_977,plain,(
    ! [A_156,C_157] :
      ( k4_xboole_0(k1_tarski(A_156),k1_tarski(A_156)) = k4_xboole_0(k1_tarski(A_156),C_157)
      | ~ r2_hidden(A_156,C_157) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_964])).

tff(c_130908,plain,(
    ! [A_1816,C_1817] :
      ( k4_xboole_0(k1_tarski(A_1816),C_1817) = k1_xboole_0
      | ~ r2_hidden(A_1816,C_1817) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1018,c_977])).

tff(c_132101,plain,(
    ! [C_1817,A_1816] :
      ( k2_xboole_0(C_1817,k1_tarski(A_1816)) = k2_xboole_0(C_1817,k1_xboole_0)
      | ~ r2_hidden(A_1816,C_1817) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130908,c_42])).

tff(c_132539,plain,(
    ! [C_1818,A_1819] :
      ( k2_xboole_0(C_1818,k1_tarski(A_1819)) = C_1818
      | ~ r2_hidden(A_1819,C_1818) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3777,c_132101])).

tff(c_222,plain,(
    ! [B_74,A_75] : k2_xboole_0(B_74,A_75) = k2_xboole_0(A_75,B_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_60])).

tff(c_68,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_242,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_68])).

tff(c_132776,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_132539,c_242])).

tff(c_132903,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_132776])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:10:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 38.67/28.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 38.67/28.20  
% 38.67/28.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 38.67/28.20  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 38.67/28.20  
% 38.67/28.20  %Foreground sorts:
% 38.67/28.20  
% 38.67/28.20  
% 38.67/28.20  %Background operators:
% 38.67/28.20  
% 38.67/28.20  
% 38.67/28.20  %Foreground operators:
% 38.67/28.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 38.67/28.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 38.67/28.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 38.67/28.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 38.67/28.20  tff('#skF_1', type, '#skF_1': $i > $i).
% 38.67/28.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 38.67/28.20  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 38.67/28.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 38.67/28.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 38.67/28.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 38.67/28.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 38.67/28.20  tff('#skF_5', type, '#skF_5': $i).
% 38.67/28.20  tff('#skF_6', type, '#skF_6': $i).
% 38.67/28.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 38.67/28.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 38.67/28.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 38.67/28.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 38.67/28.20  tff(k3_tarski, type, k3_tarski: $i > $i).
% 38.67/28.20  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 38.67/28.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 38.67/28.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 38.67/28.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 38.67/28.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 38.67/28.20  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 38.67/28.20  
% 38.67/28.22  tff(f_104, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 38.67/28.22  tff(f_69, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 38.67/28.22  tff(f_83, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 38.67/28.22  tff(f_65, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 38.67/28.22  tff(f_99, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 38.67/28.22  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 38.67/28.22  tff(f_93, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 38.67/28.22  tff(f_75, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 38.67/28.22  tff(f_41, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 38.67/28.22  tff(f_79, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 38.67/28.22  tff(f_59, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 38.67/28.22  tff(f_73, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 38.67/28.22  tff(f_67, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 38.67/28.22  tff(f_85, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 38.67/28.22  tff(c_70, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_104])).
% 38.67/28.22  tff(c_38, plain, (![A_20]: (k2_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_69])).
% 38.67/28.22  tff(c_50, plain, (![B_30, A_29]: (k2_tarski(B_30, A_29)=k2_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_83])).
% 38.67/28.22  tff(c_34, plain, (![B_17]: (r1_tarski(B_17, B_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 38.67/28.22  tff(c_342, plain, (![A_81, C_82, B_83]: (r2_hidden(A_81, C_82) | ~r1_tarski(k2_tarski(A_81, B_83), C_82))), inference(cnfTransformation, [status(thm)], [f_99])).
% 38.67/28.22  tff(c_357, plain, (![A_84, B_85]: (r2_hidden(A_84, k2_tarski(A_84, B_85)))), inference(resolution, [status(thm)], [c_34, c_342])).
% 38.67/28.22  tff(c_363, plain, (![A_29, B_30]: (r2_hidden(A_29, k2_tarski(B_30, A_29)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_357])).
% 38.67/28.22  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 38.67/28.22  tff(c_134, plain, (![A_54, B_55]: (k3_tarski(k2_tarski(A_54, B_55))=k2_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_93])).
% 38.67/28.22  tff(c_216, plain, (![B_74, A_75]: (k3_tarski(k2_tarski(B_74, A_75))=k2_xboole_0(A_75, B_74))), inference(superposition, [status(thm), theory('equality')], [c_50, c_134])).
% 38.67/28.22  tff(c_60, plain, (![A_41, B_42]: (k3_tarski(k2_tarski(A_41, B_42))=k2_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_93])).
% 38.67/28.22  tff(c_243, plain, (![B_76, A_77]: (k2_xboole_0(B_76, A_77)=k2_xboole_0(A_77, B_76))), inference(superposition, [status(thm), theory('equality')], [c_216, c_60])).
% 38.67/28.22  tff(c_259, plain, (![A_77]: (k2_xboole_0(k1_xboole_0, A_77)=A_77)), inference(superposition, [status(thm), theory('equality')], [c_243, c_38])).
% 38.67/28.22  tff(c_455, plain, (![A_106, B_107]: (k2_xboole_0(A_106, k4_xboole_0(B_107, A_106))=k2_xboole_0(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_75])).
% 38.67/28.22  tff(c_462, plain, (![B_107]: (k4_xboole_0(B_107, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_107))), inference(superposition, [status(thm), theory('equality')], [c_455, c_259])).
% 38.67/28.22  tff(c_490, plain, (![B_111]: (k4_xboole_0(B_111, k1_xboole_0)=B_111)), inference(demodulation, [status(thm), theory('equality')], [c_259, c_462])).
% 38.67/28.22  tff(c_8, plain, (![D_10, B_6, A_5]: (~r2_hidden(D_10, B_6) | ~r2_hidden(D_10, k4_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 38.67/28.22  tff(c_567, plain, (![D_116, B_117]: (~r2_hidden(D_116, k1_xboole_0) | ~r2_hidden(D_116, B_117))), inference(superposition, [status(thm), theory('equality')], [c_490, c_8])).
% 38.67/28.22  tff(c_579, plain, (![B_117]: (~r2_hidden('#skF_1'(k1_xboole_0), B_117) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_567])).
% 38.67/28.22  tff(c_615, plain, (![B_119]: (~r2_hidden('#skF_1'(k1_xboole_0), B_119))), inference(splitLeft, [status(thm)], [c_579])).
% 38.67/28.22  tff(c_630, plain, $false, inference(resolution, [status(thm)], [c_363, c_615])).
% 38.67/28.22  tff(c_631, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_579])).
% 38.67/28.22  tff(c_907, plain, (![A_151, B_152, C_153]: (r2_hidden('#skF_2'(A_151, B_152, C_153), A_151) | r2_hidden('#skF_3'(A_151, B_152, C_153), C_153) | k4_xboole_0(A_151, B_152)=C_153)), inference(cnfTransformation, [status(thm)], [f_41])).
% 38.67/28.22  tff(c_20, plain, (![A_5, B_6, C_7]: (~r2_hidden('#skF_2'(A_5, B_6, C_7), B_6) | r2_hidden('#skF_3'(A_5, B_6, C_7), C_7) | k4_xboole_0(A_5, B_6)=C_7)), inference(cnfTransformation, [status(thm)], [f_41])).
% 38.67/28.22  tff(c_985, plain, (![A_158, C_159]: (r2_hidden('#skF_3'(A_158, A_158, C_159), C_159) | k4_xboole_0(A_158, A_158)=C_159)), inference(resolution, [status(thm)], [c_907, c_20])).
% 38.67/28.22  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 38.67/28.22  tff(c_1015, plain, (![C_163, A_164]: (~v1_xboole_0(C_163) | k4_xboole_0(A_164, A_164)=C_163)), inference(resolution, [status(thm)], [c_985, c_2])).
% 38.67/28.22  tff(c_1018, plain, (![A_164]: (k4_xboole_0(A_164, A_164)=k1_xboole_0)), inference(resolution, [status(thm)], [c_631, c_1015])).
% 38.67/28.22  tff(c_46, plain, (![A_25, B_26]: (r1_xboole_0(A_25, B_26) | k4_xboole_0(A_25, B_26)!=A_25)), inference(cnfTransformation, [status(thm)], [f_79])).
% 38.67/28.22  tff(c_701, plain, (![A_125, B_126, C_127]: (~r1_xboole_0(A_125, B_126) | ~r2_hidden(C_127, B_126) | ~r2_hidden(C_127, A_125))), inference(cnfTransformation, [status(thm)], [f_59])).
% 38.67/28.22  tff(c_1232, plain, (![C_182, B_183, A_184]: (~r2_hidden(C_182, B_183) | ~r2_hidden(C_182, A_184) | k4_xboole_0(A_184, B_183)!=A_184)), inference(resolution, [status(thm)], [c_46, c_701])).
% 38.67/28.22  tff(c_2620, plain, (![A_280, A_281]: (~r2_hidden('#skF_1'(A_280), A_281) | k4_xboole_0(A_281, A_280)!=A_281 | v1_xboole_0(A_280))), inference(resolution, [status(thm)], [c_4, c_1232])).
% 38.67/28.22  tff(c_2642, plain, (![A_1]: (k4_xboole_0(A_1, A_1)!=A_1 | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_2620])).
% 38.67/28.22  tff(c_2652, plain, (![A_282]: (k1_xboole_0!=A_282 | v1_xboole_0(A_282))), inference(demodulation, [status(thm), theory('equality')], [c_1018, c_2642])).
% 38.67/28.22  tff(c_474, plain, (![D_108, A_109, B_110]: (r2_hidden(D_108, A_109) | ~r2_hidden(D_108, k4_xboole_0(A_109, B_110)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 38.67/28.22  tff(c_1492, plain, (![A_199, B_200]: (r2_hidden('#skF_1'(k4_xboole_0(A_199, B_200)), A_199) | v1_xboole_0(k4_xboole_0(A_199, B_200)))), inference(resolution, [status(thm)], [c_4, c_474])).
% 38.67/28.22  tff(c_1535, plain, (![A_201, B_202]: (~v1_xboole_0(A_201) | v1_xboole_0(k4_xboole_0(A_201, B_202)))), inference(resolution, [status(thm)], [c_1492, c_2])).
% 38.67/28.22  tff(c_1003, plain, (![C_159, A_158]: (~v1_xboole_0(C_159) | k4_xboole_0(A_158, A_158)=C_159)), inference(resolution, [status(thm)], [c_985, c_2])).
% 38.67/28.22  tff(c_1019, plain, (![C_159]: (~v1_xboole_0(C_159) | k1_xboole_0=C_159)), inference(demodulation, [status(thm), theory('equality')], [c_1018, c_1003])).
% 38.67/28.22  tff(c_1552, plain, (![A_201, B_202]: (k4_xboole_0(A_201, B_202)=k1_xboole_0 | ~v1_xboole_0(A_201))), inference(resolution, [status(thm)], [c_1535, c_1019])).
% 38.67/28.22  tff(c_3515, plain, (![A_306, B_307]: (k4_xboole_0(A_306, B_307)=k1_xboole_0 | k1_xboole_0!=A_306)), inference(resolution, [status(thm)], [c_2652, c_1552])).
% 38.67/28.22  tff(c_42, plain, (![A_23, B_24]: (k2_xboole_0(A_23, k4_xboole_0(B_24, A_23))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_75])).
% 38.67/28.22  tff(c_3665, plain, (![B_307, A_306]: (k2_xboole_0(B_307, k1_xboole_0)=k2_xboole_0(B_307, A_306) | k1_xboole_0!=A_306)), inference(superposition, [status(thm), theory('equality')], [c_3515, c_42])).
% 38.67/28.22  tff(c_3777, plain, (![B_307]: (k2_xboole_0(B_307, k1_xboole_0)=B_307)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_3665])).
% 38.67/28.22  tff(c_184, plain, (![A_63, B_64]: (k3_xboole_0(A_63, B_64)=A_63 | ~r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_73])).
% 38.67/28.22  tff(c_188, plain, (![B_17]: (k3_xboole_0(B_17, B_17)=B_17)), inference(resolution, [status(thm)], [c_34, c_184])).
% 38.67/28.22  tff(c_329, plain, (![A_79, B_80]: (k5_xboole_0(A_79, k3_xboole_0(A_79, B_80))=k4_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_67])).
% 38.67/28.22  tff(c_338, plain, (![B_17]: (k5_xboole_0(B_17, B_17)=k4_xboole_0(B_17, B_17))), inference(superposition, [status(thm), theory('equality')], [c_188, c_329])).
% 38.67/28.22  tff(c_52, plain, (![A_31]: (k2_tarski(A_31, A_31)=k1_tarski(A_31))), inference(cnfTransformation, [status(thm)], [f_85])).
% 38.67/28.22  tff(c_850, plain, (![A_142, B_143, C_144]: (r1_tarski(k2_tarski(A_142, B_143), C_144) | ~r2_hidden(B_143, C_144) | ~r2_hidden(A_142, C_144))), inference(cnfTransformation, [status(thm)], [f_99])).
% 38.67/28.22  tff(c_946, plain, (![A_154, C_155]: (r1_tarski(k1_tarski(A_154), C_155) | ~r2_hidden(A_154, C_155) | ~r2_hidden(A_154, C_155))), inference(superposition, [status(thm), theory('equality')], [c_52, c_850])).
% 38.67/28.22  tff(c_40, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=A_21 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_73])).
% 38.67/28.22  tff(c_958, plain, (![A_156, C_157]: (k3_xboole_0(k1_tarski(A_156), C_157)=k1_tarski(A_156) | ~r2_hidden(A_156, C_157))), inference(resolution, [status(thm)], [c_946, c_40])).
% 38.67/28.22  tff(c_36, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k3_xboole_0(A_18, B_19))=k4_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 38.67/28.22  tff(c_964, plain, (![A_156, C_157]: (k5_xboole_0(k1_tarski(A_156), k1_tarski(A_156))=k4_xboole_0(k1_tarski(A_156), C_157) | ~r2_hidden(A_156, C_157))), inference(superposition, [status(thm), theory('equality')], [c_958, c_36])).
% 38.67/28.22  tff(c_977, plain, (![A_156, C_157]: (k4_xboole_0(k1_tarski(A_156), k1_tarski(A_156))=k4_xboole_0(k1_tarski(A_156), C_157) | ~r2_hidden(A_156, C_157))), inference(demodulation, [status(thm), theory('equality')], [c_338, c_964])).
% 38.67/28.22  tff(c_130908, plain, (![A_1816, C_1817]: (k4_xboole_0(k1_tarski(A_1816), C_1817)=k1_xboole_0 | ~r2_hidden(A_1816, C_1817))), inference(demodulation, [status(thm), theory('equality')], [c_1018, c_977])).
% 38.67/28.22  tff(c_132101, plain, (![C_1817, A_1816]: (k2_xboole_0(C_1817, k1_tarski(A_1816))=k2_xboole_0(C_1817, k1_xboole_0) | ~r2_hidden(A_1816, C_1817))), inference(superposition, [status(thm), theory('equality')], [c_130908, c_42])).
% 38.67/28.22  tff(c_132539, plain, (![C_1818, A_1819]: (k2_xboole_0(C_1818, k1_tarski(A_1819))=C_1818 | ~r2_hidden(A_1819, C_1818))), inference(demodulation, [status(thm), theory('equality')], [c_3777, c_132101])).
% 38.67/28.22  tff(c_222, plain, (![B_74, A_75]: (k2_xboole_0(B_74, A_75)=k2_xboole_0(A_75, B_74))), inference(superposition, [status(thm), theory('equality')], [c_216, c_60])).
% 38.67/28.22  tff(c_68, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_104])).
% 38.67/28.22  tff(c_242, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_222, c_68])).
% 38.67/28.22  tff(c_132776, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_132539, c_242])).
% 38.67/28.22  tff(c_132903, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_132776])).
% 38.67/28.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 38.67/28.22  
% 38.67/28.22  Inference rules
% 38.67/28.22  ----------------------
% 38.67/28.22  #Ref     : 8
% 38.67/28.22  #Sup     : 37295
% 38.67/28.22  #Fact    : 2
% 38.67/28.22  #Define  : 0
% 38.67/28.22  #Split   : 7
% 38.67/28.22  #Chain   : 0
% 38.67/28.22  #Close   : 0
% 38.67/28.22  
% 38.67/28.22  Ordering : KBO
% 38.67/28.22  
% 38.67/28.22  Simplification rules
% 38.67/28.22  ----------------------
% 38.67/28.22  #Subsume      : 21091
% 38.67/28.22  #Demod        : 12534
% 38.67/28.22  #Tautology    : 5219
% 38.67/28.22  #SimpNegUnit  : 345
% 38.67/28.22  #BackRed      : 33
% 38.67/28.22  
% 38.67/28.22  #Partial instantiations: 0
% 38.67/28.22  #Strategies tried      : 1
% 38.67/28.22  
% 38.67/28.22  Timing (in seconds)
% 38.67/28.22  ----------------------
% 38.67/28.22  Preprocessing        : 0.34
% 38.67/28.22  Parsing              : 0.18
% 38.67/28.22  CNF conversion       : 0.03
% 38.67/28.22  Main loop            : 27.11
% 38.67/28.22  Inferencing          : 3.13
% 38.67/28.22  Reduction            : 12.13
% 38.67/28.22  Demodulation         : 9.83
% 38.67/28.22  BG Simplification    : 0.35
% 38.67/28.22  Subsumption          : 10.56
% 38.67/28.22  Abstraction          : 0.56
% 38.67/28.22  MUC search           : 0.00
% 38.67/28.22  Cooper               : 0.00
% 38.67/28.22  Total                : 27.50
% 38.67/28.22  Index Insertion      : 0.00
% 38.67/28.22  Index Deletion       : 0.00
% 38.67/28.22  Index Matching       : 0.00
% 38.67/28.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
