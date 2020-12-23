%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:49 EST 2020

% Result     : Theorem 17.80s
% Output     : CNFRefutation 17.94s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 292 expanded)
%              Number of leaves         :   39 ( 114 expanded)
%              Depth                    :   16
%              Number of atoms          :  115 ( 369 expanded)
%              Number of equality atoms :   46 ( 199 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(f_107,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_78,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_88,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_102,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_84,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_86,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_76,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_100,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_82,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_56,plain,(
    ! [A_26] : k2_xboole_0(A_26,k1_xboole_0) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_791,plain,(
    ! [D_114,A_115,B_116] :
      ( r2_hidden(D_114,A_115)
      | ~ r2_hidden(D_114,k4_xboole_0(A_115,B_116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_804,plain,(
    ! [A_115,B_116] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_115,B_116)),A_115)
      | v1_xboole_0(k4_xboole_0(A_115,B_116)) ) ),
    inference(resolution,[status(thm)],[c_4,c_791])).

tff(c_948,plain,(
    ! [D_129,B_130,A_131] :
      ( ~ r2_hidden(D_129,B_130)
      | ~ r2_hidden(D_129,k4_xboole_0(A_131,B_130)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3802,plain,(
    ! [A_300,B_301] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_300,B_301)),B_301)
      | v1_xboole_0(k4_xboole_0(A_300,B_301)) ) ),
    inference(resolution,[status(thm)],[c_4,c_948])).

tff(c_3859,plain,(
    ! [A_302] : v1_xboole_0(k4_xboole_0(A_302,A_302)) ),
    inference(resolution,[status(thm)],[c_804,c_3802])).

tff(c_64,plain,(
    ! [B_34,A_33] : k2_tarski(B_34,A_33) = k2_tarski(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_152,plain,(
    ! [A_61,B_62] : k3_tarski(k2_tarski(A_61,B_62)) = k2_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_338,plain,(
    ! [B_89,A_90] : k3_tarski(k2_tarski(B_89,A_90)) = k2_xboole_0(A_90,B_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_152])).

tff(c_78,plain,(
    ! [A_47,B_48] : k3_tarski(k2_tarski(A_47,B_48)) = k2_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_365,plain,(
    ! [B_91,A_92] : k2_xboole_0(B_91,A_92) = k2_xboole_0(A_92,B_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_78])).

tff(c_409,plain,(
    ! [A_92] : k2_xboole_0(k1_xboole_0,A_92) = A_92 ),
    inference(superposition,[status(thm),theory(equality)],[c_365,c_56])).

tff(c_605,plain,(
    ! [A_103,B_104] : k2_xboole_0(A_103,k4_xboole_0(B_104,A_103)) = k2_xboole_0(A_103,B_104) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_615,plain,(
    ! [B_104] : k4_xboole_0(B_104,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_605,c_409])).

tff(c_638,plain,(
    ! [B_104] : k4_xboole_0(B_104,k1_xboole_0) = B_104 ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_615])).

tff(c_440,plain,(
    ! [A_93] : k2_xboole_0(k1_xboole_0,A_93) = A_93 ),
    inference(superposition,[status(thm),theory(equality)],[c_365,c_56])).

tff(c_62,plain,(
    ! [A_31,B_32] : r1_tarski(A_31,k2_xboole_0(A_31,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_215,plain,(
    ! [A_67,B_68] :
      ( k3_xboole_0(A_67,B_68) = A_67
      | ~ r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_230,plain,(
    ! [A_31,B_32] : k3_xboole_0(A_31,k2_xboole_0(A_31,B_32)) = A_31 ),
    inference(resolution,[status(thm)],[c_62,c_215])).

tff(c_452,plain,(
    ! [A_93] : k3_xboole_0(k1_xboole_0,A_93) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_230])).

tff(c_659,plain,(
    ! [A_106,B_107] : k5_xboole_0(A_106,k3_xboole_0(A_106,B_107)) = k4_xboole_0(A_106,B_107) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_825,plain,(
    ! [A_121] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_121) ),
    inference(superposition,[status(thm),theory(equality)],[c_452,c_659])).

tff(c_52,plain,(
    ! [B_23] : r1_tarski(B_23,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_231,plain,(
    ! [B_23] : k3_xboole_0(B_23,B_23) = B_23 ),
    inference(resolution,[status(thm)],[c_52,c_215])).

tff(c_677,plain,(
    ! [B_23] : k5_xboole_0(B_23,B_23) = k4_xboole_0(B_23,B_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_659])).

tff(c_834,plain,(
    ! [A_121] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_121) ),
    inference(superposition,[status(thm),theory(equality)],[c_825,c_677])).

tff(c_846,plain,(
    ! [A_121] : k4_xboole_0(k1_xboole_0,A_121) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_638,c_834])).

tff(c_1535,plain,(
    ! [A_185,B_186,C_187] :
      ( r2_hidden('#skF_4'(A_185,B_186,C_187),A_185)
      | r2_hidden('#skF_5'(A_185,B_186,C_187),C_187)
      | k4_xboole_0(A_185,B_186) = C_187 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_876,plain,(
    ! [D_123,B_124,A_125] :
      ( r2_hidden(D_123,B_124)
      | ~ r2_hidden(D_123,k3_xboole_0(A_125,B_124)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1131,plain,(
    ! [D_148,A_149,B_150] :
      ( r2_hidden(D_148,k2_xboole_0(A_149,B_150))
      | ~ r2_hidden(D_148,A_149) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_876])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1154,plain,(
    ! [A_151,B_152,D_153] :
      ( ~ v1_xboole_0(k2_xboole_0(A_151,B_152))
      | ~ r2_hidden(D_153,A_151) ) ),
    inference(resolution,[status(thm)],[c_1131,c_2])).

tff(c_1158,plain,(
    ! [A_92,D_153] :
      ( ~ v1_xboole_0(A_92)
      | ~ r2_hidden(D_153,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_1154])).

tff(c_1176,plain,(
    ! [D_153] : ~ r2_hidden(D_153,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1158])).

tff(c_1539,plain,(
    ! [B_186,C_187] :
      ( r2_hidden('#skF_5'(k1_xboole_0,B_186,C_187),C_187)
      | k4_xboole_0(k1_xboole_0,B_186) = C_187 ) ),
    inference(resolution,[status(thm)],[c_1535,c_1176])).

tff(c_1628,plain,(
    ! [B_191,C_192] :
      ( r2_hidden('#skF_5'(k1_xboole_0,B_191,C_192),C_192)
      | k1_xboole_0 = C_192 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_846,c_1539])).

tff(c_1658,plain,(
    ! [C_192] :
      ( ~ v1_xboole_0(C_192)
      | k1_xboole_0 = C_192 ) ),
    inference(resolution,[status(thm)],[c_1628,c_2])).

tff(c_3891,plain,(
    ! [A_302] : k4_xboole_0(A_302,A_302) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3859,c_1658])).

tff(c_76,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(k1_tarski(A_45),B_46)
      | ~ r2_hidden(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1783,plain,(
    ! [A_201,B_202] :
      ( k3_xboole_0(k1_tarski(A_201),B_202) = k1_tarski(A_201)
      | ~ r2_hidden(A_201,B_202) ) ),
    inference(resolution,[status(thm)],[c_76,c_215])).

tff(c_54,plain,(
    ! [A_24,B_25] : k5_xboole_0(A_24,k3_xboole_0(A_24,B_25)) = k4_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1799,plain,(
    ! [A_201,B_202] :
      ( k5_xboole_0(k1_tarski(A_201),k1_tarski(A_201)) = k4_xboole_0(k1_tarski(A_201),B_202)
      | ~ r2_hidden(A_201,B_202) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1783,c_54])).

tff(c_1838,plain,(
    ! [A_201,B_202] :
      ( k4_xboole_0(k1_tarski(A_201),k1_tarski(A_201)) = k4_xboole_0(k1_tarski(A_201),B_202)
      | ~ r2_hidden(A_201,B_202) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_677,c_1799])).

tff(c_57813,plain,(
    ! [A_1415,B_1416] :
      ( k4_xboole_0(k1_tarski(A_1415),B_1416) = k1_xboole_0
      | ~ r2_hidden(A_1415,B_1416) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3891,c_1838])).

tff(c_60,plain,(
    ! [A_29,B_30] : k2_xboole_0(A_29,k4_xboole_0(B_30,A_29)) = k2_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_58310,plain,(
    ! [B_1416,A_1415] :
      ( k2_xboole_0(B_1416,k1_tarski(A_1415)) = k2_xboole_0(B_1416,k1_xboole_0)
      | ~ r2_hidden(A_1415,B_1416) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57813,c_60])).

tff(c_58464,plain,(
    ! [B_1417,A_1418] :
      ( k2_xboole_0(B_1417,k1_tarski(A_1418)) = B_1417
      | ~ r2_hidden(A_1418,B_1417) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58310])).

tff(c_344,plain,(
    ! [B_89,A_90] : k2_xboole_0(B_89,A_90) = k2_xboole_0(A_90,B_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_78])).

tff(c_80,plain,(
    k2_xboole_0(k1_tarski('#skF_7'),'#skF_8') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_364,plain,(
    k2_xboole_0('#skF_8',k1_tarski('#skF_7')) != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_80])).

tff(c_58939,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_58464,c_364])).

tff(c_59066,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_58939])).

tff(c_59067,plain,(
    ! [A_92] : ~ v1_xboole_0(A_92) ),
    inference(splitRight,[status(thm)],[c_1158])).

tff(c_919,plain,(
    ! [D_126,A_127] :
      ( r2_hidden(D_126,A_127)
      | ~ r2_hidden(D_126,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_452,c_876])).

tff(c_931,plain,(
    ! [A_127] :
      ( r2_hidden('#skF_1'(k1_xboole_0),A_127)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_919])).

tff(c_984,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_931])).

tff(c_59070,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59067,c_984])).

tff(c_59071,plain,(
    ! [A_127] : r2_hidden('#skF_1'(k1_xboole_0),A_127) ),
    inference(splitRight,[status(thm)],[c_931])).

tff(c_59080,plain,(
    ! [A_1422] : r2_hidden('#skF_1'(k1_xboole_0),A_1422) ),
    inference(splitRight,[status(thm)],[c_931])).

tff(c_958,plain,(
    ! [D_129,B_104] :
      ( ~ r2_hidden(D_129,k1_xboole_0)
      | ~ r2_hidden(D_129,B_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_638,c_948])).

tff(c_59083,plain,(
    ! [B_104] : ~ r2_hidden('#skF_1'(k1_xboole_0),B_104) ),
    inference(resolution,[status(thm)],[c_59080,c_958])).

tff(c_59113,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59071,c_59083])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:37:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.80/10.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.80/10.04  
% 17.80/10.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.80/10.04  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_8 > #skF_3
% 17.80/10.04  
% 17.80/10.04  %Foreground sorts:
% 17.80/10.04  
% 17.80/10.04  
% 17.80/10.04  %Background operators:
% 17.80/10.04  
% 17.80/10.04  
% 17.80/10.04  %Foreground operators:
% 17.80/10.04  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 17.80/10.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.80/10.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.80/10.04  tff(k1_tarski, type, k1_tarski: $i > $i).
% 17.80/10.04  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 17.80/10.04  tff('#skF_1', type, '#skF_1': $i > $i).
% 17.80/10.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.80/10.04  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 17.80/10.04  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 17.80/10.04  tff('#skF_7', type, '#skF_7': $i).
% 17.80/10.04  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 17.80/10.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.80/10.04  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 17.80/10.04  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 17.80/10.04  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 17.80/10.04  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 17.80/10.04  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 17.80/10.04  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 17.80/10.04  tff('#skF_8', type, '#skF_8': $i).
% 17.80/10.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.80/10.04  tff(k3_tarski, type, k3_tarski: $i > $i).
% 17.80/10.04  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 17.80/10.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.80/10.04  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 17.80/10.04  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 17.80/10.04  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 17.80/10.04  
% 17.94/10.06  tff(f_107, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 17.94/10.06  tff(f_78, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 17.94/10.06  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 17.94/10.06  tff(f_50, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 17.94/10.06  tff(f_88, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 17.94/10.06  tff(f_102, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 17.94/10.06  tff(f_84, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 17.94/10.06  tff(f_86, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 17.94/10.06  tff(f_82, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 17.94/10.06  tff(f_76, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 17.94/10.06  tff(f_74, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 17.94/10.06  tff(f_40, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 17.94/10.06  tff(f_100, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 17.94/10.06  tff(c_82, plain, (r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_107])).
% 17.94/10.06  tff(c_56, plain, (![A_26]: (k2_xboole_0(A_26, k1_xboole_0)=A_26)), inference(cnfTransformation, [status(thm)], [f_78])).
% 17.94/10.06  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 17.94/10.06  tff(c_791, plain, (![D_114, A_115, B_116]: (r2_hidden(D_114, A_115) | ~r2_hidden(D_114, k4_xboole_0(A_115, B_116)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 17.94/10.06  tff(c_804, plain, (![A_115, B_116]: (r2_hidden('#skF_1'(k4_xboole_0(A_115, B_116)), A_115) | v1_xboole_0(k4_xboole_0(A_115, B_116)))), inference(resolution, [status(thm)], [c_4, c_791])).
% 17.94/10.06  tff(c_948, plain, (![D_129, B_130, A_131]: (~r2_hidden(D_129, B_130) | ~r2_hidden(D_129, k4_xboole_0(A_131, B_130)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 17.94/10.06  tff(c_3802, plain, (![A_300, B_301]: (~r2_hidden('#skF_1'(k4_xboole_0(A_300, B_301)), B_301) | v1_xboole_0(k4_xboole_0(A_300, B_301)))), inference(resolution, [status(thm)], [c_4, c_948])).
% 17.94/10.06  tff(c_3859, plain, (![A_302]: (v1_xboole_0(k4_xboole_0(A_302, A_302)))), inference(resolution, [status(thm)], [c_804, c_3802])).
% 17.94/10.06  tff(c_64, plain, (![B_34, A_33]: (k2_tarski(B_34, A_33)=k2_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_88])).
% 17.94/10.06  tff(c_152, plain, (![A_61, B_62]: (k3_tarski(k2_tarski(A_61, B_62))=k2_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_102])).
% 17.94/10.06  tff(c_338, plain, (![B_89, A_90]: (k3_tarski(k2_tarski(B_89, A_90))=k2_xboole_0(A_90, B_89))), inference(superposition, [status(thm), theory('equality')], [c_64, c_152])).
% 17.94/10.06  tff(c_78, plain, (![A_47, B_48]: (k3_tarski(k2_tarski(A_47, B_48))=k2_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_102])).
% 17.94/10.06  tff(c_365, plain, (![B_91, A_92]: (k2_xboole_0(B_91, A_92)=k2_xboole_0(A_92, B_91))), inference(superposition, [status(thm), theory('equality')], [c_338, c_78])).
% 17.94/10.06  tff(c_409, plain, (![A_92]: (k2_xboole_0(k1_xboole_0, A_92)=A_92)), inference(superposition, [status(thm), theory('equality')], [c_365, c_56])).
% 17.94/10.06  tff(c_605, plain, (![A_103, B_104]: (k2_xboole_0(A_103, k4_xboole_0(B_104, A_103))=k2_xboole_0(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_84])).
% 17.94/10.06  tff(c_615, plain, (![B_104]: (k4_xboole_0(B_104, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_104))), inference(superposition, [status(thm), theory('equality')], [c_605, c_409])).
% 17.94/10.06  tff(c_638, plain, (![B_104]: (k4_xboole_0(B_104, k1_xboole_0)=B_104)), inference(demodulation, [status(thm), theory('equality')], [c_409, c_615])).
% 17.94/10.06  tff(c_440, plain, (![A_93]: (k2_xboole_0(k1_xboole_0, A_93)=A_93)), inference(superposition, [status(thm), theory('equality')], [c_365, c_56])).
% 17.94/10.06  tff(c_62, plain, (![A_31, B_32]: (r1_tarski(A_31, k2_xboole_0(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 17.94/10.06  tff(c_215, plain, (![A_67, B_68]: (k3_xboole_0(A_67, B_68)=A_67 | ~r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_82])).
% 17.94/10.06  tff(c_230, plain, (![A_31, B_32]: (k3_xboole_0(A_31, k2_xboole_0(A_31, B_32))=A_31)), inference(resolution, [status(thm)], [c_62, c_215])).
% 17.94/10.06  tff(c_452, plain, (![A_93]: (k3_xboole_0(k1_xboole_0, A_93)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_440, c_230])).
% 17.94/10.06  tff(c_659, plain, (![A_106, B_107]: (k5_xboole_0(A_106, k3_xboole_0(A_106, B_107))=k4_xboole_0(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_76])).
% 17.94/10.06  tff(c_825, plain, (![A_121]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_121))), inference(superposition, [status(thm), theory('equality')], [c_452, c_659])).
% 17.94/10.06  tff(c_52, plain, (![B_23]: (r1_tarski(B_23, B_23))), inference(cnfTransformation, [status(thm)], [f_74])).
% 17.94/10.06  tff(c_231, plain, (![B_23]: (k3_xboole_0(B_23, B_23)=B_23)), inference(resolution, [status(thm)], [c_52, c_215])).
% 17.94/10.06  tff(c_677, plain, (![B_23]: (k5_xboole_0(B_23, B_23)=k4_xboole_0(B_23, B_23))), inference(superposition, [status(thm), theory('equality')], [c_231, c_659])).
% 17.94/10.06  tff(c_834, plain, (![A_121]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_121))), inference(superposition, [status(thm), theory('equality')], [c_825, c_677])).
% 17.94/10.06  tff(c_846, plain, (![A_121]: (k4_xboole_0(k1_xboole_0, A_121)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_638, c_834])).
% 17.94/10.06  tff(c_1535, plain, (![A_185, B_186, C_187]: (r2_hidden('#skF_4'(A_185, B_186, C_187), A_185) | r2_hidden('#skF_5'(A_185, B_186, C_187), C_187) | k4_xboole_0(A_185, B_186)=C_187)), inference(cnfTransformation, [status(thm)], [f_50])).
% 17.94/10.06  tff(c_876, plain, (![D_123, B_124, A_125]: (r2_hidden(D_123, B_124) | ~r2_hidden(D_123, k3_xboole_0(A_125, B_124)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 17.94/10.06  tff(c_1131, plain, (![D_148, A_149, B_150]: (r2_hidden(D_148, k2_xboole_0(A_149, B_150)) | ~r2_hidden(D_148, A_149))), inference(superposition, [status(thm), theory('equality')], [c_230, c_876])).
% 17.94/10.06  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 17.94/10.06  tff(c_1154, plain, (![A_151, B_152, D_153]: (~v1_xboole_0(k2_xboole_0(A_151, B_152)) | ~r2_hidden(D_153, A_151))), inference(resolution, [status(thm)], [c_1131, c_2])).
% 17.94/10.06  tff(c_1158, plain, (![A_92, D_153]: (~v1_xboole_0(A_92) | ~r2_hidden(D_153, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_409, c_1154])).
% 17.94/10.06  tff(c_1176, plain, (![D_153]: (~r2_hidden(D_153, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_1158])).
% 17.94/10.06  tff(c_1539, plain, (![B_186, C_187]: (r2_hidden('#skF_5'(k1_xboole_0, B_186, C_187), C_187) | k4_xboole_0(k1_xboole_0, B_186)=C_187)), inference(resolution, [status(thm)], [c_1535, c_1176])).
% 17.94/10.06  tff(c_1628, plain, (![B_191, C_192]: (r2_hidden('#skF_5'(k1_xboole_0, B_191, C_192), C_192) | k1_xboole_0=C_192)), inference(demodulation, [status(thm), theory('equality')], [c_846, c_1539])).
% 17.94/10.06  tff(c_1658, plain, (![C_192]: (~v1_xboole_0(C_192) | k1_xboole_0=C_192)), inference(resolution, [status(thm)], [c_1628, c_2])).
% 17.94/10.06  tff(c_3891, plain, (![A_302]: (k4_xboole_0(A_302, A_302)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3859, c_1658])).
% 17.94/10.06  tff(c_76, plain, (![A_45, B_46]: (r1_tarski(k1_tarski(A_45), B_46) | ~r2_hidden(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_100])).
% 17.94/10.06  tff(c_1783, plain, (![A_201, B_202]: (k3_xboole_0(k1_tarski(A_201), B_202)=k1_tarski(A_201) | ~r2_hidden(A_201, B_202))), inference(resolution, [status(thm)], [c_76, c_215])).
% 17.94/10.06  tff(c_54, plain, (![A_24, B_25]: (k5_xboole_0(A_24, k3_xboole_0(A_24, B_25))=k4_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_76])).
% 17.94/10.06  tff(c_1799, plain, (![A_201, B_202]: (k5_xboole_0(k1_tarski(A_201), k1_tarski(A_201))=k4_xboole_0(k1_tarski(A_201), B_202) | ~r2_hidden(A_201, B_202))), inference(superposition, [status(thm), theory('equality')], [c_1783, c_54])).
% 17.94/10.06  tff(c_1838, plain, (![A_201, B_202]: (k4_xboole_0(k1_tarski(A_201), k1_tarski(A_201))=k4_xboole_0(k1_tarski(A_201), B_202) | ~r2_hidden(A_201, B_202))), inference(demodulation, [status(thm), theory('equality')], [c_677, c_1799])).
% 17.94/10.06  tff(c_57813, plain, (![A_1415, B_1416]: (k4_xboole_0(k1_tarski(A_1415), B_1416)=k1_xboole_0 | ~r2_hidden(A_1415, B_1416))), inference(demodulation, [status(thm), theory('equality')], [c_3891, c_1838])).
% 17.94/10.06  tff(c_60, plain, (![A_29, B_30]: (k2_xboole_0(A_29, k4_xboole_0(B_30, A_29))=k2_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_84])).
% 17.94/10.06  tff(c_58310, plain, (![B_1416, A_1415]: (k2_xboole_0(B_1416, k1_tarski(A_1415))=k2_xboole_0(B_1416, k1_xboole_0) | ~r2_hidden(A_1415, B_1416))), inference(superposition, [status(thm), theory('equality')], [c_57813, c_60])).
% 17.94/10.06  tff(c_58464, plain, (![B_1417, A_1418]: (k2_xboole_0(B_1417, k1_tarski(A_1418))=B_1417 | ~r2_hidden(A_1418, B_1417))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58310])).
% 17.94/10.06  tff(c_344, plain, (![B_89, A_90]: (k2_xboole_0(B_89, A_90)=k2_xboole_0(A_90, B_89))), inference(superposition, [status(thm), theory('equality')], [c_338, c_78])).
% 17.94/10.06  tff(c_80, plain, (k2_xboole_0(k1_tarski('#skF_7'), '#skF_8')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_107])).
% 17.94/10.06  tff(c_364, plain, (k2_xboole_0('#skF_8', k1_tarski('#skF_7'))!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_344, c_80])).
% 17.94/10.06  tff(c_58939, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_58464, c_364])).
% 17.94/10.06  tff(c_59066, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_58939])).
% 17.94/10.06  tff(c_59067, plain, (![A_92]: (~v1_xboole_0(A_92))), inference(splitRight, [status(thm)], [c_1158])).
% 17.94/10.06  tff(c_919, plain, (![D_126, A_127]: (r2_hidden(D_126, A_127) | ~r2_hidden(D_126, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_452, c_876])).
% 17.94/10.06  tff(c_931, plain, (![A_127]: (r2_hidden('#skF_1'(k1_xboole_0), A_127) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_919])).
% 17.94/10.06  tff(c_984, plain, (v1_xboole_0(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_931])).
% 17.94/10.06  tff(c_59070, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59067, c_984])).
% 17.94/10.06  tff(c_59071, plain, (![A_127]: (r2_hidden('#skF_1'(k1_xboole_0), A_127))), inference(splitRight, [status(thm)], [c_931])).
% 17.94/10.06  tff(c_59080, plain, (![A_1422]: (r2_hidden('#skF_1'(k1_xboole_0), A_1422))), inference(splitRight, [status(thm)], [c_931])).
% 17.94/10.06  tff(c_958, plain, (![D_129, B_104]: (~r2_hidden(D_129, k1_xboole_0) | ~r2_hidden(D_129, B_104))), inference(superposition, [status(thm), theory('equality')], [c_638, c_948])).
% 17.94/10.06  tff(c_59083, plain, (![B_104]: (~r2_hidden('#skF_1'(k1_xboole_0), B_104))), inference(resolution, [status(thm)], [c_59080, c_958])).
% 17.94/10.06  tff(c_59113, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59071, c_59083])).
% 17.94/10.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.94/10.06  
% 17.94/10.06  Inference rules
% 17.94/10.06  ----------------------
% 17.94/10.06  #Ref     : 0
% 17.94/10.06  #Sup     : 16077
% 17.94/10.06  #Fact    : 0
% 17.94/10.06  #Define  : 0
% 17.94/10.06  #Split   : 5
% 17.94/10.06  #Chain   : 0
% 17.94/10.06  #Close   : 0
% 17.94/10.06  
% 17.94/10.06  Ordering : KBO
% 17.94/10.06  
% 17.94/10.06  Simplification rules
% 17.94/10.06  ----------------------
% 17.94/10.06  #Subsume      : 5687
% 17.94/10.06  #Demod        : 9051
% 17.94/10.06  #Tautology    : 4355
% 17.94/10.06  #SimpNegUnit  : 196
% 17.94/10.06  #BackRed      : 21
% 17.94/10.06  
% 17.94/10.06  #Partial instantiations: 0
% 17.94/10.06  #Strategies tried      : 1
% 17.94/10.06  
% 17.94/10.06  Timing (in seconds)
% 17.94/10.06  ----------------------
% 17.94/10.06  Preprocessing        : 0.33
% 17.94/10.06  Parsing              : 0.17
% 17.94/10.06  CNF conversion       : 0.03
% 17.94/10.06  Main loop            : 8.94
% 17.94/10.06  Inferencing          : 1.49
% 17.94/10.06  Reduction            : 3.30
% 17.94/10.06  Demodulation         : 2.67
% 17.94/10.06  BG Simplification    : 0.17
% 17.94/10.06  Subsumption          : 3.44
% 17.94/10.06  Abstraction          : 0.27
% 17.94/10.06  MUC search           : 0.00
% 17.94/10.06  Cooper               : 0.00
% 17.94/10.06  Total                : 9.31
% 17.94/10.06  Index Insertion      : 0.00
% 17.94/10.06  Index Deletion       : 0.00
% 17.94/10.06  Index Matching       : 0.00
% 17.94/10.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
