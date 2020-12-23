%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:34 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 113 expanded)
%              Number of leaves         :   46 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :  107 ( 142 expanded)
%              Number of equality atoms :   46 (  59 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_subset_1 > k1_setfam_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_80,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_82,axiom,(
    ! [A] : v1_xboole_0(k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_subset_1)).

tff(f_101,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k2_relat_1(B))
        <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_93,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_54,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_52,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_58,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_62,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_66,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_85,axiom,(
    ! [A,B,C,D,E,F,G,H] : ~ v1_xboole_0(k6_enumset1(A,B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_subset_1)).

tff(c_38,plain,(
    ! [A_45] : k1_subset_1(A_45) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_40,plain,(
    ! [A_46] : v1_xboole_0(k1_subset_1(A_46)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_59,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40])).

tff(c_58,plain,
    ( r2_hidden('#skF_2',k2_relat_1('#skF_3'))
    | k10_relat_1('#skF_3',k1_tarski('#skF_2')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_101,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_2')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_50,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_88,plain,(
    ! [A_64,B_65] :
      ( r1_xboole_0(k1_tarski(A_64),B_65)
      | r2_hidden(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_91,plain,(
    ! [B_65,A_64] :
      ( r1_xboole_0(B_65,k1_tarski(A_64))
      | r2_hidden(A_64,B_65) ) ),
    inference(resolution,[status(thm)],[c_88,c_4])).

tff(c_297,plain,(
    ! [B_103,A_104] :
      ( k10_relat_1(B_103,A_104) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_103),A_104)
      | ~ v1_relat_1(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_361,plain,(
    ! [B_127,A_128] :
      ( k10_relat_1(B_127,k1_tarski(A_128)) = k1_xboole_0
      | ~ v1_relat_1(B_127)
      | r2_hidden(A_128,k2_relat_1(B_127)) ) ),
    inference(resolution,[status(thm)],[c_91,c_297])).

tff(c_52,plain,
    ( k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0
    | ~ r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_175,plain,(
    ~ r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_52])).

tff(c_364,plain,
    ( k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_361,c_175])).

tff(c_367,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_364])).

tff(c_369,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_367])).

tff(c_371,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_458,plain,(
    ! [A_145,B_146] :
      ( k4_xboole_0(k1_tarski(A_145),B_146) = k1_tarski(A_145)
      | r2_hidden(A_145,B_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_16,plain,(
    ! [A_11] : k2_tarski(A_11,A_11) = k1_tarski(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_14,plain,(
    ! [A_10] : k5_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_425,plain,(
    ! [A_140,B_141] : k3_xboole_0(k1_tarski(A_140),k2_tarski(A_140,B_141)) = k1_tarski(A_140) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_12,plain,(
    ! [A_8,B_9] : k5_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_431,plain,(
    ! [A_140,B_141] : k5_xboole_0(k1_tarski(A_140),k1_tarski(A_140)) = k4_xboole_0(k1_tarski(A_140),k2_tarski(A_140,B_141)) ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_12])).

tff(c_441,plain,(
    ! [A_142,B_143] : k4_xboole_0(k1_tarski(A_142),k2_tarski(A_142,B_143)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_431])).

tff(c_448,plain,(
    ! [A_11] : k4_xboole_0(k1_tarski(A_11),k1_tarski(A_11)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_441])).

tff(c_465,plain,(
    ! [A_145] :
      ( k1_tarski(A_145) = k1_xboole_0
      | r2_hidden(A_145,k1_tarski(A_145)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_448])).

tff(c_370,plain,(
    r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_578,plain,(
    ! [B_166,A_167] :
      ( r1_xboole_0(k2_relat_1(B_166),A_167)
      | k10_relat_1(B_166,A_167) != k1_xboole_0
      | ~ v1_relat_1(B_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_590,plain,(
    ! [A_176,B_177] :
      ( r1_xboole_0(A_176,k2_relat_1(B_177))
      | k10_relat_1(B_177,A_176) != k1_xboole_0
      | ~ v1_relat_1(B_177) ) ),
    inference(resolution,[status(thm)],[c_578,c_4])).

tff(c_6,plain,(
    ! [A_3,B_4,C_7] :
      ( ~ r1_xboole_0(A_3,B_4)
      | ~ r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1197,plain,(
    ! [C_292,B_293,A_294] :
      ( ~ r2_hidden(C_292,k2_relat_1(B_293))
      | ~ r2_hidden(C_292,A_294)
      | k10_relat_1(B_293,A_294) != k1_xboole_0
      | ~ v1_relat_1(B_293) ) ),
    inference(resolution,[status(thm)],[c_590,c_6])).

tff(c_1207,plain,(
    ! [A_294] :
      ( ~ r2_hidden('#skF_2',A_294)
      | k10_relat_1('#skF_3',A_294) != k1_xboole_0
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_370,c_1197])).

tff(c_1214,plain,(
    ! [A_295] :
      ( ~ r2_hidden('#skF_2',A_295)
      | k10_relat_1('#skF_3',A_295) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1207])).

tff(c_1238,plain,
    ( k10_relat_1('#skF_3',k1_tarski('#skF_2')) != k1_xboole_0
    | k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_465,c_1214])).

tff(c_1255,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_1238])).

tff(c_18,plain,(
    ! [A_12,B_13] : k1_enumset1(A_12,A_12,B_13) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_20,plain,(
    ! [A_14,B_15,C_16] : k2_enumset1(A_14,A_14,B_15,C_16) = k1_enumset1(A_14,B_15,C_16) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_22,plain,(
    ! [A_17,B_18,C_19,D_20] : k3_enumset1(A_17,A_17,B_18,C_19,D_20) = k2_enumset1(A_17,B_18,C_19,D_20) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_24,plain,(
    ! [A_21,B_22,D_24,C_23,E_25] : k4_enumset1(A_21,A_21,B_22,C_23,D_24,E_25) = k3_enumset1(A_21,B_22,C_23,D_24,E_25) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_26,plain,(
    ! [B_27,D_29,A_26,E_30,F_31,C_28] : k5_enumset1(A_26,A_26,B_27,C_28,D_29,E_30,F_31) = k4_enumset1(A_26,B_27,C_28,D_29,E_30,F_31) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_829,plain,(
    ! [D_227,C_225,E_222,F_224,G_228,A_226,B_223] : k6_enumset1(A_226,A_226,B_223,C_225,D_227,E_222,F_224,G_228) = k5_enumset1(A_226,B_223,C_225,D_227,E_222,F_224,G_228) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_42,plain,(
    ! [G_53,A_47,F_52,E_51,H_54,D_50,C_49,B_48] : ~ v1_xboole_0(k6_enumset1(A_47,B_48,C_49,D_50,E_51,F_52,G_53,H_54)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_840,plain,(
    ! [A_235,G_232,D_231,B_234,C_230,E_229,F_233] : ~ v1_xboole_0(k5_enumset1(A_235,B_234,C_230,D_231,E_229,F_233,G_232)) ),
    inference(superposition,[status(thm),theory(equality)],[c_829,c_42])).

tff(c_843,plain,(
    ! [B_237,E_241,F_239,D_236,A_238,C_240] : ~ v1_xboole_0(k4_enumset1(A_238,B_237,C_240,D_236,E_241,F_239)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_840])).

tff(c_846,plain,(
    ! [C_244,B_245,D_243,A_242,E_246] : ~ v1_xboole_0(k3_enumset1(A_242,B_245,C_244,D_243,E_246)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_843])).

tff(c_849,plain,(
    ! [A_247,B_248,C_249,D_250] : ~ v1_xboole_0(k2_enumset1(A_247,B_248,C_249,D_250)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_846])).

tff(c_852,plain,(
    ! [A_251,B_252,C_253] : ~ v1_xboole_0(k1_enumset1(A_251,B_252,C_253)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_849])).

tff(c_880,plain,(
    ! [A_257,B_258] : ~ v1_xboole_0(k2_tarski(A_257,B_258)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_852])).

tff(c_882,plain,(
    ! [A_11] : ~ v1_xboole_0(k1_tarski(A_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_880])).

tff(c_1290,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1255,c_882])).

tff(c_1386,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_1290])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:09:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.34/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.53  
% 3.34/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.54  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_subset_1 > k1_setfam_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.34/1.54  
% 3.34/1.54  %Foreground sorts:
% 3.34/1.54  
% 3.34/1.54  
% 3.34/1.54  %Background operators:
% 3.34/1.54  
% 3.34/1.54  
% 3.34/1.54  %Foreground operators:
% 3.34/1.54  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 3.34/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.34/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.34/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.34/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.34/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.34/1.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.34/1.54  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.34/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.34/1.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.34/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.34/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.34/1.54  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.34/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.34/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.34/1.54  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.34/1.54  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.34/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.34/1.54  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.34/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.34/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.34/1.54  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.34/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.34/1.54  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.34/1.54  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.34/1.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.34/1.54  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.34/1.54  
% 3.34/1.55  tff(f_80, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 3.34/1.55  tff(f_82, axiom, (![A]: v1_xboole_0(k1_subset_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc13_subset_1)).
% 3.34/1.55  tff(f_101, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 3.34/1.55  tff(f_71, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.34/1.55  tff(f_30, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.34/1.55  tff(f_93, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 3.34/1.55  tff(f_76, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 3.34/1.55  tff(f_54, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.34/1.55  tff(f_52, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.34/1.55  tff(f_78, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 3.34/1.55  tff(f_50, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.34/1.55  tff(f_48, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.34/1.55  tff(f_56, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.34/1.55  tff(f_58, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.34/1.55  tff(f_60, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.34/1.55  tff(f_62, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 3.34/1.55  tff(f_64, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 3.34/1.55  tff(f_66, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 3.34/1.55  tff(f_85, axiom, (![A, B, C, D, E, F, G, H]: ~v1_xboole_0(k6_enumset1(A, B, C, D, E, F, G, H))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_subset_1)).
% 3.34/1.55  tff(c_38, plain, (![A_45]: (k1_subset_1(A_45)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.34/1.55  tff(c_40, plain, (![A_46]: (v1_xboole_0(k1_subset_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.34/1.55  tff(c_59, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40])).
% 3.34/1.55  tff(c_58, plain, (r2_hidden('#skF_2', k2_relat_1('#skF_3')) | k10_relat_1('#skF_3', k1_tarski('#skF_2'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.34/1.55  tff(c_101, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_58])).
% 3.34/1.55  tff(c_50, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.34/1.55  tff(c_88, plain, (![A_64, B_65]: (r1_xboole_0(k1_tarski(A_64), B_65) | r2_hidden(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.34/1.55  tff(c_4, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.34/1.55  tff(c_91, plain, (![B_65, A_64]: (r1_xboole_0(B_65, k1_tarski(A_64)) | r2_hidden(A_64, B_65))), inference(resolution, [status(thm)], [c_88, c_4])).
% 3.34/1.55  tff(c_297, plain, (![B_103, A_104]: (k10_relat_1(B_103, A_104)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_103), A_104) | ~v1_relat_1(B_103))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.34/1.55  tff(c_361, plain, (![B_127, A_128]: (k10_relat_1(B_127, k1_tarski(A_128))=k1_xboole_0 | ~v1_relat_1(B_127) | r2_hidden(A_128, k2_relat_1(B_127)))), inference(resolution, [status(thm)], [c_91, c_297])).
% 3.34/1.55  tff(c_52, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0 | ~r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.34/1.55  tff(c_175, plain, (~r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_101, c_52])).
% 3.34/1.55  tff(c_364, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_361, c_175])).
% 3.34/1.55  tff(c_367, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_364])).
% 3.34/1.55  tff(c_369, plain, $false, inference(negUnitSimplification, [status(thm)], [c_101, c_367])).
% 3.34/1.55  tff(c_371, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_58])).
% 3.34/1.55  tff(c_458, plain, (![A_145, B_146]: (k4_xboole_0(k1_tarski(A_145), B_146)=k1_tarski(A_145) | r2_hidden(A_145, B_146))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.34/1.55  tff(c_16, plain, (![A_11]: (k2_tarski(A_11, A_11)=k1_tarski(A_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.34/1.55  tff(c_14, plain, (![A_10]: (k5_xboole_0(A_10, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.34/1.55  tff(c_425, plain, (![A_140, B_141]: (k3_xboole_0(k1_tarski(A_140), k2_tarski(A_140, B_141))=k1_tarski(A_140))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.34/1.55  tff(c_12, plain, (![A_8, B_9]: (k5_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.34/1.55  tff(c_431, plain, (![A_140, B_141]: (k5_xboole_0(k1_tarski(A_140), k1_tarski(A_140))=k4_xboole_0(k1_tarski(A_140), k2_tarski(A_140, B_141)))), inference(superposition, [status(thm), theory('equality')], [c_425, c_12])).
% 3.34/1.55  tff(c_441, plain, (![A_142, B_143]: (k4_xboole_0(k1_tarski(A_142), k2_tarski(A_142, B_143))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_431])).
% 3.34/1.55  tff(c_448, plain, (![A_11]: (k4_xboole_0(k1_tarski(A_11), k1_tarski(A_11))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_441])).
% 3.34/1.55  tff(c_465, plain, (![A_145]: (k1_tarski(A_145)=k1_xboole_0 | r2_hidden(A_145, k1_tarski(A_145)))), inference(superposition, [status(thm), theory('equality')], [c_458, c_448])).
% 3.34/1.55  tff(c_370, plain, (r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_58])).
% 3.34/1.55  tff(c_578, plain, (![B_166, A_167]: (r1_xboole_0(k2_relat_1(B_166), A_167) | k10_relat_1(B_166, A_167)!=k1_xboole_0 | ~v1_relat_1(B_166))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.34/1.55  tff(c_590, plain, (![A_176, B_177]: (r1_xboole_0(A_176, k2_relat_1(B_177)) | k10_relat_1(B_177, A_176)!=k1_xboole_0 | ~v1_relat_1(B_177))), inference(resolution, [status(thm)], [c_578, c_4])).
% 3.34/1.55  tff(c_6, plain, (![A_3, B_4, C_7]: (~r1_xboole_0(A_3, B_4) | ~r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.34/1.55  tff(c_1197, plain, (![C_292, B_293, A_294]: (~r2_hidden(C_292, k2_relat_1(B_293)) | ~r2_hidden(C_292, A_294) | k10_relat_1(B_293, A_294)!=k1_xboole_0 | ~v1_relat_1(B_293))), inference(resolution, [status(thm)], [c_590, c_6])).
% 3.34/1.55  tff(c_1207, plain, (![A_294]: (~r2_hidden('#skF_2', A_294) | k10_relat_1('#skF_3', A_294)!=k1_xboole_0 | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_370, c_1197])).
% 3.34/1.55  tff(c_1214, plain, (![A_295]: (~r2_hidden('#skF_2', A_295) | k10_relat_1('#skF_3', A_295)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1207])).
% 3.34/1.55  tff(c_1238, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))!=k1_xboole_0 | k1_tarski('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_465, c_1214])).
% 3.34/1.55  tff(c_1255, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_371, c_1238])).
% 3.34/1.55  tff(c_18, plain, (![A_12, B_13]: (k1_enumset1(A_12, A_12, B_13)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.34/1.55  tff(c_20, plain, (![A_14, B_15, C_16]: (k2_enumset1(A_14, A_14, B_15, C_16)=k1_enumset1(A_14, B_15, C_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.34/1.55  tff(c_22, plain, (![A_17, B_18, C_19, D_20]: (k3_enumset1(A_17, A_17, B_18, C_19, D_20)=k2_enumset1(A_17, B_18, C_19, D_20))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.34/1.55  tff(c_24, plain, (![A_21, B_22, D_24, C_23, E_25]: (k4_enumset1(A_21, A_21, B_22, C_23, D_24, E_25)=k3_enumset1(A_21, B_22, C_23, D_24, E_25))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.34/1.55  tff(c_26, plain, (![B_27, D_29, A_26, E_30, F_31, C_28]: (k5_enumset1(A_26, A_26, B_27, C_28, D_29, E_30, F_31)=k4_enumset1(A_26, B_27, C_28, D_29, E_30, F_31))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.34/1.55  tff(c_829, plain, (![D_227, C_225, E_222, F_224, G_228, A_226, B_223]: (k6_enumset1(A_226, A_226, B_223, C_225, D_227, E_222, F_224, G_228)=k5_enumset1(A_226, B_223, C_225, D_227, E_222, F_224, G_228))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.34/1.55  tff(c_42, plain, (![G_53, A_47, F_52, E_51, H_54, D_50, C_49, B_48]: (~v1_xboole_0(k6_enumset1(A_47, B_48, C_49, D_50, E_51, F_52, G_53, H_54)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.34/1.55  tff(c_840, plain, (![A_235, G_232, D_231, B_234, C_230, E_229, F_233]: (~v1_xboole_0(k5_enumset1(A_235, B_234, C_230, D_231, E_229, F_233, G_232)))), inference(superposition, [status(thm), theory('equality')], [c_829, c_42])).
% 3.34/1.55  tff(c_843, plain, (![B_237, E_241, F_239, D_236, A_238, C_240]: (~v1_xboole_0(k4_enumset1(A_238, B_237, C_240, D_236, E_241, F_239)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_840])).
% 3.34/1.55  tff(c_846, plain, (![C_244, B_245, D_243, A_242, E_246]: (~v1_xboole_0(k3_enumset1(A_242, B_245, C_244, D_243, E_246)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_843])).
% 3.34/1.55  tff(c_849, plain, (![A_247, B_248, C_249, D_250]: (~v1_xboole_0(k2_enumset1(A_247, B_248, C_249, D_250)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_846])).
% 3.34/1.55  tff(c_852, plain, (![A_251, B_252, C_253]: (~v1_xboole_0(k1_enumset1(A_251, B_252, C_253)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_849])).
% 3.34/1.55  tff(c_880, plain, (![A_257, B_258]: (~v1_xboole_0(k2_tarski(A_257, B_258)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_852])).
% 3.34/1.55  tff(c_882, plain, (![A_11]: (~v1_xboole_0(k1_tarski(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_880])).
% 3.34/1.55  tff(c_1290, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1255, c_882])).
% 3.34/1.55  tff(c_1386, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_1290])).
% 3.34/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.55  
% 3.34/1.55  Inference rules
% 3.34/1.55  ----------------------
% 3.34/1.55  #Ref     : 0
% 3.34/1.55  #Sup     : 339
% 3.34/1.55  #Fact    : 0
% 3.34/1.55  #Define  : 0
% 3.34/1.55  #Split   : 1
% 3.34/1.55  #Chain   : 0
% 3.34/1.55  #Close   : 0
% 3.34/1.55  
% 3.34/1.55  Ordering : KBO
% 3.34/1.55  
% 3.34/1.55  Simplification rules
% 3.34/1.55  ----------------------
% 3.34/1.55  #Subsume      : 90
% 3.34/1.55  #Demod        : 43
% 3.34/1.55  #Tautology    : 111
% 3.34/1.55  #SimpNegUnit  : 2
% 3.34/1.55  #BackRed      : 2
% 3.34/1.55  
% 3.34/1.55  #Partial instantiations: 0
% 3.34/1.55  #Strategies tried      : 1
% 3.34/1.55  
% 3.34/1.55  Timing (in seconds)
% 3.34/1.55  ----------------------
% 3.34/1.56  Preprocessing        : 0.34
% 3.34/1.56  Parsing              : 0.18
% 3.34/1.56  CNF conversion       : 0.02
% 3.34/1.56  Main loop            : 0.45
% 3.34/1.56  Inferencing          : 0.19
% 3.34/1.56  Reduction            : 0.12
% 3.34/1.56  Demodulation         : 0.08
% 3.34/1.56  BG Simplification    : 0.02
% 3.34/1.56  Subsumption          : 0.08
% 3.34/1.56  Abstraction          : 0.02
% 3.34/1.56  MUC search           : 0.00
% 3.34/1.56  Cooper               : 0.00
% 3.34/1.56  Total                : 0.83
% 3.34/1.56  Index Insertion      : 0.00
% 3.34/1.56  Index Deletion       : 0.00
% 3.34/1.56  Index Matching       : 0.00
% 3.34/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
