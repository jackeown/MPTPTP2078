%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:34 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 109 expanded)
%              Number of leaves         :   44 (  53 expanded)
%              Depth                    :   10
%              Number of atoms          :  104 ( 139 expanded)
%              Number of equality atoms :   44 (  56 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_27,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k2_relat_1(B))
        <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_79,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
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

tff(f_57,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_67,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_82,axiom,(
    ! [A,B,C,D,E,F,G,H] : ~ v1_xboole_0(k6_enumset1(A,B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_subset_1)).

tff(c_4,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_50,plain,
    ( k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0
    | ~ r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_116,plain,(
    ~ r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_56,plain,
    ( r2_hidden('#skF_2',k2_relat_1('#skF_3'))
    | k10_relat_1('#skF_3',k1_tarski('#skF_2')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_172,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_2')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_56])).

tff(c_48,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_117,plain,(
    ! [A_66,B_67] :
      ( r1_xboole_0(k1_tarski(A_66),B_67)
      | r2_hidden(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_120,plain,(
    ! [B_67,A_66] :
      ( r1_xboole_0(B_67,k1_tarski(A_66))
      | r2_hidden(A_66,B_67) ) ),
    inference(resolution,[status(thm)],[c_117,c_6])).

tff(c_288,plain,(
    ! [B_108,A_109] :
      ( k10_relat_1(B_108,A_109) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_108),A_109)
      | ~ v1_relat_1(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_351,plain,(
    ! [B_124,A_125] :
      ( k10_relat_1(B_124,k1_tarski(A_125)) = k1_xboole_0
      | ~ v1_relat_1(B_124)
      | r2_hidden(A_125,k2_relat_1(B_124)) ) ),
    inference(resolution,[status(thm)],[c_120,c_288])).

tff(c_354,plain,
    ( k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_351,c_116])).

tff(c_357,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_354])).

tff(c_359,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_357])).

tff(c_360,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_486,plain,(
    ! [A_150,B_151] :
      ( k4_xboole_0(k1_tarski(A_150),B_151) = k1_tarski(A_150)
      | r2_hidden(A_150,B_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_16,plain,(
    ! [A_10] : k5_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    ! [A_11] : k2_tarski(A_11,A_11) = k1_tarski(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_375,plain,(
    ! [A_132,B_133] : k3_xboole_0(k1_tarski(A_132),k2_tarski(A_132,B_133)) = k1_tarski(A_132) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_384,plain,(
    ! [A_11] : k3_xboole_0(k1_tarski(A_11),k1_tarski(A_11)) = k1_tarski(A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_375])).

tff(c_415,plain,(
    ! [A_138,B_139] : k5_xboole_0(A_138,k3_xboole_0(A_138,B_139)) = k4_xboole_0(A_138,B_139) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_424,plain,(
    ! [A_11] : k5_xboole_0(k1_tarski(A_11),k1_tarski(A_11)) = k4_xboole_0(k1_tarski(A_11),k1_tarski(A_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_415])).

tff(c_433,plain,(
    ! [A_11] : k4_xboole_0(k1_tarski(A_11),k1_tarski(A_11)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_424])).

tff(c_497,plain,(
    ! [A_150] :
      ( k1_tarski(A_150) = k1_xboole_0
      | r2_hidden(A_150,k1_tarski(A_150)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_486,c_433])).

tff(c_361,plain,(
    r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_545,plain,(
    ! [B_170,A_171] :
      ( r1_xboole_0(k2_relat_1(B_170),A_171)
      | k10_relat_1(B_170,A_171) != k1_xboole_0
      | ~ v1_relat_1(B_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_578,plain,(
    ! [A_176,B_177] :
      ( r1_xboole_0(A_176,k2_relat_1(B_177))
      | k10_relat_1(B_177,A_176) != k1_xboole_0
      | ~ v1_relat_1(B_177) ) ),
    inference(resolution,[status(thm)],[c_545,c_6])).

tff(c_8,plain,(
    ! [A_3,B_4,C_7] :
      ( ~ r1_xboole_0(A_3,B_4)
      | ~ r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1212,plain,(
    ! [C_294,B_295,A_296] :
      ( ~ r2_hidden(C_294,k2_relat_1(B_295))
      | ~ r2_hidden(C_294,A_296)
      | k10_relat_1(B_295,A_296) != k1_xboole_0
      | ~ v1_relat_1(B_295) ) ),
    inference(resolution,[status(thm)],[c_578,c_8])).

tff(c_1222,plain,(
    ! [A_296] :
      ( ~ r2_hidden('#skF_2',A_296)
      | k10_relat_1('#skF_3',A_296) != k1_xboole_0
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_361,c_1212])).

tff(c_1229,plain,(
    ! [A_297] :
      ( ~ r2_hidden('#skF_2',A_297)
      | k10_relat_1('#skF_3',A_297) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1222])).

tff(c_1253,plain,
    ( k10_relat_1('#skF_3',k1_tarski('#skF_2')) != k1_xboole_0
    | k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_497,c_1229])).

tff(c_1270,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_1253])).

tff(c_20,plain,(
    ! [A_12,B_13] : k1_enumset1(A_12,A_12,B_13) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22,plain,(
    ! [A_14,B_15,C_16] : k2_enumset1(A_14,A_14,B_15,C_16) = k1_enumset1(A_14,B_15,C_16) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_24,plain,(
    ! [A_17,B_18,C_19,D_20] : k3_enumset1(A_17,A_17,B_18,C_19,D_20) = k2_enumset1(A_17,B_18,C_19,D_20) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_26,plain,(
    ! [A_21,B_22,D_24,C_23,E_25] : k4_enumset1(A_21,A_21,B_22,C_23,D_24,E_25) = k3_enumset1(A_21,B_22,C_23,D_24,E_25) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_28,plain,(
    ! [B_27,D_29,A_26,E_30,F_31,C_28] : k5_enumset1(A_26,A_26,B_27,C_28,D_29,E_30,F_31) = k4_enumset1(A_26,B_27,C_28,D_29,E_30,F_31) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_761,plain,(
    ! [A_218,B_215,C_217,D_219,F_216,G_220,E_214] : k6_enumset1(A_218,A_218,B_215,C_217,D_219,E_214,F_216,G_220) = k5_enumset1(A_218,B_215,C_217,D_219,E_214,F_216,G_220) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_40,plain,(
    ! [H_52,D_48,C_47,A_45,B_46,G_51,E_49,F_50] : ~ v1_xboole_0(k6_enumset1(A_45,B_46,C_47,D_48,E_49,F_50,G_51,H_52)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_788,plain,(
    ! [G_226,C_228,D_223,B_225,E_224,A_227,F_222] : ~ v1_xboole_0(k5_enumset1(A_227,B_225,C_228,D_223,E_224,F_222,G_226)) ),
    inference(superposition,[status(thm),theory(equality)],[c_761,c_40])).

tff(c_791,plain,(
    ! [C_233,E_234,F_232,D_229,A_231,B_230] : ~ v1_xboole_0(k4_enumset1(A_231,B_230,C_233,D_229,E_234,F_232)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_788])).

tff(c_794,plain,(
    ! [A_235,E_239,B_238,C_237,D_236] : ~ v1_xboole_0(k3_enumset1(A_235,B_238,C_237,D_236,E_239)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_791])).

tff(c_797,plain,(
    ! [A_240,B_241,C_242,D_243] : ~ v1_xboole_0(k2_enumset1(A_240,B_241,C_242,D_243)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_794])).

tff(c_800,plain,(
    ! [A_244,B_245,C_246] : ~ v1_xboole_0(k1_enumset1(A_244,B_245,C_246)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_797])).

tff(c_803,plain,(
    ! [A_247,B_248] : ~ v1_xboole_0(k2_tarski(A_247,B_248)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_800])).

tff(c_805,plain,(
    ! [A_11] : ~ v1_xboole_0(k1_tarski(A_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_803])).

tff(c_1312,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1270,c_805])).

tff(c_1411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1312])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:20:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.37/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.57  
% 3.37/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.57  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.37/1.57  
% 3.37/1.57  %Foreground sorts:
% 3.37/1.57  
% 3.37/1.57  
% 3.37/1.57  %Background operators:
% 3.37/1.57  
% 3.37/1.57  
% 3.37/1.57  %Foreground operators:
% 3.37/1.57  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 3.37/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.37/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.37/1.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.37/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.37/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.37/1.57  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.37/1.57  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.37/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.37/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.37/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.37/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.37/1.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.37/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.37/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.37/1.57  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.37/1.57  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.37/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.37/1.57  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.37/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.37/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.37/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.37/1.57  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.37/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.37/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.37/1.57  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.37/1.57  
% 3.55/1.59  tff(f_27, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.55/1.59  tff(f_98, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 3.55/1.59  tff(f_72, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.55/1.59  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.55/1.59  tff(f_90, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 3.55/1.59  tff(f_77, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 3.55/1.59  tff(f_53, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.55/1.59  tff(f_55, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.55/1.59  tff(f_79, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 3.55/1.59  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.55/1.59  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.55/1.59  tff(f_57, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.55/1.59  tff(f_59, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.55/1.59  tff(f_61, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.55/1.59  tff(f_63, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 3.55/1.59  tff(f_65, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 3.55/1.59  tff(f_67, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 3.55/1.59  tff(f_82, axiom, (![A, B, C, D, E, F, G, H]: ~v1_xboole_0(k6_enumset1(A, B, C, D, E, F, G, H))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_subset_1)).
% 3.55/1.59  tff(c_4, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.55/1.59  tff(c_50, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0 | ~r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.55/1.59  tff(c_116, plain, (~r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_50])).
% 3.55/1.59  tff(c_56, plain, (r2_hidden('#skF_2', k2_relat_1('#skF_3')) | k10_relat_1('#skF_3', k1_tarski('#skF_2'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.55/1.59  tff(c_172, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_116, c_56])).
% 3.55/1.59  tff(c_48, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.55/1.59  tff(c_117, plain, (![A_66, B_67]: (r1_xboole_0(k1_tarski(A_66), B_67) | r2_hidden(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.55/1.59  tff(c_6, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.55/1.59  tff(c_120, plain, (![B_67, A_66]: (r1_xboole_0(B_67, k1_tarski(A_66)) | r2_hidden(A_66, B_67))), inference(resolution, [status(thm)], [c_117, c_6])).
% 3.55/1.59  tff(c_288, plain, (![B_108, A_109]: (k10_relat_1(B_108, A_109)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_108), A_109) | ~v1_relat_1(B_108))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.55/1.59  tff(c_351, plain, (![B_124, A_125]: (k10_relat_1(B_124, k1_tarski(A_125))=k1_xboole_0 | ~v1_relat_1(B_124) | r2_hidden(A_125, k2_relat_1(B_124)))), inference(resolution, [status(thm)], [c_120, c_288])).
% 3.55/1.59  tff(c_354, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_351, c_116])).
% 3.55/1.59  tff(c_357, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_354])).
% 3.55/1.59  tff(c_359, plain, $false, inference(negUnitSimplification, [status(thm)], [c_172, c_357])).
% 3.55/1.59  tff(c_360, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 3.55/1.59  tff(c_486, plain, (![A_150, B_151]: (k4_xboole_0(k1_tarski(A_150), B_151)=k1_tarski(A_150) | r2_hidden(A_150, B_151))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.55/1.59  tff(c_16, plain, (![A_10]: (k5_xboole_0(A_10, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.55/1.59  tff(c_18, plain, (![A_11]: (k2_tarski(A_11, A_11)=k1_tarski(A_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.55/1.59  tff(c_375, plain, (![A_132, B_133]: (k3_xboole_0(k1_tarski(A_132), k2_tarski(A_132, B_133))=k1_tarski(A_132))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.55/1.59  tff(c_384, plain, (![A_11]: (k3_xboole_0(k1_tarski(A_11), k1_tarski(A_11))=k1_tarski(A_11))), inference(superposition, [status(thm), theory('equality')], [c_18, c_375])).
% 3.55/1.59  tff(c_415, plain, (![A_138, B_139]: (k5_xboole_0(A_138, k3_xboole_0(A_138, B_139))=k4_xboole_0(A_138, B_139))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.55/1.59  tff(c_424, plain, (![A_11]: (k5_xboole_0(k1_tarski(A_11), k1_tarski(A_11))=k4_xboole_0(k1_tarski(A_11), k1_tarski(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_384, c_415])).
% 3.55/1.59  tff(c_433, plain, (![A_11]: (k4_xboole_0(k1_tarski(A_11), k1_tarski(A_11))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_424])).
% 3.55/1.59  tff(c_497, plain, (![A_150]: (k1_tarski(A_150)=k1_xboole_0 | r2_hidden(A_150, k1_tarski(A_150)))), inference(superposition, [status(thm), theory('equality')], [c_486, c_433])).
% 3.55/1.59  tff(c_361, plain, (r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_50])).
% 3.55/1.59  tff(c_545, plain, (![B_170, A_171]: (r1_xboole_0(k2_relat_1(B_170), A_171) | k10_relat_1(B_170, A_171)!=k1_xboole_0 | ~v1_relat_1(B_170))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.55/1.59  tff(c_578, plain, (![A_176, B_177]: (r1_xboole_0(A_176, k2_relat_1(B_177)) | k10_relat_1(B_177, A_176)!=k1_xboole_0 | ~v1_relat_1(B_177))), inference(resolution, [status(thm)], [c_545, c_6])).
% 3.55/1.59  tff(c_8, plain, (![A_3, B_4, C_7]: (~r1_xboole_0(A_3, B_4) | ~r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.55/1.59  tff(c_1212, plain, (![C_294, B_295, A_296]: (~r2_hidden(C_294, k2_relat_1(B_295)) | ~r2_hidden(C_294, A_296) | k10_relat_1(B_295, A_296)!=k1_xboole_0 | ~v1_relat_1(B_295))), inference(resolution, [status(thm)], [c_578, c_8])).
% 3.55/1.59  tff(c_1222, plain, (![A_296]: (~r2_hidden('#skF_2', A_296) | k10_relat_1('#skF_3', A_296)!=k1_xboole_0 | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_361, c_1212])).
% 3.55/1.59  tff(c_1229, plain, (![A_297]: (~r2_hidden('#skF_2', A_297) | k10_relat_1('#skF_3', A_297)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1222])).
% 3.55/1.59  tff(c_1253, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))!=k1_xboole_0 | k1_tarski('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_497, c_1229])).
% 3.55/1.59  tff(c_1270, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_360, c_1253])).
% 3.55/1.59  tff(c_20, plain, (![A_12, B_13]: (k1_enumset1(A_12, A_12, B_13)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.55/1.59  tff(c_22, plain, (![A_14, B_15, C_16]: (k2_enumset1(A_14, A_14, B_15, C_16)=k1_enumset1(A_14, B_15, C_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.55/1.59  tff(c_24, plain, (![A_17, B_18, C_19, D_20]: (k3_enumset1(A_17, A_17, B_18, C_19, D_20)=k2_enumset1(A_17, B_18, C_19, D_20))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.55/1.59  tff(c_26, plain, (![A_21, B_22, D_24, C_23, E_25]: (k4_enumset1(A_21, A_21, B_22, C_23, D_24, E_25)=k3_enumset1(A_21, B_22, C_23, D_24, E_25))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.55/1.59  tff(c_28, plain, (![B_27, D_29, A_26, E_30, F_31, C_28]: (k5_enumset1(A_26, A_26, B_27, C_28, D_29, E_30, F_31)=k4_enumset1(A_26, B_27, C_28, D_29, E_30, F_31))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.55/1.59  tff(c_761, plain, (![A_218, B_215, C_217, D_219, F_216, G_220, E_214]: (k6_enumset1(A_218, A_218, B_215, C_217, D_219, E_214, F_216, G_220)=k5_enumset1(A_218, B_215, C_217, D_219, E_214, F_216, G_220))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.55/1.59  tff(c_40, plain, (![H_52, D_48, C_47, A_45, B_46, G_51, E_49, F_50]: (~v1_xboole_0(k6_enumset1(A_45, B_46, C_47, D_48, E_49, F_50, G_51, H_52)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.55/1.59  tff(c_788, plain, (![G_226, C_228, D_223, B_225, E_224, A_227, F_222]: (~v1_xboole_0(k5_enumset1(A_227, B_225, C_228, D_223, E_224, F_222, G_226)))), inference(superposition, [status(thm), theory('equality')], [c_761, c_40])).
% 3.55/1.59  tff(c_791, plain, (![C_233, E_234, F_232, D_229, A_231, B_230]: (~v1_xboole_0(k4_enumset1(A_231, B_230, C_233, D_229, E_234, F_232)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_788])).
% 3.55/1.59  tff(c_794, plain, (![A_235, E_239, B_238, C_237, D_236]: (~v1_xboole_0(k3_enumset1(A_235, B_238, C_237, D_236, E_239)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_791])).
% 3.55/1.59  tff(c_797, plain, (![A_240, B_241, C_242, D_243]: (~v1_xboole_0(k2_enumset1(A_240, B_241, C_242, D_243)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_794])).
% 3.55/1.59  tff(c_800, plain, (![A_244, B_245, C_246]: (~v1_xboole_0(k1_enumset1(A_244, B_245, C_246)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_797])).
% 3.55/1.59  tff(c_803, plain, (![A_247, B_248]: (~v1_xboole_0(k2_tarski(A_247, B_248)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_800])).
% 3.55/1.59  tff(c_805, plain, (![A_11]: (~v1_xboole_0(k1_tarski(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_803])).
% 3.55/1.59  tff(c_1312, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1270, c_805])).
% 3.55/1.59  tff(c_1411, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_1312])).
% 3.55/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.59  
% 3.55/1.59  Inference rules
% 3.55/1.59  ----------------------
% 3.55/1.59  #Ref     : 0
% 3.55/1.59  #Sup     : 344
% 3.55/1.59  #Fact    : 0
% 3.55/1.59  #Define  : 0
% 3.55/1.59  #Split   : 1
% 3.55/1.59  #Chain   : 0
% 3.55/1.59  #Close   : 0
% 3.55/1.59  
% 3.55/1.59  Ordering : KBO
% 3.55/1.59  
% 3.55/1.59  Simplification rules
% 3.55/1.59  ----------------------
% 3.55/1.59  #Subsume      : 101
% 3.55/1.59  #Demod        : 45
% 3.55/1.59  #Tautology    : 104
% 3.55/1.59  #SimpNegUnit  : 2
% 3.55/1.59  #BackRed      : 2
% 3.55/1.59  
% 3.55/1.59  #Partial instantiations: 0
% 3.55/1.59  #Strategies tried      : 1
% 3.55/1.59  
% 3.55/1.59  Timing (in seconds)
% 3.55/1.59  ----------------------
% 3.55/1.59  Preprocessing        : 0.33
% 3.55/1.59  Parsing              : 0.18
% 3.55/1.59  CNF conversion       : 0.02
% 3.55/1.59  Main loop            : 0.43
% 3.55/1.59  Inferencing          : 0.18
% 3.55/1.59  Reduction            : 0.11
% 3.55/1.59  Demodulation         : 0.08
% 3.55/1.59  BG Simplification    : 0.02
% 3.55/1.59  Subsumption          : 0.08
% 3.55/1.59  Abstraction          : 0.02
% 3.55/1.59  MUC search           : 0.00
% 3.55/1.59  Cooper               : 0.00
% 3.55/1.59  Total                : 0.80
% 3.55/1.59  Index Insertion      : 0.00
% 3.55/1.59  Index Deletion       : 0.00
% 3.55/1.59  Index Matching       : 0.00
% 3.55/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
