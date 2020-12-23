%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:22 EST 2020

% Result     : Theorem 4.04s
% Output     : CNFRefutation 4.45s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 232 expanded)
%              Number of leaves         :   40 (  93 expanded)
%              Depth                    :   12
%              Number of atoms          :  165 ( 484 expanded)
%              Number of equality atoms :   36 (  61 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_132,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_38,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_84,axiom,(
    ! [A,B,C,D,E,F,G,H,I] :
      ( I = k6_enumset1(A,B,C,D,E,F,G,H)
    <=> ! [J] :
          ( r2_hidden(J,I)
        <=> ~ ( J != A
              & J != B
              & J != C
              & J != D
              & J != E
              & J != F
              & J != G
              & J != H ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).

tff(f_94,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_117,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_122,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_106,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_108,plain,(
    v3_ordinal1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1330,plain,(
    ! [B_369,A_370] :
      ( r1_ordinal1(B_369,A_370)
      | r1_ordinal1(A_370,B_369)
      | ~ v3_ordinal1(B_369)
      | ~ v3_ordinal1(A_370) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_22,plain,(
    ! [A_8,B_9] : k1_enumset1(A_8,A_8,B_9) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_24,plain,(
    ! [A_10,B_11,C_12] : k2_enumset1(A_10,A_10,B_11,C_12) = k1_enumset1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_26,plain,(
    ! [A_13,B_14,C_15,D_16] : k3_enumset1(A_13,A_13,B_14,C_15,D_16) = k2_enumset1(A_13,B_14,C_15,D_16) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_28,plain,(
    ! [E_21,D_20,C_19,B_18,A_17] : k4_enumset1(A_17,A_17,B_18,C_19,D_20,E_21) = k3_enumset1(A_17,B_18,C_19,D_20,E_21) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_30,plain,(
    ! [E_26,F_27,A_22,B_23,D_25,C_24] : k5_enumset1(A_22,A_22,B_23,C_24,D_25,E_26,F_27) = k4_enumset1(A_22,B_23,C_24,D_25,E_26,F_27) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_830,plain,(
    ! [A_290,B_292,E_289,C_291,D_293,F_288,G_287] : k6_enumset1(A_290,A_290,B_292,C_291,D_293,E_289,F_288,G_287) = k5_enumset1(A_290,B_292,C_291,D_293,E_289,F_288,G_287) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_44,plain,(
    ! [J_50,E_43,H_46,F_44,D_42,A_39,C_41,B_40] : r2_hidden(J_50,k6_enumset1(A_39,B_40,C_41,D_42,E_43,F_44,J_50,H_46)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_887,plain,(
    ! [E_299,B_296,C_294,F_295,D_300,G_298,A_297] : r2_hidden(F_295,k5_enumset1(A_297,B_296,C_294,D_300,E_299,F_295,G_298)) ),
    inference(superposition,[status(thm),theory(equality)],[c_830,c_44])).

tff(c_895,plain,(
    ! [F_304,B_306,C_302,E_303,D_305,A_301] : r2_hidden(E_303,k4_enumset1(A_301,B_306,C_302,D_305,E_303,F_304)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_887])).

tff(c_903,plain,(
    ! [A_308,C_307,B_309,D_310,E_311] : r2_hidden(D_310,k3_enumset1(A_308,B_309,C_307,D_310,E_311)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_895])).

tff(c_1010,plain,(
    ! [C_315,A_316,B_317,D_318] : r2_hidden(C_315,k2_enumset1(A_316,B_317,C_315,D_318)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_903])).

tff(c_1018,plain,(
    ! [B_319,A_320,C_321] : r2_hidden(B_319,k1_enumset1(A_320,B_319,C_321)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1010])).

tff(c_1026,plain,(
    ! [A_322,B_323] : r2_hidden(A_322,k2_tarski(A_322,B_323)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1018])).

tff(c_1035,plain,(
    ! [A_324] : r2_hidden(A_324,k1_tarski(A_324)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1026])).

tff(c_96,plain,(
    ! [A_53] : k2_xboole_0(A_53,k1_tarski(A_53)) = k1_ordinal1(A_53) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_202,plain,(
    ! [D_80,B_81,A_82] :
      ( ~ r2_hidden(D_80,B_81)
      | r2_hidden(D_80,k2_xboole_0(A_82,B_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_211,plain,(
    ! [D_80,A_53] :
      ( ~ r2_hidden(D_80,k1_tarski(A_53))
      | r2_hidden(D_80,k1_ordinal1(A_53)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_202])).

tff(c_1046,plain,(
    ! [A_324] : r2_hidden(A_324,k1_ordinal1(A_324)) ),
    inference(resolution,[status(thm)],[c_1035,c_211])).

tff(c_110,plain,
    ( ~ r1_ordinal1('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_136,plain,(
    ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_116,plain,
    ( r2_hidden('#skF_5',k1_ordinal1('#skF_6'))
    | r1_ordinal1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_146,plain,(
    r1_ordinal1('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_116])).

tff(c_100,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,B_55)
      | ~ r1_ordinal1(A_54,B_55)
      | ~ v3_ordinal1(B_55)
      | ~ v3_ordinal1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_400,plain,(
    ! [B_204,A_205] :
      ( r2_hidden(B_204,A_205)
      | B_204 = A_205
      | r2_hidden(A_205,B_204)
      | ~ v3_ordinal1(B_204)
      | ~ v3_ordinal1(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_182,plain,(
    ! [D_75,A_76,B_77] :
      ( ~ r2_hidden(D_75,A_76)
      | r2_hidden(D_75,k2_xboole_0(A_76,B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_193,plain,(
    ! [D_78,A_79] :
      ( ~ r2_hidden(D_78,A_79)
      | r2_hidden(D_78,k1_ordinal1(A_79)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_182])).

tff(c_200,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_193,c_136])).

tff(c_415,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_400,c_200])).

tff(c_444,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_108,c_415])).

tff(c_453,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_444])).

tff(c_104,plain,(
    ! [B_60,A_59] :
      ( ~ r1_tarski(B_60,A_59)
      | ~ r2_hidden(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_457,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_453,c_104])).

tff(c_460,plain,
    ( ~ r1_ordinal1('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_100,c_457])).

tff(c_464,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_146,c_460])).

tff(c_465,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_444])).

tff(c_470,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_136])).

tff(c_1156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1046,c_470])).

tff(c_1157,plain,(
    ~ r1_ordinal1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_1333,plain,
    ( r1_ordinal1('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1330,c_1157])).

tff(c_1339,plain,(
    r1_ordinal1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_108,c_1333])).

tff(c_94,plain,(
    ! [B_52,A_51] :
      ( r1_ordinal1(B_52,A_51)
      | r1_ordinal1(A_51,B_52)
      | ~ v3_ordinal1(B_52)
      | ~ v3_ordinal1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1328,plain,(
    ! [B_52] :
      ( ~ v3_ordinal1(B_52)
      | r1_ordinal1(B_52,B_52) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_94])).

tff(c_1425,plain,(
    ! [B_443,A_444] :
      ( r2_hidden(B_443,A_444)
      | B_443 = A_444
      | r2_hidden(A_444,B_443)
      | ~ v3_ordinal1(B_443)
      | ~ v3_ordinal1(A_444) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1652,plain,(
    ! [A_532,B_533] :
      ( ~ r1_tarski(A_532,B_533)
      | B_533 = A_532
      | r2_hidden(A_532,B_533)
      | ~ v3_ordinal1(B_533)
      | ~ v3_ordinal1(A_532) ) ),
    inference(resolution,[status(thm)],[c_1425,c_104])).

tff(c_36,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(k1_tarski(A_35),B_36)
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1158,plain,(
    r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_1364,plain,(
    ! [D_392,B_393,A_394] :
      ( r2_hidden(D_392,B_393)
      | r2_hidden(D_392,A_394)
      | ~ r2_hidden(D_392,k2_xboole_0(A_394,B_393)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1488,plain,(
    ! [D_477,A_478] :
      ( r2_hidden(D_477,k1_tarski(A_478))
      | r2_hidden(D_477,A_478)
      | ~ r2_hidden(D_477,k1_ordinal1(A_478)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_1364])).

tff(c_1561,plain,(
    ! [A_524,D_525] :
      ( ~ r1_tarski(k1_tarski(A_524),D_525)
      | r2_hidden(D_525,A_524)
      | ~ r2_hidden(D_525,k1_ordinal1(A_524)) ) ),
    inference(resolution,[status(thm)],[c_1488,c_104])).

tff(c_1579,plain,
    ( ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_1158,c_1561])).

tff(c_1580,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1579])).

tff(c_1590,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_1580])).

tff(c_1658,plain,
    ( ~ r1_tarski('#skF_6','#skF_5')
    | '#skF_5' = '#skF_6'
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1652,c_1590])).

tff(c_1688,plain,
    ( ~ r1_tarski('#skF_6','#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_108,c_1658])).

tff(c_1696,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1688])).

tff(c_1699,plain,
    ( ~ r1_ordinal1('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_100,c_1696])).

tff(c_1703,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_108,c_1339,c_1699])).

tff(c_1704,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1688])).

tff(c_1711,plain,(
    ~ r1_ordinal1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1704,c_1157])).

tff(c_1777,plain,(
    ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1328,c_1711])).

tff(c_1783,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_1777])).

tff(c_1784,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_1579])).

tff(c_1789,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_1784,c_104])).

tff(c_1802,plain,
    ( ~ r1_ordinal1('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_100,c_1789])).

tff(c_1806,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_108,c_1339,c_1802])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:32:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.04/1.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.04/1.72  
% 4.04/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.04/1.73  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 4.04/1.73  
% 4.04/1.73  %Foreground sorts:
% 4.04/1.73  
% 4.04/1.73  
% 4.04/1.73  %Background operators:
% 4.04/1.73  
% 4.04/1.73  
% 4.04/1.73  %Foreground operators:
% 4.04/1.73  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.04/1.73  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 4.04/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.04/1.73  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.04/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.04/1.73  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.04/1.73  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.04/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.04/1.73  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.04/1.73  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 4.04/1.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.04/1.73  tff('#skF_5', type, '#skF_5': $i).
% 4.04/1.73  tff('#skF_6', type, '#skF_6': $i).
% 4.04/1.73  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.04/1.73  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.04/1.73  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 4.04/1.73  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.04/1.73  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.04/1.73  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.04/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.04/1.73  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.04/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.04/1.73  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.04/1.73  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.04/1.73  
% 4.45/1.75  tff(f_132, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 4.45/1.75  tff(f_92, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 4.45/1.75  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.45/1.75  tff(f_38, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.45/1.75  tff(f_40, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 4.45/1.75  tff(f_42, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 4.45/1.75  tff(f_44, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 4.45/1.75  tff(f_46, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 4.45/1.75  tff(f_48, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 4.45/1.75  tff(f_84, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_enumset1)).
% 4.45/1.75  tff(f_94, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 4.45/1.75  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 4.45/1.75  tff(f_102, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 4.45/1.75  tff(f_117, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 4.45/1.75  tff(f_122, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.45/1.75  tff(f_52, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.45/1.75  tff(c_106, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.45/1.75  tff(c_108, plain, (v3_ordinal1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.45/1.75  tff(c_1330, plain, (![B_369, A_370]: (r1_ordinal1(B_369, A_370) | r1_ordinal1(A_370, B_369) | ~v3_ordinal1(B_369) | ~v3_ordinal1(A_370))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.45/1.75  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.45/1.75  tff(c_22, plain, (![A_8, B_9]: (k1_enumset1(A_8, A_8, B_9)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.45/1.75  tff(c_24, plain, (![A_10, B_11, C_12]: (k2_enumset1(A_10, A_10, B_11, C_12)=k1_enumset1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.45/1.75  tff(c_26, plain, (![A_13, B_14, C_15, D_16]: (k3_enumset1(A_13, A_13, B_14, C_15, D_16)=k2_enumset1(A_13, B_14, C_15, D_16))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.45/1.75  tff(c_28, plain, (![E_21, D_20, C_19, B_18, A_17]: (k4_enumset1(A_17, A_17, B_18, C_19, D_20, E_21)=k3_enumset1(A_17, B_18, C_19, D_20, E_21))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.45/1.75  tff(c_30, plain, (![E_26, F_27, A_22, B_23, D_25, C_24]: (k5_enumset1(A_22, A_22, B_23, C_24, D_25, E_26, F_27)=k4_enumset1(A_22, B_23, C_24, D_25, E_26, F_27))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.45/1.75  tff(c_830, plain, (![A_290, B_292, E_289, C_291, D_293, F_288, G_287]: (k6_enumset1(A_290, A_290, B_292, C_291, D_293, E_289, F_288, G_287)=k5_enumset1(A_290, B_292, C_291, D_293, E_289, F_288, G_287))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.45/1.75  tff(c_44, plain, (![J_50, E_43, H_46, F_44, D_42, A_39, C_41, B_40]: (r2_hidden(J_50, k6_enumset1(A_39, B_40, C_41, D_42, E_43, F_44, J_50, H_46)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.45/1.75  tff(c_887, plain, (![E_299, B_296, C_294, F_295, D_300, G_298, A_297]: (r2_hidden(F_295, k5_enumset1(A_297, B_296, C_294, D_300, E_299, F_295, G_298)))), inference(superposition, [status(thm), theory('equality')], [c_830, c_44])).
% 4.45/1.75  tff(c_895, plain, (![F_304, B_306, C_302, E_303, D_305, A_301]: (r2_hidden(E_303, k4_enumset1(A_301, B_306, C_302, D_305, E_303, F_304)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_887])).
% 4.45/1.75  tff(c_903, plain, (![A_308, C_307, B_309, D_310, E_311]: (r2_hidden(D_310, k3_enumset1(A_308, B_309, C_307, D_310, E_311)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_895])).
% 4.45/1.75  tff(c_1010, plain, (![C_315, A_316, B_317, D_318]: (r2_hidden(C_315, k2_enumset1(A_316, B_317, C_315, D_318)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_903])).
% 4.45/1.75  tff(c_1018, plain, (![B_319, A_320, C_321]: (r2_hidden(B_319, k1_enumset1(A_320, B_319, C_321)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1010])).
% 4.45/1.75  tff(c_1026, plain, (![A_322, B_323]: (r2_hidden(A_322, k2_tarski(A_322, B_323)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1018])).
% 4.45/1.75  tff(c_1035, plain, (![A_324]: (r2_hidden(A_324, k1_tarski(A_324)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1026])).
% 4.45/1.75  tff(c_96, plain, (![A_53]: (k2_xboole_0(A_53, k1_tarski(A_53))=k1_ordinal1(A_53))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.45/1.75  tff(c_202, plain, (![D_80, B_81, A_82]: (~r2_hidden(D_80, B_81) | r2_hidden(D_80, k2_xboole_0(A_82, B_81)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.45/1.75  tff(c_211, plain, (![D_80, A_53]: (~r2_hidden(D_80, k1_tarski(A_53)) | r2_hidden(D_80, k1_ordinal1(A_53)))), inference(superposition, [status(thm), theory('equality')], [c_96, c_202])).
% 4.45/1.75  tff(c_1046, plain, (![A_324]: (r2_hidden(A_324, k1_ordinal1(A_324)))), inference(resolution, [status(thm)], [c_1035, c_211])).
% 4.45/1.75  tff(c_110, plain, (~r1_ordinal1('#skF_5', '#skF_6') | ~r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.45/1.75  tff(c_136, plain, (~r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(splitLeft, [status(thm)], [c_110])).
% 4.45/1.75  tff(c_116, plain, (r2_hidden('#skF_5', k1_ordinal1('#skF_6')) | r1_ordinal1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.45/1.75  tff(c_146, plain, (r1_ordinal1('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_136, c_116])).
% 4.45/1.75  tff(c_100, plain, (![A_54, B_55]: (r1_tarski(A_54, B_55) | ~r1_ordinal1(A_54, B_55) | ~v3_ordinal1(B_55) | ~v3_ordinal1(A_54))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.45/1.75  tff(c_400, plain, (![B_204, A_205]: (r2_hidden(B_204, A_205) | B_204=A_205 | r2_hidden(A_205, B_204) | ~v3_ordinal1(B_204) | ~v3_ordinal1(A_205))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.45/1.75  tff(c_182, plain, (![D_75, A_76, B_77]: (~r2_hidden(D_75, A_76) | r2_hidden(D_75, k2_xboole_0(A_76, B_77)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.45/1.75  tff(c_193, plain, (![D_78, A_79]: (~r2_hidden(D_78, A_79) | r2_hidden(D_78, k1_ordinal1(A_79)))), inference(superposition, [status(thm), theory('equality')], [c_96, c_182])).
% 4.45/1.75  tff(c_200, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_193, c_136])).
% 4.45/1.75  tff(c_415, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_400, c_200])).
% 4.45/1.75  tff(c_444, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_108, c_415])).
% 4.45/1.75  tff(c_453, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_444])).
% 4.45/1.75  tff(c_104, plain, (![B_60, A_59]: (~r1_tarski(B_60, A_59) | ~r2_hidden(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.45/1.75  tff(c_457, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_453, c_104])).
% 4.45/1.75  tff(c_460, plain, (~r1_ordinal1('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_100, c_457])).
% 4.45/1.75  tff(c_464, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_146, c_460])).
% 4.45/1.75  tff(c_465, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_444])).
% 4.45/1.75  tff(c_470, plain, (~r2_hidden('#skF_6', k1_ordinal1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_465, c_136])).
% 4.45/1.75  tff(c_1156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1046, c_470])).
% 4.45/1.75  tff(c_1157, plain, (~r1_ordinal1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_110])).
% 4.45/1.75  tff(c_1333, plain, (r1_ordinal1('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_1330, c_1157])).
% 4.45/1.75  tff(c_1339, plain, (r1_ordinal1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_108, c_1333])).
% 4.45/1.75  tff(c_94, plain, (![B_52, A_51]: (r1_ordinal1(B_52, A_51) | r1_ordinal1(A_51, B_52) | ~v3_ordinal1(B_52) | ~v3_ordinal1(A_51))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.45/1.75  tff(c_1328, plain, (![B_52]: (~v3_ordinal1(B_52) | r1_ordinal1(B_52, B_52))), inference(factorization, [status(thm), theory('equality')], [c_94])).
% 4.45/1.75  tff(c_1425, plain, (![B_443, A_444]: (r2_hidden(B_443, A_444) | B_443=A_444 | r2_hidden(A_444, B_443) | ~v3_ordinal1(B_443) | ~v3_ordinal1(A_444))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.45/1.75  tff(c_1652, plain, (![A_532, B_533]: (~r1_tarski(A_532, B_533) | B_533=A_532 | r2_hidden(A_532, B_533) | ~v3_ordinal1(B_533) | ~v3_ordinal1(A_532))), inference(resolution, [status(thm)], [c_1425, c_104])).
% 4.45/1.75  tff(c_36, plain, (![A_35, B_36]: (r1_tarski(k1_tarski(A_35), B_36) | ~r2_hidden(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.45/1.75  tff(c_1158, plain, (r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(splitRight, [status(thm)], [c_110])).
% 4.45/1.75  tff(c_1364, plain, (![D_392, B_393, A_394]: (r2_hidden(D_392, B_393) | r2_hidden(D_392, A_394) | ~r2_hidden(D_392, k2_xboole_0(A_394, B_393)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.45/1.75  tff(c_1488, plain, (![D_477, A_478]: (r2_hidden(D_477, k1_tarski(A_478)) | r2_hidden(D_477, A_478) | ~r2_hidden(D_477, k1_ordinal1(A_478)))), inference(superposition, [status(thm), theory('equality')], [c_96, c_1364])).
% 4.45/1.75  tff(c_1561, plain, (![A_524, D_525]: (~r1_tarski(k1_tarski(A_524), D_525) | r2_hidden(D_525, A_524) | ~r2_hidden(D_525, k1_ordinal1(A_524)))), inference(resolution, [status(thm)], [c_1488, c_104])).
% 4.45/1.75  tff(c_1579, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_5') | r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_1158, c_1561])).
% 4.45/1.75  tff(c_1580, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_1579])).
% 4.45/1.75  tff(c_1590, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_36, c_1580])).
% 4.45/1.75  tff(c_1658, plain, (~r1_tarski('#skF_6', '#skF_5') | '#skF_5'='#skF_6' | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_1652, c_1590])).
% 4.45/1.75  tff(c_1688, plain, (~r1_tarski('#skF_6', '#skF_5') | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_108, c_1658])).
% 4.45/1.75  tff(c_1696, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_1688])).
% 4.45/1.75  tff(c_1699, plain, (~r1_ordinal1('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_100, c_1696])).
% 4.45/1.75  tff(c_1703, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_108, c_1339, c_1699])).
% 4.45/1.75  tff(c_1704, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_1688])).
% 4.45/1.75  tff(c_1711, plain, (~r1_ordinal1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1704, c_1157])).
% 4.45/1.75  tff(c_1777, plain, (~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_1328, c_1711])).
% 4.45/1.75  tff(c_1783, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_1777])).
% 4.45/1.75  tff(c_1784, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_1579])).
% 4.45/1.75  tff(c_1789, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_1784, c_104])).
% 4.45/1.75  tff(c_1802, plain, (~r1_ordinal1('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_100, c_1789])).
% 4.45/1.75  tff(c_1806, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_108, c_1339, c_1802])).
% 4.45/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.45/1.75  
% 4.45/1.75  Inference rules
% 4.45/1.75  ----------------------
% 4.45/1.75  #Ref     : 0
% 4.45/1.75  #Sup     : 335
% 4.45/1.75  #Fact    : 12
% 4.45/1.75  #Define  : 0
% 4.45/1.75  #Split   : 8
% 4.45/1.75  #Chain   : 0
% 4.45/1.75  #Close   : 0
% 4.45/1.75  
% 4.45/1.75  Ordering : KBO
% 4.45/1.75  
% 4.45/1.75  Simplification rules
% 4.45/1.75  ----------------------
% 4.45/1.75  #Subsume      : 26
% 4.45/1.75  #Demod        : 49
% 4.45/1.75  #Tautology    : 74
% 4.45/1.75  #SimpNegUnit  : 2
% 4.45/1.75  #BackRed      : 12
% 4.45/1.75  
% 4.45/1.75  #Partial instantiations: 0
% 4.45/1.75  #Strategies tried      : 1
% 4.45/1.75  
% 4.45/1.75  Timing (in seconds)
% 4.45/1.75  ----------------------
% 4.45/1.75  Preprocessing        : 0.37
% 4.45/1.75  Parsing              : 0.18
% 4.45/1.75  CNF conversion       : 0.03
% 4.45/1.75  Main loop            : 0.58
% 4.45/1.75  Inferencing          : 0.20
% 4.45/1.75  Reduction            : 0.16
% 4.45/1.75  Demodulation         : 0.11
% 4.45/1.75  BG Simplification    : 0.04
% 4.45/1.75  Subsumption          : 0.15
% 4.45/1.75  Abstraction          : 0.04
% 4.45/1.75  MUC search           : 0.00
% 4.45/1.75  Cooper               : 0.00
% 4.45/1.75  Total                : 0.99
% 4.45/1.75  Index Insertion      : 0.00
% 4.45/1.75  Index Deletion       : 0.00
% 4.45/1.75  Index Matching       : 0.00
% 4.45/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
