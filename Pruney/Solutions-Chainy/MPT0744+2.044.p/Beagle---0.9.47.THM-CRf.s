%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:20 EST 2020

% Result     : Theorem 5.35s
% Output     : CNFRefutation 5.69s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 185 expanded)
%              Number of leaves         :   45 (  79 expanded)
%              Depth                    :   10
%              Number of atoms          :  158 ( 353 expanded)
%              Number of equality atoms :   32 (  49 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_5 > #skF_1 > #skF_3 > #skF_7 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

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

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

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

tff(f_92,axiom,(
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

tff(f_146,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_122,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_136,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_90,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_131,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_99,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

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

tff(c_1692,plain,(
    ! [F_321,D_326,C_324,B_325,E_322,G_320,A_323] : k6_enumset1(A_323,A_323,B_325,C_324,D_326,E_322,F_321,G_320) = k5_enumset1(A_323,B_325,C_324,D_326,E_322,F_321,G_320) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_42,plain,(
    ! [J_50,E_43,G_45,F_44,D_42,A_39,C_41,B_40] : r2_hidden(J_50,k6_enumset1(A_39,B_40,C_41,D_42,E_43,F_44,G_45,J_50)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1749,plain,(
    ! [G_329,F_332,B_333,C_330,A_328,D_331,E_327] : r2_hidden(G_329,k5_enumset1(A_328,B_333,C_330,D_331,E_327,F_332,G_329)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1692,c_42])).

tff(c_1770,plain,(
    ! [F_337,B_339,D_338,E_336,C_335,A_334] : r2_hidden(F_337,k4_enumset1(A_334,B_339,C_335,D_338,E_336,F_337)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1749])).

tff(c_1791,plain,(
    ! [A_341,D_343,C_340,B_342,E_344] : r2_hidden(E_344,k3_enumset1(A_341,B_342,C_340,D_343,E_344)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1770])).

tff(c_1967,plain,(
    ! [D_348,A_349,B_350,C_351] : r2_hidden(D_348,k2_enumset1(A_349,B_350,C_351,D_348)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1791])).

tff(c_1988,plain,(
    ! [C_352,A_353,B_354] : r2_hidden(C_352,k1_enumset1(A_353,B_354,C_352)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1967])).

tff(c_2009,plain,(
    ! [B_355,A_356] : r2_hidden(B_355,k2_tarski(A_356,B_355)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1988])).

tff(c_2030,plain,(
    ! [A_357] : r2_hidden(A_357,k1_tarski(A_357)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2009])).

tff(c_98,plain,(
    ! [A_52] : k2_xboole_0(A_52,k1_tarski(A_52)) = k1_ordinal1(A_52) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_223,plain,(
    ! [D_86,B_87,A_88] :
      ( ~ r2_hidden(D_86,B_87)
      | r2_hidden(D_86,k2_xboole_0(A_88,B_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_232,plain,(
    ! [D_86,A_52] :
      ( ~ r2_hidden(D_86,k1_tarski(A_52))
      | r2_hidden(D_86,k1_ordinal1(A_52)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_223])).

tff(c_2057,plain,(
    ! [A_357] : r2_hidden(A_357,k1_ordinal1(A_357)) ),
    inference(resolution,[status(thm)],[c_2030,c_232])).

tff(c_118,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_116,plain,(
    v3_ordinal1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_126,plain,
    ( r2_hidden('#skF_6',k1_ordinal1('#skF_7'))
    | r1_ordinal1('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_154,plain,(
    r1_ordinal1('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_108,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(A_57,B_58)
      | ~ r1_ordinal1(A_57,B_58)
      | ~ v3_ordinal1(B_58)
      | ~ v3_ordinal1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_638,plain,(
    ! [B_231,A_232] :
      ( r2_hidden(B_231,A_232)
      | B_231 = A_232
      | r2_hidden(A_232,B_231)
      | ~ v3_ordinal1(B_231)
      | ~ v3_ordinal1(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_114,plain,(
    ! [B_66,A_65] :
      ( ~ r1_tarski(B_66,A_65)
      | ~ r2_hidden(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1181,plain,(
    ! [A_294,B_295] :
      ( ~ r1_tarski(A_294,B_295)
      | B_295 = A_294
      | r2_hidden(A_294,B_295)
      | ~ v3_ordinal1(B_295)
      | ~ v3_ordinal1(A_294) ) ),
    inference(resolution,[status(thm)],[c_638,c_114])).

tff(c_234,plain,(
    ! [D_89,A_90,B_91] :
      ( ~ r2_hidden(D_89,A_90)
      | r2_hidden(D_89,k2_xboole_0(A_90,B_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_245,plain,(
    ! [D_92,A_93] :
      ( ~ r2_hidden(D_92,A_93)
      | r2_hidden(D_92,k1_ordinal1(A_93)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_234])).

tff(c_120,plain,
    ( ~ r1_ordinal1('#skF_6','#skF_7')
    | ~ r2_hidden('#skF_6',k1_ordinal1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_193,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_120])).

tff(c_252,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_245,c_193])).

tff(c_1218,plain,
    ( ~ r1_tarski('#skF_6','#skF_7')
    | '#skF_7' = '#skF_6'
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1181,c_252])).

tff(c_1239,plain,
    ( ~ r1_tarski('#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_116,c_1218])).

tff(c_1245,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1239])).

tff(c_1294,plain,
    ( ~ r1_ordinal1('#skF_6','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_108,c_1245])).

tff(c_1298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_116,c_154,c_1294])).

tff(c_1299,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1239])).

tff(c_1304,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1299,c_193])).

tff(c_2205,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2057,c_1304])).

tff(c_2207,plain,(
    ~ r1_ordinal1('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_127,plain,(
    ! [A_68] :
      ( v1_ordinal1(A_68)
      | ~ v3_ordinal1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_134,plain,(
    v1_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_116,c_127])).

tff(c_112,plain,(
    ! [B_64,A_62] :
      ( r2_hidden(B_64,A_62)
      | r1_ordinal1(A_62,B_64)
      | ~ v3_ordinal1(B_64)
      | ~ v3_ordinal1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_36,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(k1_tarski(A_35),B_36)
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2206,plain,(
    r2_hidden('#skF_6',k1_ordinal1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_2534,plain,(
    ! [D_441,B_442,A_443] :
      ( r2_hidden(D_441,B_442)
      | r2_hidden(D_441,A_443)
      | ~ r2_hidden(D_441,k2_xboole_0(A_443,B_442)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2766,plain,(
    ! [D_551,A_552] :
      ( r2_hidden(D_551,k1_tarski(A_552))
      | r2_hidden(D_551,A_552)
      | ~ r2_hidden(D_551,k1_ordinal1(A_552)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_2534])).

tff(c_2961,plain,(
    ! [A_576,D_577] :
      ( ~ r1_tarski(k1_tarski(A_576),D_577)
      | r2_hidden(D_577,A_576)
      | ~ r2_hidden(D_577,k1_ordinal1(A_576)) ) ),
    inference(resolution,[status(thm)],[c_2766,c_114])).

tff(c_3004,plain,
    ( ~ r1_tarski(k1_tarski('#skF_7'),'#skF_6')
    | r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_2206,c_2961])).

tff(c_3005,plain,(
    ~ r1_tarski(k1_tarski('#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_3004])).

tff(c_3015,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_3005])).

tff(c_3024,plain,
    ( r1_ordinal1('#skF_6','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_112,c_3015])).

tff(c_3033,plain,(
    r1_ordinal1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_116,c_3024])).

tff(c_3035,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2207,c_3033])).

tff(c_3036,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_3004])).

tff(c_100,plain,(
    ! [B_56,A_53] :
      ( r1_tarski(B_56,A_53)
      | ~ r2_hidden(B_56,A_53)
      | ~ v1_ordinal1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_3040,plain,
    ( r1_tarski('#skF_6','#skF_7')
    | ~ v1_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_3036,c_100])).

tff(c_3046,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_3040])).

tff(c_106,plain,(
    ! [A_57,B_58] :
      ( r1_ordinal1(A_57,B_58)
      | ~ r1_tarski(A_57,B_58)
      | ~ v3_ordinal1(B_58)
      | ~ v3_ordinal1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_3050,plain,
    ( r1_ordinal1('#skF_6','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_3046,c_106])).

tff(c_3053,plain,(
    r1_ordinal1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_116,c_3050])).

tff(c_3055,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2207,c_3053])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:16:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.35/2.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.35/2.05  
% 5.35/2.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.35/2.05  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_5 > #skF_1 > #skF_3 > #skF_7 > #skF_6 > #skF_2 > #skF_4
% 5.35/2.05  
% 5.35/2.05  %Foreground sorts:
% 5.35/2.05  
% 5.35/2.05  
% 5.35/2.05  %Background operators:
% 5.35/2.05  
% 5.35/2.05  
% 5.35/2.05  %Foreground operators:
% 5.35/2.05  tff('#skF_5', type, '#skF_5': $i > $i).
% 5.35/2.05  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.35/2.05  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 5.35/2.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.35/2.05  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.35/2.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.35/2.05  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.35/2.05  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 5.35/2.05  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.35/2.05  tff('#skF_7', type, '#skF_7': $i).
% 5.35/2.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.35/2.05  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.35/2.05  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 5.35/2.05  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.35/2.05  tff('#skF_6', type, '#skF_6': $i).
% 5.35/2.05  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.35/2.05  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.35/2.05  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 5.35/2.05  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.35/2.05  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 5.35/2.05  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.35/2.05  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.35/2.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.35/2.05  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.35/2.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.35/2.05  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.35/2.05  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.35/2.05  
% 5.69/2.07  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 5.69/2.07  tff(f_38, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 5.69/2.07  tff(f_40, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 5.69/2.07  tff(f_42, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 5.69/2.07  tff(f_44, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 5.69/2.07  tff(f_46, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 5.69/2.07  tff(f_48, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 5.69/2.07  tff(f_84, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_enumset1)).
% 5.69/2.07  tff(f_92, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 5.69/2.07  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 5.69/2.07  tff(f_146, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 5.69/2.07  tff(f_107, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 5.69/2.07  tff(f_122, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 5.69/2.07  tff(f_136, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.69/2.07  tff(f_90, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 5.69/2.07  tff(f_131, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 5.69/2.07  tff(f_52, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 5.69/2.07  tff(f_99, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 5.69/2.07  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.69/2.07  tff(c_22, plain, (![A_8, B_9]: (k1_enumset1(A_8, A_8, B_9)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.69/2.07  tff(c_24, plain, (![A_10, B_11, C_12]: (k2_enumset1(A_10, A_10, B_11, C_12)=k1_enumset1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.69/2.07  tff(c_26, plain, (![A_13, B_14, C_15, D_16]: (k3_enumset1(A_13, A_13, B_14, C_15, D_16)=k2_enumset1(A_13, B_14, C_15, D_16))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.69/2.07  tff(c_28, plain, (![E_21, D_20, C_19, B_18, A_17]: (k4_enumset1(A_17, A_17, B_18, C_19, D_20, E_21)=k3_enumset1(A_17, B_18, C_19, D_20, E_21))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.69/2.07  tff(c_30, plain, (![E_26, F_27, A_22, B_23, D_25, C_24]: (k5_enumset1(A_22, A_22, B_23, C_24, D_25, E_26, F_27)=k4_enumset1(A_22, B_23, C_24, D_25, E_26, F_27))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.69/2.07  tff(c_1692, plain, (![F_321, D_326, C_324, B_325, E_322, G_320, A_323]: (k6_enumset1(A_323, A_323, B_325, C_324, D_326, E_322, F_321, G_320)=k5_enumset1(A_323, B_325, C_324, D_326, E_322, F_321, G_320))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.69/2.07  tff(c_42, plain, (![J_50, E_43, G_45, F_44, D_42, A_39, C_41, B_40]: (r2_hidden(J_50, k6_enumset1(A_39, B_40, C_41, D_42, E_43, F_44, G_45, J_50)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.69/2.07  tff(c_1749, plain, (![G_329, F_332, B_333, C_330, A_328, D_331, E_327]: (r2_hidden(G_329, k5_enumset1(A_328, B_333, C_330, D_331, E_327, F_332, G_329)))), inference(superposition, [status(thm), theory('equality')], [c_1692, c_42])).
% 5.69/2.07  tff(c_1770, plain, (![F_337, B_339, D_338, E_336, C_335, A_334]: (r2_hidden(F_337, k4_enumset1(A_334, B_339, C_335, D_338, E_336, F_337)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1749])).
% 5.69/2.07  tff(c_1791, plain, (![A_341, D_343, C_340, B_342, E_344]: (r2_hidden(E_344, k3_enumset1(A_341, B_342, C_340, D_343, E_344)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1770])).
% 5.69/2.07  tff(c_1967, plain, (![D_348, A_349, B_350, C_351]: (r2_hidden(D_348, k2_enumset1(A_349, B_350, C_351, D_348)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1791])).
% 5.69/2.07  tff(c_1988, plain, (![C_352, A_353, B_354]: (r2_hidden(C_352, k1_enumset1(A_353, B_354, C_352)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1967])).
% 5.69/2.07  tff(c_2009, plain, (![B_355, A_356]: (r2_hidden(B_355, k2_tarski(A_356, B_355)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1988])).
% 5.69/2.07  tff(c_2030, plain, (![A_357]: (r2_hidden(A_357, k1_tarski(A_357)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2009])).
% 5.69/2.07  tff(c_98, plain, (![A_52]: (k2_xboole_0(A_52, k1_tarski(A_52))=k1_ordinal1(A_52))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.69/2.07  tff(c_223, plain, (![D_86, B_87, A_88]: (~r2_hidden(D_86, B_87) | r2_hidden(D_86, k2_xboole_0(A_88, B_87)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.69/2.07  tff(c_232, plain, (![D_86, A_52]: (~r2_hidden(D_86, k1_tarski(A_52)) | r2_hidden(D_86, k1_ordinal1(A_52)))), inference(superposition, [status(thm), theory('equality')], [c_98, c_223])).
% 5.69/2.07  tff(c_2057, plain, (![A_357]: (r2_hidden(A_357, k1_ordinal1(A_357)))), inference(resolution, [status(thm)], [c_2030, c_232])).
% 5.69/2.07  tff(c_118, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.69/2.07  tff(c_116, plain, (v3_ordinal1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.69/2.07  tff(c_126, plain, (r2_hidden('#skF_6', k1_ordinal1('#skF_7')) | r1_ordinal1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.69/2.07  tff(c_154, plain, (r1_ordinal1('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_126])).
% 5.69/2.07  tff(c_108, plain, (![A_57, B_58]: (r1_tarski(A_57, B_58) | ~r1_ordinal1(A_57, B_58) | ~v3_ordinal1(B_58) | ~v3_ordinal1(A_57))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.69/2.07  tff(c_638, plain, (![B_231, A_232]: (r2_hidden(B_231, A_232) | B_231=A_232 | r2_hidden(A_232, B_231) | ~v3_ordinal1(B_231) | ~v3_ordinal1(A_232))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.69/2.07  tff(c_114, plain, (![B_66, A_65]: (~r1_tarski(B_66, A_65) | ~r2_hidden(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.69/2.07  tff(c_1181, plain, (![A_294, B_295]: (~r1_tarski(A_294, B_295) | B_295=A_294 | r2_hidden(A_294, B_295) | ~v3_ordinal1(B_295) | ~v3_ordinal1(A_294))), inference(resolution, [status(thm)], [c_638, c_114])).
% 5.69/2.07  tff(c_234, plain, (![D_89, A_90, B_91]: (~r2_hidden(D_89, A_90) | r2_hidden(D_89, k2_xboole_0(A_90, B_91)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.69/2.07  tff(c_245, plain, (![D_92, A_93]: (~r2_hidden(D_92, A_93) | r2_hidden(D_92, k1_ordinal1(A_93)))), inference(superposition, [status(thm), theory('equality')], [c_98, c_234])).
% 5.69/2.07  tff(c_120, plain, (~r1_ordinal1('#skF_6', '#skF_7') | ~r2_hidden('#skF_6', k1_ordinal1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.69/2.07  tff(c_193, plain, (~r2_hidden('#skF_6', k1_ordinal1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_120])).
% 5.69/2.07  tff(c_252, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_245, c_193])).
% 5.69/2.07  tff(c_1218, plain, (~r1_tarski('#skF_6', '#skF_7') | '#skF_7'='#skF_6' | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_1181, c_252])).
% 5.69/2.07  tff(c_1239, plain, (~r1_tarski('#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_116, c_1218])).
% 5.69/2.07  tff(c_1245, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_1239])).
% 5.69/2.07  tff(c_1294, plain, (~r1_ordinal1('#skF_6', '#skF_7') | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_108, c_1245])).
% 5.69/2.07  tff(c_1298, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_116, c_154, c_1294])).
% 5.69/2.07  tff(c_1299, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_1239])).
% 5.69/2.07  tff(c_1304, plain, (~r2_hidden('#skF_6', k1_ordinal1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1299, c_193])).
% 5.69/2.07  tff(c_2205, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2057, c_1304])).
% 5.69/2.07  tff(c_2207, plain, (~r1_ordinal1('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_126])).
% 5.69/2.07  tff(c_127, plain, (![A_68]: (v1_ordinal1(A_68) | ~v3_ordinal1(A_68))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.69/2.07  tff(c_134, plain, (v1_ordinal1('#skF_7')), inference(resolution, [status(thm)], [c_116, c_127])).
% 5.69/2.07  tff(c_112, plain, (![B_64, A_62]: (r2_hidden(B_64, A_62) | r1_ordinal1(A_62, B_64) | ~v3_ordinal1(B_64) | ~v3_ordinal1(A_62))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.69/2.07  tff(c_36, plain, (![A_35, B_36]: (r1_tarski(k1_tarski(A_35), B_36) | ~r2_hidden(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.69/2.07  tff(c_2206, plain, (r2_hidden('#skF_6', k1_ordinal1('#skF_7'))), inference(splitRight, [status(thm)], [c_126])).
% 5.69/2.07  tff(c_2534, plain, (![D_441, B_442, A_443]: (r2_hidden(D_441, B_442) | r2_hidden(D_441, A_443) | ~r2_hidden(D_441, k2_xboole_0(A_443, B_442)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.69/2.07  tff(c_2766, plain, (![D_551, A_552]: (r2_hidden(D_551, k1_tarski(A_552)) | r2_hidden(D_551, A_552) | ~r2_hidden(D_551, k1_ordinal1(A_552)))), inference(superposition, [status(thm), theory('equality')], [c_98, c_2534])).
% 5.69/2.07  tff(c_2961, plain, (![A_576, D_577]: (~r1_tarski(k1_tarski(A_576), D_577) | r2_hidden(D_577, A_576) | ~r2_hidden(D_577, k1_ordinal1(A_576)))), inference(resolution, [status(thm)], [c_2766, c_114])).
% 5.69/2.07  tff(c_3004, plain, (~r1_tarski(k1_tarski('#skF_7'), '#skF_6') | r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_2206, c_2961])).
% 5.69/2.07  tff(c_3005, plain, (~r1_tarski(k1_tarski('#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_3004])).
% 5.69/2.07  tff(c_3015, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_36, c_3005])).
% 5.69/2.07  tff(c_3024, plain, (r1_ordinal1('#skF_6', '#skF_7') | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_112, c_3015])).
% 5.69/2.07  tff(c_3033, plain, (r1_ordinal1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_116, c_3024])).
% 5.69/2.07  tff(c_3035, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2207, c_3033])).
% 5.69/2.07  tff(c_3036, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_3004])).
% 5.69/2.07  tff(c_100, plain, (![B_56, A_53]: (r1_tarski(B_56, A_53) | ~r2_hidden(B_56, A_53) | ~v1_ordinal1(A_53))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.69/2.07  tff(c_3040, plain, (r1_tarski('#skF_6', '#skF_7') | ~v1_ordinal1('#skF_7')), inference(resolution, [status(thm)], [c_3036, c_100])).
% 5.69/2.07  tff(c_3046, plain, (r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_3040])).
% 5.69/2.07  tff(c_106, plain, (![A_57, B_58]: (r1_ordinal1(A_57, B_58) | ~r1_tarski(A_57, B_58) | ~v3_ordinal1(B_58) | ~v3_ordinal1(A_57))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.69/2.07  tff(c_3050, plain, (r1_ordinal1('#skF_6', '#skF_7') | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_3046, c_106])).
% 5.69/2.07  tff(c_3053, plain, (r1_ordinal1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_116, c_3050])).
% 5.69/2.07  tff(c_3055, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2207, c_3053])).
% 5.69/2.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.69/2.07  
% 5.69/2.07  Inference rules
% 5.69/2.07  ----------------------
% 5.69/2.07  #Ref     : 0
% 5.69/2.07  #Sup     : 606
% 5.69/2.07  #Fact    : 8
% 5.69/2.07  #Define  : 0
% 5.69/2.07  #Split   : 6
% 5.69/2.07  #Chain   : 0
% 5.69/2.07  #Close   : 0
% 5.69/2.07  
% 5.69/2.07  Ordering : KBO
% 5.69/2.07  
% 5.69/2.07  Simplification rules
% 5.69/2.07  ----------------------
% 5.69/2.07  #Subsume      : 46
% 5.69/2.07  #Demod        : 65
% 5.69/2.07  #Tautology    : 81
% 5.69/2.07  #SimpNegUnit  : 2
% 5.69/2.07  #BackRed      : 9
% 5.69/2.07  
% 5.69/2.07  #Partial instantiations: 0
% 5.69/2.07  #Strategies tried      : 1
% 5.69/2.07  
% 5.69/2.07  Timing (in seconds)
% 5.69/2.07  ----------------------
% 5.69/2.07  Preprocessing        : 0.42
% 5.69/2.07  Parsing              : 0.19
% 5.69/2.07  CNF conversion       : 0.03
% 5.69/2.07  Main loop            : 0.82
% 5.69/2.07  Inferencing          : 0.29
% 5.69/2.07  Reduction            : 0.23
% 5.69/2.07  Demodulation         : 0.16
% 5.69/2.07  BG Simplification    : 0.05
% 5.69/2.07  Subsumption          : 0.19
% 5.69/2.07  Abstraction          : 0.07
% 5.69/2.07  MUC search           : 0.00
% 5.69/2.07  Cooper               : 0.00
% 5.69/2.07  Total                : 1.28
% 5.69/2.08  Index Insertion      : 0.00
% 5.69/2.08  Index Deletion       : 0.00
% 5.69/2.08  Index Matching       : 0.00
% 5.69/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
