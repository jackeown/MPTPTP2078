%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:01 EST 2020

% Result     : Theorem 6.91s
% Output     : CNFRefutation 6.91s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 472 expanded)
%              Number of leaves         :   27 ( 164 expanded)
%              Depth                    :   15
%              Number of atoms          :  213 (1167 expanded)
%              Number of equality atoms :    5 (  50 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ! [D] :
          ( v1_relat_1(D)
         => ( ( r1_tarski(C,D)
              & r1_tarski(A,B) )
           => r1_tarski(k7_relat_1(C,A),k7_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_relat_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,(
    ! [A_40,B_41] :
      ( ~ r2_hidden('#skF_1'(A_40,B_41),B_41)
      | r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_57,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_52])).

tff(c_26,plain,(
    ! [B_29,A_28] :
      ( r1_tarski(k7_relat_1(B_29,A_28),B_29)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_59,plain,(
    ! [C_43,B_44,A_45] :
      ( r2_hidden(C_43,B_44)
      | ~ r2_hidden(C_43,A_45)
      | ~ r1_tarski(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_77,plain,(
    ! [A_51,B_52,B_53] :
      ( r2_hidden('#skF_1'(A_51,B_52),B_53)
      | ~ r1_tarski(A_51,B_53)
      | r1_tarski(A_51,B_52) ) ),
    inference(resolution,[status(thm)],[c_6,c_59])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_118,plain,(
    ! [A_61,B_62,B_63,B_64] :
      ( r2_hidden('#skF_1'(A_61,B_62),B_63)
      | ~ r1_tarski(B_64,B_63)
      | ~ r1_tarski(A_61,B_64)
      | r1_tarski(A_61,B_62) ) ),
    inference(resolution,[status(thm)],[c_77,c_2])).

tff(c_145,plain,(
    ! [A_68,B_69,B_70,A_71] :
      ( r2_hidden('#skF_1'(A_68,B_69),B_70)
      | ~ r1_tarski(A_68,k7_relat_1(B_70,A_71))
      | r1_tarski(A_68,B_69)
      | ~ v1_relat_1(B_70) ) ),
    inference(resolution,[status(thm)],[c_26,c_118])).

tff(c_2527,plain,(
    ! [B_315,A_316,B_317] :
      ( r2_hidden('#skF_1'(k7_relat_1(B_315,A_316),B_317),B_315)
      | r1_tarski(k7_relat_1(B_315,A_316),B_317)
      | ~ v1_relat_1(B_315) ) ),
    inference(resolution,[status(thm)],[c_57,c_145])).

tff(c_2586,plain,(
    ! [B_324,A_325,B_326,B_327] :
      ( r2_hidden('#skF_1'(k7_relat_1(B_324,A_325),B_326),B_327)
      | ~ r1_tarski(B_324,B_327)
      | r1_tarski(k7_relat_1(B_324,A_325),B_326)
      | ~ v1_relat_1(B_324) ) ),
    inference(resolution,[status(thm)],[c_2527,c_2])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2597,plain,(
    ! [B_324,B_327,A_325] :
      ( ~ r1_tarski(B_324,B_327)
      | r1_tarski(k7_relat_1(B_324,A_325),B_327)
      | ~ v1_relat_1(B_324) ) ),
    inference(resolution,[status(thm)],[c_2586,c_4])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( v1_relat_1(k7_relat_1(A_13,B_14))
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_20,plain,(
    ! [B_24,A_23] :
      ( k2_relat_1(k7_relat_1(B_24,A_23)) = k9_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_111,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(k2_relat_1(A_59),k2_relat_1(B_60))
      | ~ r1_tarski(A_59,B_60)
      | ~ v1_relat_1(B_60)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2622,plain,(
    ! [A_333,B_334,A_335] :
      ( r1_tarski(k2_relat_1(A_333),k9_relat_1(B_334,A_335))
      | ~ r1_tarski(A_333,k7_relat_1(B_334,A_335))
      | ~ v1_relat_1(k7_relat_1(B_334,A_335))
      | ~ v1_relat_1(A_333)
      | ~ v1_relat_1(B_334) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_111])).

tff(c_87,plain,(
    ! [C_56,A_57,B_58] :
      ( k7_relat_1(k7_relat_1(C_56,A_57),B_58) = k7_relat_1(C_56,k3_xboole_0(A_57,B_58))
      | ~ v1_relat_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_99,plain,(
    ! [C_56,A_57,B_58] :
      ( r1_tarski(k7_relat_1(C_56,k3_xboole_0(A_57,B_58)),k7_relat_1(C_56,A_57))
      | ~ v1_relat_1(k7_relat_1(C_56,A_57))
      | ~ v1_relat_1(C_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_26])).

tff(c_223,plain,(
    ! [A_86,B_87,A_88] :
      ( r1_tarski(k2_relat_1(A_86),k9_relat_1(B_87,A_88))
      | ~ r1_tarski(A_86,k7_relat_1(B_87,A_88))
      | ~ v1_relat_1(k7_relat_1(B_87,A_88))
      | ~ v1_relat_1(A_86)
      | ~ v1_relat_1(B_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_111])).

tff(c_2409,plain,(
    ! [B_307,A_308,B_309,A_310] :
      ( r1_tarski(k9_relat_1(B_307,A_308),k9_relat_1(B_309,A_310))
      | ~ r1_tarski(k7_relat_1(B_307,A_308),k7_relat_1(B_309,A_310))
      | ~ v1_relat_1(k7_relat_1(B_309,A_310))
      | ~ v1_relat_1(k7_relat_1(B_307,A_308))
      | ~ v1_relat_1(B_309)
      | ~ v1_relat_1(B_307) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_223])).

tff(c_72,plain,(
    ! [A_48,B_49,C_50] :
      ( r1_tarski(A_48,k3_xboole_0(B_49,C_50))
      | ~ r1_tarski(A_48,C_50)
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_28,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4',k3_xboole_0('#skF_2','#skF_3')),k3_xboole_0(k9_relat_1('#skF_4','#skF_2'),k9_relat_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_76,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4',k3_xboole_0('#skF_2','#skF_3')),k9_relat_1('#skF_4','#skF_3'))
    | ~ r1_tarski(k9_relat_1('#skF_4',k3_xboole_0('#skF_2','#skF_3')),k9_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_72,c_28])).

tff(c_159,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4',k3_xboole_0('#skF_2','#skF_3')),k9_relat_1('#skF_4','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_2422,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_4',k3_xboole_0('#skF_2','#skF_3')),k7_relat_1('#skF_4','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_4',k3_xboole_0('#skF_2','#skF_3')))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2409,c_159])).

tff(c_2450,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_4',k3_xboole_0('#skF_2','#skF_3')),k7_relat_1('#skF_4','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_4',k3_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2422])).

tff(c_2452,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4',k3_xboole_0('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2450])).

tff(c_2455,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_2452])).

tff(c_2459,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2455])).

tff(c_2460,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2'))
    | ~ r1_tarski(k7_relat_1('#skF_4',k3_xboole_0('#skF_2','#skF_3')),k7_relat_1('#skF_4','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2450])).

tff(c_2462,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4',k3_xboole_0('#skF_2','#skF_3')),k7_relat_1('#skF_4','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2460])).

tff(c_2477,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_99,c_2462])).

tff(c_2492,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2477])).

tff(c_2495,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_2492])).

tff(c_2499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2495])).

tff(c_2500,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2460])).

tff(c_2504,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_2500])).

tff(c_2508,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2504])).

tff(c_2510,plain,(
    r1_tarski(k9_relat_1('#skF_4',k3_xboole_0('#skF_2','#skF_3')),k9_relat_1('#skF_4','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_84,plain,(
    ! [A_51,B_52,B_2,B_53] :
      ( r2_hidden('#skF_1'(A_51,B_52),B_2)
      | ~ r1_tarski(B_53,B_2)
      | ~ r1_tarski(A_51,B_53)
      | r1_tarski(A_51,B_52) ) ),
    inference(resolution,[status(thm)],[c_77,c_2])).

tff(c_2565,plain,(
    ! [A_321,B_322] :
      ( r2_hidden('#skF_1'(A_321,B_322),k9_relat_1('#skF_4','#skF_2'))
      | ~ r1_tarski(A_321,k9_relat_1('#skF_4',k3_xboole_0('#skF_2','#skF_3')))
      | r1_tarski(A_321,B_322) ) ),
    inference(resolution,[status(thm)],[c_2510,c_84])).

tff(c_2573,plain,(
    ! [A_321] :
      ( ~ r1_tarski(A_321,k9_relat_1('#skF_4',k3_xboole_0('#skF_2','#skF_3')))
      | r1_tarski(A_321,k9_relat_1('#skF_4','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_2565,c_4])).

tff(c_2626,plain,(
    ! [A_333] :
      ( r1_tarski(k2_relat_1(A_333),k9_relat_1('#skF_4','#skF_2'))
      | ~ r1_tarski(A_333,k7_relat_1('#skF_4',k3_xboole_0('#skF_2','#skF_3')))
      | ~ v1_relat_1(k7_relat_1('#skF_4',k3_xboole_0('#skF_2','#skF_3')))
      | ~ v1_relat_1(A_333)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2622,c_2573])).

tff(c_2637,plain,(
    ! [A_333] :
      ( r1_tarski(k2_relat_1(A_333),k9_relat_1('#skF_4','#skF_2'))
      | ~ r1_tarski(A_333,k7_relat_1('#skF_4',k3_xboole_0('#skF_2','#skF_3')))
      | ~ v1_relat_1(k7_relat_1('#skF_4',k3_xboole_0('#skF_2','#skF_3')))
      | ~ v1_relat_1(A_333) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2626])).

tff(c_3164,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4',k3_xboole_0('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2637])).

tff(c_3167,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_3164])).

tff(c_3171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3167])).

tff(c_3173,plain,(
    v1_relat_1(k7_relat_1('#skF_4',k3_xboole_0('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2637])).

tff(c_4434,plain,(
    ! [B_529,A_530,B_531,A_532] :
      ( r1_tarski(k9_relat_1(B_529,A_530),k9_relat_1(B_531,A_532))
      | ~ r1_tarski(k7_relat_1(B_529,A_530),k7_relat_1(B_531,A_532))
      | ~ v1_relat_1(k7_relat_1(B_531,A_532))
      | ~ v1_relat_1(k7_relat_1(B_529,A_530))
      | ~ v1_relat_1(B_531)
      | ~ v1_relat_1(B_529) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2622])).

tff(c_2509,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4',k3_xboole_0('#skF_2','#skF_3')),k9_relat_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_4458,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_4',k3_xboole_0('#skF_2','#skF_3')),k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_4',k3_xboole_0('#skF_2','#skF_3')))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4434,c_2509])).

tff(c_4497,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_4',k3_xboole_0('#skF_2','#skF_3')),k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3173,c_4458])).

tff(c_4499,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_4497])).

tff(c_4502,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_4499])).

tff(c_4506,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_4502])).

tff(c_4508,plain,(
    v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_4497])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8] :
      ( r1_tarski(A_6,k3_xboole_0(B_7,C_8))
      | ~ r1_tarski(A_6,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2738,plain,(
    ! [A_361,C_357,B_358,B_359,A_360] :
      ( r2_hidden('#skF_1'(A_360,B_358),k3_xboole_0(B_359,C_357))
      | ~ r1_tarski(A_360,A_361)
      | r1_tarski(A_360,B_358)
      | ~ r1_tarski(A_361,C_357)
      | ~ r1_tarski(A_361,B_359) ) ),
    inference(resolution,[status(thm)],[c_8,c_118])).

tff(c_2903,plain,(
    ! [B_379,B_380,C_381] :
      ( r2_hidden('#skF_1'(k9_relat_1('#skF_4',k3_xboole_0('#skF_2','#skF_3')),B_379),k3_xboole_0(B_380,C_381))
      | r1_tarski(k9_relat_1('#skF_4',k3_xboole_0('#skF_2','#skF_3')),B_379)
      | ~ r1_tarski(k9_relat_1('#skF_4','#skF_2'),C_381)
      | ~ r1_tarski(k9_relat_1('#skF_4','#skF_2'),B_380) ) ),
    inference(resolution,[status(thm)],[c_2510,c_2738])).

tff(c_2933,plain,(
    ! [B_385,C_386] :
      ( r1_tarski(k9_relat_1('#skF_4',k3_xboole_0('#skF_2','#skF_3')),k3_xboole_0(B_385,C_386))
      | ~ r1_tarski(k9_relat_1('#skF_4','#skF_2'),C_386)
      | ~ r1_tarski(k9_relat_1('#skF_4','#skF_2'),B_385) ) ),
    inference(resolution,[status(thm)],[c_2903,c_4])).

tff(c_2940,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_2'),k9_relat_1('#skF_4','#skF_3'))
    | ~ r1_tarski(k9_relat_1('#skF_4','#skF_2'),k9_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2933,c_28])).

tff(c_2945,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_2'),k9_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_2940])).

tff(c_4446,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_4','#skF_2'),k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4434,c_2945])).

tff(c_4487,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_4','#skF_2'),k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_4446])).

tff(c_4510,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_4','#skF_2'),k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4508,c_4487])).

tff(c_4511,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_4510])).

tff(c_4514,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_4511])).

tff(c_4518,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_4514])).

tff(c_4520,plain,(
    v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_4510])).

tff(c_16,plain,(
    ! [C_17,A_15,B_16] :
      ( k7_relat_1(k7_relat_1(C_17,A_15),B_16) = k7_relat_1(C_17,k3_xboole_0(A_15,B_16))
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2514,plain,(
    ! [C_311,A_312,D_313,B_314] :
      ( r1_tarski(k7_relat_1(C_311,A_312),k7_relat_1(D_313,B_314))
      | ~ r1_tarski(A_312,B_314)
      | ~ r1_tarski(C_311,D_313)
      | ~ v1_relat_1(D_313)
      | ~ v1_relat_1(C_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2521,plain,(
    ! [B_16,A_15,D_313,B_314,C_17] :
      ( r1_tarski(k7_relat_1(C_17,k3_xboole_0(A_15,B_16)),k7_relat_1(D_313,B_314))
      | ~ r1_tarski(B_16,B_314)
      | ~ r1_tarski(k7_relat_1(C_17,A_15),D_313)
      | ~ v1_relat_1(D_313)
      | ~ v1_relat_1(k7_relat_1(C_17,A_15))
      | ~ v1_relat_1(C_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2514])).

tff(c_4507,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4',k3_xboole_0('#skF_2','#skF_3')),k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_4497])).

tff(c_4535,plain,
    ( ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski(k7_relat_1('#skF_4','#skF_2'),'#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2521,c_4507])).

tff(c_4547,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4','#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_4520,c_57,c_4535])).

tff(c_4559,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2597,c_4547])).

tff(c_4566,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_57,c_4559])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:33:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.91/2.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.91/2.48  
% 6.91/2.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.91/2.49  %$ r2_hidden > r1_tarski > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.91/2.49  
% 6.91/2.49  %Foreground sorts:
% 6.91/2.49  
% 6.91/2.49  
% 6.91/2.49  %Background operators:
% 6.91/2.49  
% 6.91/2.49  
% 6.91/2.49  %Foreground operators:
% 6.91/2.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.91/2.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.91/2.49  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.91/2.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.91/2.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.91/2.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.91/2.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.91/2.49  tff('#skF_2', type, '#skF_2': $i).
% 6.91/2.49  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.91/2.49  tff('#skF_3', type, '#skF_3': $i).
% 6.91/2.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.91/2.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.91/2.49  tff('#skF_4', type, '#skF_4': $i).
% 6.91/2.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.91/2.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.91/2.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.91/2.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.91/2.49  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.91/2.49  
% 6.91/2.51  tff(f_85, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_relat_1)).
% 6.91/2.51  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.91/2.51  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 6.91/2.51  tff(f_46, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 6.91/2.51  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 6.91/2.51  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 6.91/2.51  tff(f_50, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 6.91/2.51  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 6.91/2.51  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k7_relat_1(C, A), k7_relat_1(D, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_relat_1)).
% 6.91/2.51  tff(c_30, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.91/2.51  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.91/2.51  tff(c_52, plain, (![A_40, B_41]: (~r2_hidden('#skF_1'(A_40, B_41), B_41) | r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.91/2.51  tff(c_57, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_52])).
% 6.91/2.51  tff(c_26, plain, (![B_29, A_28]: (r1_tarski(k7_relat_1(B_29, A_28), B_29) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.91/2.51  tff(c_59, plain, (![C_43, B_44, A_45]: (r2_hidden(C_43, B_44) | ~r2_hidden(C_43, A_45) | ~r1_tarski(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.91/2.51  tff(c_77, plain, (![A_51, B_52, B_53]: (r2_hidden('#skF_1'(A_51, B_52), B_53) | ~r1_tarski(A_51, B_53) | r1_tarski(A_51, B_52))), inference(resolution, [status(thm)], [c_6, c_59])).
% 6.91/2.51  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.91/2.51  tff(c_118, plain, (![A_61, B_62, B_63, B_64]: (r2_hidden('#skF_1'(A_61, B_62), B_63) | ~r1_tarski(B_64, B_63) | ~r1_tarski(A_61, B_64) | r1_tarski(A_61, B_62))), inference(resolution, [status(thm)], [c_77, c_2])).
% 6.91/2.51  tff(c_145, plain, (![A_68, B_69, B_70, A_71]: (r2_hidden('#skF_1'(A_68, B_69), B_70) | ~r1_tarski(A_68, k7_relat_1(B_70, A_71)) | r1_tarski(A_68, B_69) | ~v1_relat_1(B_70))), inference(resolution, [status(thm)], [c_26, c_118])).
% 6.91/2.51  tff(c_2527, plain, (![B_315, A_316, B_317]: (r2_hidden('#skF_1'(k7_relat_1(B_315, A_316), B_317), B_315) | r1_tarski(k7_relat_1(B_315, A_316), B_317) | ~v1_relat_1(B_315))), inference(resolution, [status(thm)], [c_57, c_145])).
% 6.91/2.51  tff(c_2586, plain, (![B_324, A_325, B_326, B_327]: (r2_hidden('#skF_1'(k7_relat_1(B_324, A_325), B_326), B_327) | ~r1_tarski(B_324, B_327) | r1_tarski(k7_relat_1(B_324, A_325), B_326) | ~v1_relat_1(B_324))), inference(resolution, [status(thm)], [c_2527, c_2])).
% 6.91/2.51  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.91/2.51  tff(c_2597, plain, (![B_324, B_327, A_325]: (~r1_tarski(B_324, B_327) | r1_tarski(k7_relat_1(B_324, A_325), B_327) | ~v1_relat_1(B_324))), inference(resolution, [status(thm)], [c_2586, c_4])).
% 6.91/2.51  tff(c_14, plain, (![A_13, B_14]: (v1_relat_1(k7_relat_1(A_13, B_14)) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.91/2.51  tff(c_20, plain, (![B_24, A_23]: (k2_relat_1(k7_relat_1(B_24, A_23))=k9_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.91/2.51  tff(c_111, plain, (![A_59, B_60]: (r1_tarski(k2_relat_1(A_59), k2_relat_1(B_60)) | ~r1_tarski(A_59, B_60) | ~v1_relat_1(B_60) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.91/2.51  tff(c_2622, plain, (![A_333, B_334, A_335]: (r1_tarski(k2_relat_1(A_333), k9_relat_1(B_334, A_335)) | ~r1_tarski(A_333, k7_relat_1(B_334, A_335)) | ~v1_relat_1(k7_relat_1(B_334, A_335)) | ~v1_relat_1(A_333) | ~v1_relat_1(B_334))), inference(superposition, [status(thm), theory('equality')], [c_20, c_111])).
% 6.91/2.51  tff(c_87, plain, (![C_56, A_57, B_58]: (k7_relat_1(k7_relat_1(C_56, A_57), B_58)=k7_relat_1(C_56, k3_xboole_0(A_57, B_58)) | ~v1_relat_1(C_56))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.91/2.51  tff(c_99, plain, (![C_56, A_57, B_58]: (r1_tarski(k7_relat_1(C_56, k3_xboole_0(A_57, B_58)), k7_relat_1(C_56, A_57)) | ~v1_relat_1(k7_relat_1(C_56, A_57)) | ~v1_relat_1(C_56))), inference(superposition, [status(thm), theory('equality')], [c_87, c_26])).
% 6.91/2.51  tff(c_223, plain, (![A_86, B_87, A_88]: (r1_tarski(k2_relat_1(A_86), k9_relat_1(B_87, A_88)) | ~r1_tarski(A_86, k7_relat_1(B_87, A_88)) | ~v1_relat_1(k7_relat_1(B_87, A_88)) | ~v1_relat_1(A_86) | ~v1_relat_1(B_87))), inference(superposition, [status(thm), theory('equality')], [c_20, c_111])).
% 6.91/2.51  tff(c_2409, plain, (![B_307, A_308, B_309, A_310]: (r1_tarski(k9_relat_1(B_307, A_308), k9_relat_1(B_309, A_310)) | ~r1_tarski(k7_relat_1(B_307, A_308), k7_relat_1(B_309, A_310)) | ~v1_relat_1(k7_relat_1(B_309, A_310)) | ~v1_relat_1(k7_relat_1(B_307, A_308)) | ~v1_relat_1(B_309) | ~v1_relat_1(B_307))), inference(superposition, [status(thm), theory('equality')], [c_20, c_223])).
% 6.91/2.51  tff(c_72, plain, (![A_48, B_49, C_50]: (r1_tarski(A_48, k3_xboole_0(B_49, C_50)) | ~r1_tarski(A_48, C_50) | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.91/2.51  tff(c_28, plain, (~r1_tarski(k9_relat_1('#skF_4', k3_xboole_0('#skF_2', '#skF_3')), k3_xboole_0(k9_relat_1('#skF_4', '#skF_2'), k9_relat_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.91/2.51  tff(c_76, plain, (~r1_tarski(k9_relat_1('#skF_4', k3_xboole_0('#skF_2', '#skF_3')), k9_relat_1('#skF_4', '#skF_3')) | ~r1_tarski(k9_relat_1('#skF_4', k3_xboole_0('#skF_2', '#skF_3')), k9_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_72, c_28])).
% 6.91/2.51  tff(c_159, plain, (~r1_tarski(k9_relat_1('#skF_4', k3_xboole_0('#skF_2', '#skF_3')), k9_relat_1('#skF_4', '#skF_2'))), inference(splitLeft, [status(thm)], [c_76])).
% 6.91/2.51  tff(c_2422, plain, (~r1_tarski(k7_relat_1('#skF_4', k3_xboole_0('#skF_2', '#skF_3')), k7_relat_1('#skF_4', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_4', k3_xboole_0('#skF_2', '#skF_3'))) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2409, c_159])).
% 6.91/2.51  tff(c_2450, plain, (~r1_tarski(k7_relat_1('#skF_4', k3_xboole_0('#skF_2', '#skF_3')), k7_relat_1('#skF_4', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_4', k3_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2422])).
% 6.91/2.51  tff(c_2452, plain, (~v1_relat_1(k7_relat_1('#skF_4', k3_xboole_0('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_2450])).
% 6.91/2.51  tff(c_2455, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_2452])).
% 6.91/2.51  tff(c_2459, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_2455])).
% 6.91/2.51  tff(c_2460, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_2')) | ~r1_tarski(k7_relat_1('#skF_4', k3_xboole_0('#skF_2', '#skF_3')), k7_relat_1('#skF_4', '#skF_2'))), inference(splitRight, [status(thm)], [c_2450])).
% 6.91/2.51  tff(c_2462, plain, (~r1_tarski(k7_relat_1('#skF_4', k3_xboole_0('#skF_2', '#skF_3')), k7_relat_1('#skF_4', '#skF_2'))), inference(splitLeft, [status(thm)], [c_2460])).
% 6.91/2.51  tff(c_2477, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_2')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_99, c_2462])).
% 6.91/2.51  tff(c_2492, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2477])).
% 6.91/2.51  tff(c_2495, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_2492])).
% 6.91/2.51  tff(c_2499, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_2495])).
% 6.91/2.51  tff(c_2500, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(splitRight, [status(thm)], [c_2460])).
% 6.91/2.51  tff(c_2504, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_2500])).
% 6.91/2.51  tff(c_2508, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_2504])).
% 6.91/2.51  tff(c_2510, plain, (r1_tarski(k9_relat_1('#skF_4', k3_xboole_0('#skF_2', '#skF_3')), k9_relat_1('#skF_4', '#skF_2'))), inference(splitRight, [status(thm)], [c_76])).
% 6.91/2.51  tff(c_84, plain, (![A_51, B_52, B_2, B_53]: (r2_hidden('#skF_1'(A_51, B_52), B_2) | ~r1_tarski(B_53, B_2) | ~r1_tarski(A_51, B_53) | r1_tarski(A_51, B_52))), inference(resolution, [status(thm)], [c_77, c_2])).
% 6.91/2.51  tff(c_2565, plain, (![A_321, B_322]: (r2_hidden('#skF_1'(A_321, B_322), k9_relat_1('#skF_4', '#skF_2')) | ~r1_tarski(A_321, k9_relat_1('#skF_4', k3_xboole_0('#skF_2', '#skF_3'))) | r1_tarski(A_321, B_322))), inference(resolution, [status(thm)], [c_2510, c_84])).
% 6.91/2.51  tff(c_2573, plain, (![A_321]: (~r1_tarski(A_321, k9_relat_1('#skF_4', k3_xboole_0('#skF_2', '#skF_3'))) | r1_tarski(A_321, k9_relat_1('#skF_4', '#skF_2')))), inference(resolution, [status(thm)], [c_2565, c_4])).
% 6.91/2.51  tff(c_2626, plain, (![A_333]: (r1_tarski(k2_relat_1(A_333), k9_relat_1('#skF_4', '#skF_2')) | ~r1_tarski(A_333, k7_relat_1('#skF_4', k3_xboole_0('#skF_2', '#skF_3'))) | ~v1_relat_1(k7_relat_1('#skF_4', k3_xboole_0('#skF_2', '#skF_3'))) | ~v1_relat_1(A_333) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_2622, c_2573])).
% 6.91/2.51  tff(c_2637, plain, (![A_333]: (r1_tarski(k2_relat_1(A_333), k9_relat_1('#skF_4', '#skF_2')) | ~r1_tarski(A_333, k7_relat_1('#skF_4', k3_xboole_0('#skF_2', '#skF_3'))) | ~v1_relat_1(k7_relat_1('#skF_4', k3_xboole_0('#skF_2', '#skF_3'))) | ~v1_relat_1(A_333))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2626])).
% 6.91/2.51  tff(c_3164, plain, (~v1_relat_1(k7_relat_1('#skF_4', k3_xboole_0('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_2637])).
% 6.91/2.51  tff(c_3167, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_3164])).
% 6.91/2.51  tff(c_3171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_3167])).
% 6.91/2.51  tff(c_3173, plain, (v1_relat_1(k7_relat_1('#skF_4', k3_xboole_0('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_2637])).
% 6.91/2.51  tff(c_4434, plain, (![B_529, A_530, B_531, A_532]: (r1_tarski(k9_relat_1(B_529, A_530), k9_relat_1(B_531, A_532)) | ~r1_tarski(k7_relat_1(B_529, A_530), k7_relat_1(B_531, A_532)) | ~v1_relat_1(k7_relat_1(B_531, A_532)) | ~v1_relat_1(k7_relat_1(B_529, A_530)) | ~v1_relat_1(B_531) | ~v1_relat_1(B_529))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2622])).
% 6.91/2.51  tff(c_2509, plain, (~r1_tarski(k9_relat_1('#skF_4', k3_xboole_0('#skF_2', '#skF_3')), k9_relat_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_76])).
% 6.91/2.51  tff(c_4458, plain, (~r1_tarski(k7_relat_1('#skF_4', k3_xboole_0('#skF_2', '#skF_3')), k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_4', k3_xboole_0('#skF_2', '#skF_3'))) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4434, c_2509])).
% 6.91/2.51  tff(c_4497, plain, (~r1_tarski(k7_relat_1('#skF_4', k3_xboole_0('#skF_2', '#skF_3')), k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3173, c_4458])).
% 6.91/2.51  tff(c_4499, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_4497])).
% 6.91/2.51  tff(c_4502, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_4499])).
% 6.91/2.51  tff(c_4506, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_4502])).
% 6.91/2.51  tff(c_4508, plain, (v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_4497])).
% 6.91/2.51  tff(c_8, plain, (![A_6, B_7, C_8]: (r1_tarski(A_6, k3_xboole_0(B_7, C_8)) | ~r1_tarski(A_6, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.91/2.51  tff(c_2738, plain, (![A_361, C_357, B_358, B_359, A_360]: (r2_hidden('#skF_1'(A_360, B_358), k3_xboole_0(B_359, C_357)) | ~r1_tarski(A_360, A_361) | r1_tarski(A_360, B_358) | ~r1_tarski(A_361, C_357) | ~r1_tarski(A_361, B_359))), inference(resolution, [status(thm)], [c_8, c_118])).
% 6.91/2.51  tff(c_2903, plain, (![B_379, B_380, C_381]: (r2_hidden('#skF_1'(k9_relat_1('#skF_4', k3_xboole_0('#skF_2', '#skF_3')), B_379), k3_xboole_0(B_380, C_381)) | r1_tarski(k9_relat_1('#skF_4', k3_xboole_0('#skF_2', '#skF_3')), B_379) | ~r1_tarski(k9_relat_1('#skF_4', '#skF_2'), C_381) | ~r1_tarski(k9_relat_1('#skF_4', '#skF_2'), B_380))), inference(resolution, [status(thm)], [c_2510, c_2738])).
% 6.91/2.51  tff(c_2933, plain, (![B_385, C_386]: (r1_tarski(k9_relat_1('#skF_4', k3_xboole_0('#skF_2', '#skF_3')), k3_xboole_0(B_385, C_386)) | ~r1_tarski(k9_relat_1('#skF_4', '#skF_2'), C_386) | ~r1_tarski(k9_relat_1('#skF_4', '#skF_2'), B_385))), inference(resolution, [status(thm)], [c_2903, c_4])).
% 6.91/2.51  tff(c_2940, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_2'), k9_relat_1('#skF_4', '#skF_3')) | ~r1_tarski(k9_relat_1('#skF_4', '#skF_2'), k9_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_2933, c_28])).
% 6.91/2.51  tff(c_2945, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_2'), k9_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_2940])).
% 6.91/2.51  tff(c_4446, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_2'), k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4434, c_2945])).
% 6.91/2.51  tff(c_4487, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_2'), k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_4446])).
% 6.91/2.51  tff(c_4510, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_2'), k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4508, c_4487])).
% 6.91/2.51  tff(c_4511, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(splitLeft, [status(thm)], [c_4510])).
% 6.91/2.51  tff(c_4514, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_4511])).
% 6.91/2.51  tff(c_4518, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_4514])).
% 6.91/2.51  tff(c_4520, plain, (v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(splitRight, [status(thm)], [c_4510])).
% 6.91/2.51  tff(c_16, plain, (![C_17, A_15, B_16]: (k7_relat_1(k7_relat_1(C_17, A_15), B_16)=k7_relat_1(C_17, k3_xboole_0(A_15, B_16)) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.91/2.51  tff(c_2514, plain, (![C_311, A_312, D_313, B_314]: (r1_tarski(k7_relat_1(C_311, A_312), k7_relat_1(D_313, B_314)) | ~r1_tarski(A_312, B_314) | ~r1_tarski(C_311, D_313) | ~v1_relat_1(D_313) | ~v1_relat_1(C_311))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.91/2.51  tff(c_2521, plain, (![B_16, A_15, D_313, B_314, C_17]: (r1_tarski(k7_relat_1(C_17, k3_xboole_0(A_15, B_16)), k7_relat_1(D_313, B_314)) | ~r1_tarski(B_16, B_314) | ~r1_tarski(k7_relat_1(C_17, A_15), D_313) | ~v1_relat_1(D_313) | ~v1_relat_1(k7_relat_1(C_17, A_15)) | ~v1_relat_1(C_17))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2514])).
% 6.91/2.51  tff(c_4507, plain, (~r1_tarski(k7_relat_1('#skF_4', k3_xboole_0('#skF_2', '#skF_3')), k7_relat_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_4497])).
% 6.91/2.51  tff(c_4535, plain, (~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski(k7_relat_1('#skF_4', '#skF_2'), '#skF_4') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2521, c_4507])).
% 6.91/2.51  tff(c_4547, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_4520, c_57, c_4535])).
% 6.91/2.51  tff(c_4559, plain, (~r1_tarski('#skF_4', '#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2597, c_4547])).
% 6.91/2.51  tff(c_4566, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_57, c_4559])).
% 6.91/2.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.91/2.51  
% 6.91/2.51  Inference rules
% 6.91/2.51  ----------------------
% 6.91/2.51  #Ref     : 0
% 6.91/2.51  #Sup     : 1298
% 6.91/2.51  #Fact    : 0
% 6.91/2.51  #Define  : 0
% 6.91/2.51  #Split   : 7
% 6.91/2.51  #Chain   : 0
% 6.91/2.51  #Close   : 0
% 6.91/2.51  
% 6.91/2.51  Ordering : KBO
% 6.91/2.51  
% 6.91/2.51  Simplification rules
% 6.91/2.51  ----------------------
% 6.91/2.51  #Subsume      : 152
% 6.91/2.51  #Demod        : 68
% 6.91/2.51  #Tautology    : 38
% 6.91/2.51  #SimpNegUnit  : 0
% 6.91/2.51  #BackRed      : 0
% 6.91/2.51  
% 6.91/2.51  #Partial instantiations: 0
% 6.91/2.51  #Strategies tried      : 1
% 6.91/2.51  
% 6.91/2.51  Timing (in seconds)
% 6.91/2.51  ----------------------
% 6.91/2.51  Preprocessing        : 0.30
% 6.91/2.51  Parsing              : 0.16
% 6.91/2.51  CNF conversion       : 0.02
% 6.91/2.51  Main loop            : 1.43
% 6.91/2.51  Inferencing          : 0.44
% 6.91/2.51  Reduction            : 0.30
% 6.91/2.51  Demodulation         : 0.19
% 6.91/2.51  BG Simplification    : 0.06
% 6.91/2.51  Subsumption          : 0.54
% 6.91/2.51  Abstraction          : 0.06
% 6.91/2.51  MUC search           : 0.00
% 6.91/2.51  Cooper               : 0.00
% 6.91/2.51  Total                : 1.77
% 6.91/2.51  Index Insertion      : 0.00
% 6.91/2.51  Index Deletion       : 0.00
% 6.91/2.51  Index Matching       : 0.00
% 6.91/2.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
