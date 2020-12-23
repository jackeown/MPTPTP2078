%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:28 EST 2020

% Result     : Theorem 13.39s
% Output     : CNFRefutation 13.39s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 250 expanded)
%              Number of leaves         :   46 ( 106 expanded)
%              Depth                    :   20
%              Number of atoms          :  185 ( 442 expanded)
%              Number of equality atoms :   30 (  84 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_10 > #skF_2 > #skF_9 > #skF_3 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_152,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_142,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_124,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_66,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_120,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_84,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_86,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_58,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(f_52,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_101,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_131,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k1_relat_1(A),k1_relat_1(B)),k1_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_92,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_90,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_88,plain,(
    r1_tarski('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_82,plain,(
    ! [A_76,B_78] :
      ( r1_tarski(k2_relat_1(A_76),k2_relat_1(B_78))
      | ~ r1_tarski(A_76,B_78)
      | ~ v1_relat_1(B_78)
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_518,plain,(
    ! [A_141] :
      ( k2_xboole_0(k1_relat_1(A_141),k2_relat_1(A_141)) = k3_relat_1(A_141)
      | ~ v1_relat_1(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_34,plain,(
    ! [A_16,C_18,B_17] :
      ( r1_tarski(A_16,k2_xboole_0(C_18,B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_530,plain,(
    ! [A_16,A_141] :
      ( r1_tarski(A_16,k3_relat_1(A_141))
      | ~ r1_tarski(A_16,k2_relat_1(A_141))
      | ~ v1_relat_1(A_141) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_518,c_34])).

tff(c_78,plain,(
    ! [A_72] :
      ( k2_xboole_0(k1_relat_1(A_72),k2_relat_1(A_72)) = k3_relat_1(A_72)
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_40,plain,(
    ! [A_23] : r1_tarski(k1_xboole_0,A_23) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24573,plain,(
    ! [C_697,A_698] :
      ( r2_hidden(k4_tarski(C_697,'#skF_8'(A_698,k1_relat_1(A_698),C_697)),A_698)
      | ~ r2_hidden(C_697,k1_relat_1(A_698)) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_3113,plain,(
    ! [C_266,A_267] :
      ( r2_hidden(k4_tarski(C_266,'#skF_8'(A_267,k1_relat_1(A_267),C_266)),A_267)
      | ~ r2_hidden(C_266,k1_relat_1(A_267)) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_50,plain,(
    ! [B_36,A_35] : k2_tarski(B_36,A_35) = k2_tarski(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_150,plain,(
    ! [A_91,B_92] : k3_tarski(k2_tarski(A_91,B_92)) = k2_xboole_0(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_171,plain,(
    ! [B_97,A_98] : k3_tarski(k2_tarski(B_97,A_98)) = k2_xboole_0(A_98,B_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_150])).

tff(c_52,plain,(
    ! [A_37,B_38] : k3_tarski(k2_tarski(A_37,B_38)) = k2_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_198,plain,(
    ! [B_101,A_102] : k2_xboole_0(B_101,A_102) = k2_xboole_0(A_102,B_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_52])).

tff(c_36,plain,(
    ! [A_19] : k2_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_214,plain,(
    ! [A_102] : k2_xboole_0(k1_xboole_0,A_102) = A_102 ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_36])).

tff(c_14,plain,(
    ! [D_13,A_8,B_9] :
      ( ~ r2_hidden(D_13,A_8)
      | r2_hidden(D_13,k2_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_331,plain,(
    ! [D_108,B_109,A_110] :
      ( ~ r2_hidden(D_108,B_109)
      | r2_hidden(D_108,k2_xboole_0(A_110,B_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_482,plain,(
    ! [A_136,B_137,D_138] :
      ( ~ r2_hidden(k2_xboole_0(A_136,B_137),D_138)
      | ~ r2_hidden(D_138,B_137) ) ),
    inference(resolution,[status(thm)],[c_331,c_2])).

tff(c_505,plain,(
    ! [A_139,D_140] :
      ( ~ r2_hidden(A_139,D_140)
      | ~ r2_hidden(D_140,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_482])).

tff(c_626,plain,(
    ! [A_156,B_157,D_158] :
      ( ~ r2_hidden(k2_xboole_0(A_156,B_157),k1_xboole_0)
      | ~ r2_hidden(D_158,A_156) ) ),
    inference(resolution,[status(thm)],[c_14,c_505])).

tff(c_630,plain,(
    ! [A_102,D_158] :
      ( ~ r2_hidden(A_102,k1_xboole_0)
      | ~ r2_hidden(D_158,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_626])).

tff(c_698,plain,(
    ! [D_158] : ~ r2_hidden(D_158,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_630])).

tff(c_3139,plain,(
    ! [C_268] : ~ r2_hidden(C_268,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_3113,c_698])).

tff(c_3155,plain,(
    ! [B_269] : r1_tarski(k1_relat_1(k1_xboole_0),B_269) ),
    inference(resolution,[status(thm)],[c_8,c_3139])).

tff(c_283,plain,(
    ! [B_104,A_105] :
      ( B_104 = A_105
      | ~ r1_tarski(B_104,A_105)
      | ~ r1_tarski(A_105,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_297,plain,(
    ! [A_23] :
      ( k1_xboole_0 = A_23
      | ~ r1_tarski(A_23,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_40,c_283])).

tff(c_3198,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3155,c_297])).

tff(c_970,plain,(
    ! [A_190,B_191,C_192] :
      ( r1_tarski(k4_xboole_0(A_190,B_191),C_192)
      | ~ r1_tarski(A_190,k2_xboole_0(B_191,C_192)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_995,plain,(
    ! [A_190,B_191] :
      ( k4_xboole_0(A_190,B_191) = k1_xboole_0
      | ~ r1_tarski(A_190,k2_xboole_0(B_191,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_970,c_297])).

tff(c_1203,plain,(
    ! [A_199,B_200] :
      ( k4_xboole_0(A_199,B_200) = k1_xboole_0
      | ~ r1_tarski(A_199,B_200) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_995])).

tff(c_1256,plain,(
    k4_xboole_0('#skF_9','#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_88,c_1203])).

tff(c_58,plain,(
    ! [A_46,B_47] : k6_subset_1(A_46,B_47) = k4_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_80,plain,(
    ! [A_73,B_75] :
      ( r1_tarski(k6_subset_1(k1_relat_1(A_73),k1_relat_1(B_75)),k1_relat_1(k6_subset_1(A_73,B_75)))
      | ~ v1_relat_1(B_75)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_3491,plain,(
    ! [A_278,B_279] :
      ( r1_tarski(k4_xboole_0(k1_relat_1(A_278),k1_relat_1(B_279)),k1_relat_1(k4_xboole_0(A_278,B_279)))
      | ~ v1_relat_1(B_279)
      | ~ v1_relat_1(A_278) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_58,c_80])).

tff(c_3536,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1('#skF_9'),k1_relat_1('#skF_10')),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_10')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_1256,c_3491])).

tff(c_3572,plain,(
    r1_tarski(k4_xboole_0(k1_relat_1('#skF_9'),k1_relat_1('#skF_10')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_3198,c_3536])).

tff(c_3613,plain,(
    k4_xboole_0(k1_relat_1('#skF_9'),k1_relat_1('#skF_10')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3572,c_297])).

tff(c_46,plain,(
    ! [A_29,B_30,C_31] :
      ( r1_tarski(A_29,k2_xboole_0(B_30,C_31))
      | ~ r1_tarski(k4_xboole_0(A_29,B_30),C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_3671,plain,(
    ! [C_31] :
      ( r1_tarski(k1_relat_1('#skF_9'),k2_xboole_0(k1_relat_1('#skF_10'),C_31))
      | ~ r1_tarski(k1_xboole_0,C_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3613,c_46])).

tff(c_3749,plain,(
    ! [C_286] : r1_tarski(k1_relat_1('#skF_9'),k2_xboole_0(k1_relat_1('#skF_10'),C_286)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3671])).

tff(c_3765,plain,
    ( r1_tarski(k1_relat_1('#skF_9'),k3_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_3749])).

tff(c_3784,plain,(
    r1_tarski(k1_relat_1('#skF_9'),k3_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_3765])).

tff(c_1332,plain,(
    ! [A_202,C_203,B_204] :
      ( r1_tarski(k2_xboole_0(A_202,C_203),B_204)
      | ~ r1_tarski(C_203,B_204)
      | ~ r1_tarski(A_202,B_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_21781,plain,(
    ! [A_587,B_588] :
      ( r1_tarski(k3_relat_1(A_587),B_588)
      | ~ r1_tarski(k2_relat_1(A_587),B_588)
      | ~ r1_tarski(k1_relat_1(A_587),B_588)
      | ~ v1_relat_1(A_587) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_1332])).

tff(c_86,plain,(
    ~ r1_tarski(k3_relat_1('#skF_9'),k3_relat_1('#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_21885,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_9'),k3_relat_1('#skF_10'))
    | ~ r1_tarski(k1_relat_1('#skF_9'),k3_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_21781,c_86])).

tff(c_21931,plain,(
    ~ r1_tarski(k2_relat_1('#skF_9'),k3_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_3784,c_21885])).

tff(c_21939,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_9'),k2_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_530,c_21931])).

tff(c_21943,plain,(
    ~ r1_tarski(k2_relat_1('#skF_9'),k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_21939])).

tff(c_21946,plain,
    ( ~ r1_tarski('#skF_9','#skF_10')
    | ~ v1_relat_1('#skF_10')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_82,c_21943])).

tff(c_21950,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_21946])).

tff(c_21951,plain,(
    ! [A_102] : ~ r2_hidden(A_102,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_630])).

tff(c_24599,plain,(
    ! [C_699] : ~ r2_hidden(C_699,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_24573,c_21951])).

tff(c_24615,plain,(
    ! [B_700] : r1_tarski(k1_relat_1(k1_xboole_0),B_700) ),
    inference(resolution,[status(thm)],[c_8,c_24599])).

tff(c_24663,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24615,c_297])).

tff(c_22073,plain,(
    ! [A_604,B_605,C_606] :
      ( r1_tarski(k4_xboole_0(A_604,B_605),C_606)
      | ~ r1_tarski(A_604,k2_xboole_0(B_605,C_606)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_22095,plain,(
    ! [A_604,B_605] :
      ( k4_xboole_0(A_604,B_605) = k1_xboole_0
      | ~ r1_tarski(A_604,k2_xboole_0(B_605,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_22073,c_297])).

tff(c_22113,plain,(
    ! [A_607,B_608] :
      ( k4_xboole_0(A_607,B_608) = k1_xboole_0
      | ~ r1_tarski(A_607,B_608) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_22095])).

tff(c_22150,plain,(
    k4_xboole_0('#skF_9','#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_88,c_22113])).

tff(c_24914,plain,(
    ! [A_706,B_707] :
      ( r1_tarski(k4_xboole_0(k1_relat_1(A_706),k1_relat_1(B_707)),k1_relat_1(k4_xboole_0(A_706,B_707)))
      | ~ v1_relat_1(B_707)
      | ~ v1_relat_1(A_706) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_58,c_80])).

tff(c_24962,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1('#skF_9'),k1_relat_1('#skF_10')),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_10')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_22150,c_24914])).

tff(c_24997,plain,(
    r1_tarski(k4_xboole_0(k1_relat_1('#skF_9'),k1_relat_1('#skF_10')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_24663,c_24962])).

tff(c_25100,plain,(
    k4_xboole_0(k1_relat_1('#skF_9'),k1_relat_1('#skF_10')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24997,c_297])).

tff(c_25147,plain,(
    ! [C_31] :
      ( r1_tarski(k1_relat_1('#skF_9'),k2_xboole_0(k1_relat_1('#skF_10'),C_31))
      | ~ r1_tarski(k1_xboole_0,C_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25100,c_46])).

tff(c_25561,plain,(
    ! [C_726] : r1_tarski(k1_relat_1('#skF_9'),k2_xboole_0(k1_relat_1('#skF_10'),C_726)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_25147])).

tff(c_25577,plain,
    ( r1_tarski(k1_relat_1('#skF_9'),k3_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_25561])).

tff(c_25596,plain,(
    r1_tarski(k1_relat_1('#skF_9'),k3_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_25577])).

tff(c_23527,plain,(
    ! [A_657,C_658,B_659] :
      ( r1_tarski(k2_xboole_0(A_657,C_658),B_659)
      | ~ r1_tarski(C_658,B_659)
      | ~ r1_tarski(A_657,B_659) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_42966,plain,(
    ! [A_1009,B_1010] :
      ( r1_tarski(k3_relat_1(A_1009),B_1010)
      | ~ r1_tarski(k2_relat_1(A_1009),B_1010)
      | ~ r1_tarski(k1_relat_1(A_1009),B_1010)
      | ~ v1_relat_1(A_1009) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_23527])).

tff(c_43068,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_9'),k3_relat_1('#skF_10'))
    | ~ r1_tarski(k1_relat_1('#skF_9'),k3_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_42966,c_86])).

tff(c_43113,plain,(
    ~ r1_tarski(k2_relat_1('#skF_9'),k3_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_25596,c_43068])).

tff(c_43121,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_9'),k2_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_530,c_43113])).

tff(c_43125,plain,(
    ~ r1_tarski(k2_relat_1('#skF_9'),k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_43121])).

tff(c_43128,plain,
    ( ~ r1_tarski('#skF_9','#skF_10')
    | ~ v1_relat_1('#skF_10')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_82,c_43125])).

tff(c_43132,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_43128])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:31:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.39/6.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.39/6.05  
% 13.39/6.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.39/6.05  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_10 > #skF_2 > #skF_9 > #skF_3 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_4
% 13.39/6.05  
% 13.39/6.05  %Foreground sorts:
% 13.39/6.05  
% 13.39/6.05  
% 13.39/6.05  %Background operators:
% 13.39/6.05  
% 13.39/6.05  
% 13.39/6.05  %Foreground operators:
% 13.39/6.05  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 13.39/6.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.39/6.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.39/6.05  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.39/6.05  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 13.39/6.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.39/6.05  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 13.39/6.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.39/6.05  tff('#skF_10', type, '#skF_10': $i).
% 13.39/6.05  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.39/6.05  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.39/6.05  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 13.39/6.05  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 13.39/6.05  tff('#skF_9', type, '#skF_9': $i).
% 13.39/6.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.39/6.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.39/6.05  tff(k3_tarski, type, k3_tarski: $i > $i).
% 13.39/6.05  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.39/6.05  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 13.39/6.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.39/6.05  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 13.39/6.05  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.39/6.05  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 13.39/6.05  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.39/6.05  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 13.39/6.05  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.39/6.05  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 13.39/6.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.39/6.05  
% 13.39/6.07  tff(f_152, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 13.39/6.07  tff(f_142, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 13.39/6.07  tff(f_124, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 13.39/6.07  tff(f_56, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 13.39/6.07  tff(f_66, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 13.39/6.07  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 13.39/6.07  tff(f_120, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 13.39/6.07  tff(f_84, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 13.39/6.07  tff(f_86, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 13.39/6.07  tff(f_58, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 13.39/6.07  tff(f_46, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 13.39/6.07  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 13.39/6.07  tff(f_52, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.39/6.07  tff(f_72, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 13.39/6.07  tff(f_101, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 13.39/6.07  tff(f_131, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k1_relat_1(A), k1_relat_1(B)), k1_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_relat_1)).
% 13.39/6.07  tff(f_76, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 13.39/6.07  tff(f_82, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 13.39/6.07  tff(c_92, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_152])).
% 13.39/6.07  tff(c_90, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_152])).
% 13.39/6.07  tff(c_88, plain, (r1_tarski('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_152])).
% 13.39/6.07  tff(c_82, plain, (![A_76, B_78]: (r1_tarski(k2_relat_1(A_76), k2_relat_1(B_78)) | ~r1_tarski(A_76, B_78) | ~v1_relat_1(B_78) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_142])).
% 13.39/6.07  tff(c_518, plain, (![A_141]: (k2_xboole_0(k1_relat_1(A_141), k2_relat_1(A_141))=k3_relat_1(A_141) | ~v1_relat_1(A_141))), inference(cnfTransformation, [status(thm)], [f_124])).
% 13.39/6.07  tff(c_34, plain, (![A_16, C_18, B_17]: (r1_tarski(A_16, k2_xboole_0(C_18, B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_56])).
% 13.39/6.07  tff(c_530, plain, (![A_16, A_141]: (r1_tarski(A_16, k3_relat_1(A_141)) | ~r1_tarski(A_16, k2_relat_1(A_141)) | ~v1_relat_1(A_141))), inference(superposition, [status(thm), theory('equality')], [c_518, c_34])).
% 13.39/6.07  tff(c_78, plain, (![A_72]: (k2_xboole_0(k1_relat_1(A_72), k2_relat_1(A_72))=k3_relat_1(A_72) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_124])).
% 13.39/6.07  tff(c_40, plain, (![A_23]: (r1_tarski(k1_xboole_0, A_23))), inference(cnfTransformation, [status(thm)], [f_66])).
% 13.39/6.07  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.39/6.07  tff(c_24573, plain, (![C_697, A_698]: (r2_hidden(k4_tarski(C_697, '#skF_8'(A_698, k1_relat_1(A_698), C_697)), A_698) | ~r2_hidden(C_697, k1_relat_1(A_698)))), inference(cnfTransformation, [status(thm)], [f_120])).
% 13.39/6.07  tff(c_3113, plain, (![C_266, A_267]: (r2_hidden(k4_tarski(C_266, '#skF_8'(A_267, k1_relat_1(A_267), C_266)), A_267) | ~r2_hidden(C_266, k1_relat_1(A_267)))), inference(cnfTransformation, [status(thm)], [f_120])).
% 13.39/6.07  tff(c_50, plain, (![B_36, A_35]: (k2_tarski(B_36, A_35)=k2_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_84])).
% 13.39/6.07  tff(c_150, plain, (![A_91, B_92]: (k3_tarski(k2_tarski(A_91, B_92))=k2_xboole_0(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.39/6.07  tff(c_171, plain, (![B_97, A_98]: (k3_tarski(k2_tarski(B_97, A_98))=k2_xboole_0(A_98, B_97))), inference(superposition, [status(thm), theory('equality')], [c_50, c_150])).
% 13.39/6.07  tff(c_52, plain, (![A_37, B_38]: (k3_tarski(k2_tarski(A_37, B_38))=k2_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.39/6.07  tff(c_198, plain, (![B_101, A_102]: (k2_xboole_0(B_101, A_102)=k2_xboole_0(A_102, B_101))), inference(superposition, [status(thm), theory('equality')], [c_171, c_52])).
% 13.39/6.07  tff(c_36, plain, (![A_19]: (k2_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_58])).
% 13.39/6.07  tff(c_214, plain, (![A_102]: (k2_xboole_0(k1_xboole_0, A_102)=A_102)), inference(superposition, [status(thm), theory('equality')], [c_198, c_36])).
% 13.39/6.07  tff(c_14, plain, (![D_13, A_8, B_9]: (~r2_hidden(D_13, A_8) | r2_hidden(D_13, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 13.39/6.07  tff(c_331, plain, (![D_108, B_109, A_110]: (~r2_hidden(D_108, B_109) | r2_hidden(D_108, k2_xboole_0(A_110, B_109)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 13.39/6.07  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 13.39/6.07  tff(c_482, plain, (![A_136, B_137, D_138]: (~r2_hidden(k2_xboole_0(A_136, B_137), D_138) | ~r2_hidden(D_138, B_137))), inference(resolution, [status(thm)], [c_331, c_2])).
% 13.39/6.07  tff(c_505, plain, (![A_139, D_140]: (~r2_hidden(A_139, D_140) | ~r2_hidden(D_140, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36, c_482])).
% 13.39/6.07  tff(c_626, plain, (![A_156, B_157, D_158]: (~r2_hidden(k2_xboole_0(A_156, B_157), k1_xboole_0) | ~r2_hidden(D_158, A_156))), inference(resolution, [status(thm)], [c_14, c_505])).
% 13.39/6.07  tff(c_630, plain, (![A_102, D_158]: (~r2_hidden(A_102, k1_xboole_0) | ~r2_hidden(D_158, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_214, c_626])).
% 13.39/6.07  tff(c_698, plain, (![D_158]: (~r2_hidden(D_158, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_630])).
% 13.39/6.07  tff(c_3139, plain, (![C_268]: (~r2_hidden(C_268, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_3113, c_698])).
% 13.39/6.07  tff(c_3155, plain, (![B_269]: (r1_tarski(k1_relat_1(k1_xboole_0), B_269))), inference(resolution, [status(thm)], [c_8, c_3139])).
% 13.39/6.07  tff(c_283, plain, (![B_104, A_105]: (B_104=A_105 | ~r1_tarski(B_104, A_105) | ~r1_tarski(A_105, B_104))), inference(cnfTransformation, [status(thm)], [f_52])).
% 13.39/6.07  tff(c_297, plain, (![A_23]: (k1_xboole_0=A_23 | ~r1_tarski(A_23, k1_xboole_0))), inference(resolution, [status(thm)], [c_40, c_283])).
% 13.39/6.07  tff(c_3198, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_3155, c_297])).
% 13.39/6.07  tff(c_970, plain, (![A_190, B_191, C_192]: (r1_tarski(k4_xboole_0(A_190, B_191), C_192) | ~r1_tarski(A_190, k2_xboole_0(B_191, C_192)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 13.39/6.07  tff(c_995, plain, (![A_190, B_191]: (k4_xboole_0(A_190, B_191)=k1_xboole_0 | ~r1_tarski(A_190, k2_xboole_0(B_191, k1_xboole_0)))), inference(resolution, [status(thm)], [c_970, c_297])).
% 13.39/6.07  tff(c_1203, plain, (![A_199, B_200]: (k4_xboole_0(A_199, B_200)=k1_xboole_0 | ~r1_tarski(A_199, B_200))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_995])).
% 13.39/6.07  tff(c_1256, plain, (k4_xboole_0('#skF_9', '#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_88, c_1203])).
% 13.39/6.07  tff(c_58, plain, (![A_46, B_47]: (k6_subset_1(A_46, B_47)=k4_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_101])).
% 13.39/6.07  tff(c_80, plain, (![A_73, B_75]: (r1_tarski(k6_subset_1(k1_relat_1(A_73), k1_relat_1(B_75)), k1_relat_1(k6_subset_1(A_73, B_75))) | ~v1_relat_1(B_75) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_131])).
% 13.39/6.07  tff(c_3491, plain, (![A_278, B_279]: (r1_tarski(k4_xboole_0(k1_relat_1(A_278), k1_relat_1(B_279)), k1_relat_1(k4_xboole_0(A_278, B_279))) | ~v1_relat_1(B_279) | ~v1_relat_1(A_278))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_58, c_80])).
% 13.39/6.07  tff(c_3536, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_9'), k1_relat_1('#skF_10')), k1_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_10') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_1256, c_3491])).
% 13.39/6.07  tff(c_3572, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_9'), k1_relat_1('#skF_10')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_3198, c_3536])).
% 13.39/6.07  tff(c_3613, plain, (k4_xboole_0(k1_relat_1('#skF_9'), k1_relat_1('#skF_10'))=k1_xboole_0), inference(resolution, [status(thm)], [c_3572, c_297])).
% 13.39/6.07  tff(c_46, plain, (![A_29, B_30, C_31]: (r1_tarski(A_29, k2_xboole_0(B_30, C_31)) | ~r1_tarski(k4_xboole_0(A_29, B_30), C_31))), inference(cnfTransformation, [status(thm)], [f_76])).
% 13.39/6.07  tff(c_3671, plain, (![C_31]: (r1_tarski(k1_relat_1('#skF_9'), k2_xboole_0(k1_relat_1('#skF_10'), C_31)) | ~r1_tarski(k1_xboole_0, C_31))), inference(superposition, [status(thm), theory('equality')], [c_3613, c_46])).
% 13.39/6.07  tff(c_3749, plain, (![C_286]: (r1_tarski(k1_relat_1('#skF_9'), k2_xboole_0(k1_relat_1('#skF_10'), C_286)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_3671])).
% 13.39/6.07  tff(c_3765, plain, (r1_tarski(k1_relat_1('#skF_9'), k3_relat_1('#skF_10')) | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_78, c_3749])).
% 13.39/6.07  tff(c_3784, plain, (r1_tarski(k1_relat_1('#skF_9'), k3_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_3765])).
% 13.39/6.07  tff(c_1332, plain, (![A_202, C_203, B_204]: (r1_tarski(k2_xboole_0(A_202, C_203), B_204) | ~r1_tarski(C_203, B_204) | ~r1_tarski(A_202, B_204))), inference(cnfTransformation, [status(thm)], [f_82])).
% 13.39/6.07  tff(c_21781, plain, (![A_587, B_588]: (r1_tarski(k3_relat_1(A_587), B_588) | ~r1_tarski(k2_relat_1(A_587), B_588) | ~r1_tarski(k1_relat_1(A_587), B_588) | ~v1_relat_1(A_587))), inference(superposition, [status(thm), theory('equality')], [c_78, c_1332])).
% 13.39/6.07  tff(c_86, plain, (~r1_tarski(k3_relat_1('#skF_9'), k3_relat_1('#skF_10'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 13.39/6.07  tff(c_21885, plain, (~r1_tarski(k2_relat_1('#skF_9'), k3_relat_1('#skF_10')) | ~r1_tarski(k1_relat_1('#skF_9'), k3_relat_1('#skF_10')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_21781, c_86])).
% 13.39/6.07  tff(c_21931, plain, (~r1_tarski(k2_relat_1('#skF_9'), k3_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_3784, c_21885])).
% 13.39/6.07  tff(c_21939, plain, (~r1_tarski(k2_relat_1('#skF_9'), k2_relat_1('#skF_10')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_530, c_21931])).
% 13.39/6.07  tff(c_21943, plain, (~r1_tarski(k2_relat_1('#skF_9'), k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_21939])).
% 13.39/6.07  tff(c_21946, plain, (~r1_tarski('#skF_9', '#skF_10') | ~v1_relat_1('#skF_10') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_82, c_21943])).
% 13.39/6.07  tff(c_21950, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_21946])).
% 13.39/6.07  tff(c_21951, plain, (![A_102]: (~r2_hidden(A_102, k1_xboole_0))), inference(splitRight, [status(thm)], [c_630])).
% 13.39/6.07  tff(c_24599, plain, (![C_699]: (~r2_hidden(C_699, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_24573, c_21951])).
% 13.39/6.07  tff(c_24615, plain, (![B_700]: (r1_tarski(k1_relat_1(k1_xboole_0), B_700))), inference(resolution, [status(thm)], [c_8, c_24599])).
% 13.39/6.07  tff(c_24663, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_24615, c_297])).
% 13.39/6.07  tff(c_22073, plain, (![A_604, B_605, C_606]: (r1_tarski(k4_xboole_0(A_604, B_605), C_606) | ~r1_tarski(A_604, k2_xboole_0(B_605, C_606)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 13.39/6.07  tff(c_22095, plain, (![A_604, B_605]: (k4_xboole_0(A_604, B_605)=k1_xboole_0 | ~r1_tarski(A_604, k2_xboole_0(B_605, k1_xboole_0)))), inference(resolution, [status(thm)], [c_22073, c_297])).
% 13.39/6.07  tff(c_22113, plain, (![A_607, B_608]: (k4_xboole_0(A_607, B_608)=k1_xboole_0 | ~r1_tarski(A_607, B_608))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_22095])).
% 13.39/6.07  tff(c_22150, plain, (k4_xboole_0('#skF_9', '#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_88, c_22113])).
% 13.39/6.07  tff(c_24914, plain, (![A_706, B_707]: (r1_tarski(k4_xboole_0(k1_relat_1(A_706), k1_relat_1(B_707)), k1_relat_1(k4_xboole_0(A_706, B_707))) | ~v1_relat_1(B_707) | ~v1_relat_1(A_706))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_58, c_80])).
% 13.39/6.07  tff(c_24962, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_9'), k1_relat_1('#skF_10')), k1_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_10') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_22150, c_24914])).
% 13.39/6.07  tff(c_24997, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_9'), k1_relat_1('#skF_10')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_24663, c_24962])).
% 13.39/6.07  tff(c_25100, plain, (k4_xboole_0(k1_relat_1('#skF_9'), k1_relat_1('#skF_10'))=k1_xboole_0), inference(resolution, [status(thm)], [c_24997, c_297])).
% 13.39/6.07  tff(c_25147, plain, (![C_31]: (r1_tarski(k1_relat_1('#skF_9'), k2_xboole_0(k1_relat_1('#skF_10'), C_31)) | ~r1_tarski(k1_xboole_0, C_31))), inference(superposition, [status(thm), theory('equality')], [c_25100, c_46])).
% 13.39/6.07  tff(c_25561, plain, (![C_726]: (r1_tarski(k1_relat_1('#skF_9'), k2_xboole_0(k1_relat_1('#skF_10'), C_726)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_25147])).
% 13.39/6.07  tff(c_25577, plain, (r1_tarski(k1_relat_1('#skF_9'), k3_relat_1('#skF_10')) | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_78, c_25561])).
% 13.39/6.07  tff(c_25596, plain, (r1_tarski(k1_relat_1('#skF_9'), k3_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_25577])).
% 13.39/6.07  tff(c_23527, plain, (![A_657, C_658, B_659]: (r1_tarski(k2_xboole_0(A_657, C_658), B_659) | ~r1_tarski(C_658, B_659) | ~r1_tarski(A_657, B_659))), inference(cnfTransformation, [status(thm)], [f_82])).
% 13.39/6.07  tff(c_42966, plain, (![A_1009, B_1010]: (r1_tarski(k3_relat_1(A_1009), B_1010) | ~r1_tarski(k2_relat_1(A_1009), B_1010) | ~r1_tarski(k1_relat_1(A_1009), B_1010) | ~v1_relat_1(A_1009))), inference(superposition, [status(thm), theory('equality')], [c_78, c_23527])).
% 13.39/6.07  tff(c_43068, plain, (~r1_tarski(k2_relat_1('#skF_9'), k3_relat_1('#skF_10')) | ~r1_tarski(k1_relat_1('#skF_9'), k3_relat_1('#skF_10')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_42966, c_86])).
% 13.39/6.07  tff(c_43113, plain, (~r1_tarski(k2_relat_1('#skF_9'), k3_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_25596, c_43068])).
% 13.39/6.07  tff(c_43121, plain, (~r1_tarski(k2_relat_1('#skF_9'), k2_relat_1('#skF_10')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_530, c_43113])).
% 13.39/6.07  tff(c_43125, plain, (~r1_tarski(k2_relat_1('#skF_9'), k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_43121])).
% 13.39/6.07  tff(c_43128, plain, (~r1_tarski('#skF_9', '#skF_10') | ~v1_relat_1('#skF_10') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_82, c_43125])).
% 13.39/6.07  tff(c_43132, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_43128])).
% 13.39/6.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.39/6.07  
% 13.39/6.07  Inference rules
% 13.39/6.07  ----------------------
% 13.39/6.07  #Ref     : 0
% 13.39/6.07  #Sup     : 10721
% 13.39/6.07  #Fact    : 12
% 13.39/6.07  #Define  : 0
% 13.39/6.07  #Split   : 25
% 13.39/6.07  #Chain   : 0
% 13.39/6.07  #Close   : 0
% 13.39/6.07  
% 13.39/6.07  Ordering : KBO
% 13.39/6.07  
% 13.39/6.07  Simplification rules
% 13.39/6.07  ----------------------
% 13.39/6.07  #Subsume      : 2002
% 13.39/6.07  #Demod        : 8456
% 13.39/6.07  #Tautology    : 6017
% 13.39/6.07  #SimpNegUnit  : 22
% 13.39/6.07  #BackRed      : 16
% 13.39/6.07  
% 13.39/6.07  #Partial instantiations: 0
% 13.39/6.07  #Strategies tried      : 1
% 13.39/6.07  
% 13.39/6.07  Timing (in seconds)
% 13.39/6.07  ----------------------
% 13.61/6.07  Preprocessing        : 0.51
% 13.61/6.07  Parsing              : 0.26
% 13.61/6.07  CNF conversion       : 0.04
% 13.61/6.07  Main loop            : 4.77
% 13.61/6.07  Inferencing          : 0.97
% 13.61/6.07  Reduction            : 2.18
% 13.61/6.07  Demodulation         : 1.79
% 13.61/6.07  BG Simplification    : 0.10
% 13.61/6.07  Subsumption          : 1.26
% 13.61/6.07  Abstraction          : 0.14
% 13.61/6.07  MUC search           : 0.00
% 13.61/6.07  Cooper               : 0.00
% 13.61/6.07  Total                : 5.33
% 13.61/6.07  Index Insertion      : 0.00
% 13.61/6.07  Index Deletion       : 0.00
% 13.61/6.07  Index Matching       : 0.00
% 13.61/6.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
