%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:32 EST 2020

% Result     : Theorem 4.90s
% Output     : CNFRefutation 5.19s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 650 expanded)
%              Number of leaves         :   37 ( 230 expanded)
%              Depth                    :   17
%              Number of atoms          :  199 (1347 expanded)
%              Number of equality atoms :   45 ( 128 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_52,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_110,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( ~ v1_xboole_0(k3_xboole_0(A,B))
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_81,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_75,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_subset_1(B,A)
           => ~ v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_subset_1)).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_52,plain,(
    m1_subset_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_292,plain,(
    ! [A_88,B_89] :
      ( k6_domain_1(A_88,B_89) = k1_tarski(B_89)
      | ~ m1_subset_1(B_89,A_88)
      | v1_xboole_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_301,plain,
    ( k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_292])).

tff(c_306,plain,(
    k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_301])).

tff(c_854,plain,(
    ! [A_117,B_118] :
      ( m1_subset_1(k6_domain_1(A_117,B_118),k1_zfmisc_1(A_117))
      | ~ m1_subset_1(B_118,A_117)
      | v1_xboole_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_866,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_854])).

tff(c_871,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_866])).

tff(c_872,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_871])).

tff(c_38,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,B_29)
      | ~ m1_subset_1(A_28,k1_zfmisc_1(B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_887,plain,(
    r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_872,c_38])).

tff(c_22,plain,(
    ! [A_15] : k2_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_77,plain,(
    ! [A_43,B_44] : k2_xboole_0(k1_tarski(A_43),B_44) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_81,plain,(
    ! [A_43] : k1_tarski(A_43) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_77])).

tff(c_48,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_24,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_902,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),'#skF_4') = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_887,c_24])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2262,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_5')) = k1_tarski('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_902,c_2])).

tff(c_46,plain,(
    ! [A_34,B_36] :
      ( r1_tarski(A_34,B_36)
      | v1_xboole_0(k3_xboole_0(A_34,B_36))
      | ~ v1_zfmisc_1(A_34)
      | v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2279,plain,
    ( r1_tarski('#skF_4',k1_tarski('#skF_5'))
    | v1_xboole_0(k1_tarski('#skF_5'))
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2262,c_46])).

tff(c_2283,plain,
    ( r1_tarski('#skF_4',k1_tarski('#skF_5'))
    | v1_xboole_0(k1_tarski('#skF_5'))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2279])).

tff(c_2284,plain,
    ( r1_tarski('#skF_4',k1_tarski('#skF_5'))
    | v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2283])).

tff(c_2287,plain,(
    v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2284])).

tff(c_14,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2302,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2287,c_14])).

tff(c_2311,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_2302])).

tff(c_2312,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2284])).

tff(c_16,plain,(
    ! [B_14,A_13] :
      ( B_14 = A_13
      | ~ r1_tarski(B_14,A_13)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2321,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_2312,c_16])).

tff(c_2330,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_887,c_2321])).

tff(c_50,plain,(
    v1_subset_1(k6_domain_1('#skF_4','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_307,plain,(
    v1_subset_1(k1_tarski('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_50])).

tff(c_2338,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2330,c_307])).

tff(c_36,plain,(
    ! [A_26] : m1_subset_1('#skF_3'(A_26),k1_zfmisc_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_137,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(A_55,B_56)
      | ~ m1_subset_1(A_55,k1_zfmisc_1(B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_141,plain,(
    ! [A_26] : r1_tarski('#skF_3'(A_26),A_26) ),
    inference(resolution,[status(thm)],[c_36,c_137])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_249,plain,(
    ! [C_80,B_81,A_82] :
      ( r2_hidden(C_80,B_81)
      | ~ r2_hidden(C_80,A_82)
      | ~ r1_tarski(A_82,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_256,plain,(
    ! [A_83,B_84] :
      ( r2_hidden('#skF_1'(A_83),B_84)
      | ~ r1_tarski(A_83,B_84)
      | v1_xboole_0(A_83) ) ),
    inference(resolution,[status(thm)],[c_6,c_249])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_264,plain,(
    ! [B_85,A_86] :
      ( ~ v1_xboole_0(B_85)
      | ~ r1_tarski(A_86,B_85)
      | v1_xboole_0(A_86) ) ),
    inference(resolution,[status(thm)],[c_256,c_4])).

tff(c_275,plain,(
    ! [A_26] :
      ( ~ v1_xboole_0(A_26)
      | v1_xboole_0('#skF_3'(A_26)) ) ),
    inference(resolution,[status(thm)],[c_141,c_264])).

tff(c_277,plain,(
    ! [A_87] :
      ( ~ v1_xboole_0(A_87)
      | v1_xboole_0('#skF_3'(A_87)) ) ),
    inference(resolution,[status(thm)],[c_141,c_264])).

tff(c_312,plain,(
    ! [A_90] :
      ( '#skF_3'(A_90) = k1_xboole_0
      | ~ v1_xboole_0(A_90) ) ),
    inference(resolution,[status(thm)],[c_277,c_14])).

tff(c_317,plain,(
    ! [A_91] :
      ( '#skF_3'('#skF_3'(A_91)) = k1_xboole_0
      | ~ v1_xboole_0(A_91) ) ),
    inference(resolution,[status(thm)],[c_275,c_312])).

tff(c_326,plain,(
    ! [A_91] :
      ( ~ v1_xboole_0('#skF_3'(A_91))
      | v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(A_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_275])).

tff(c_523,plain,(
    ! [A_103] :
      ( ~ v1_xboole_0('#skF_3'(A_103))
      | ~ v1_xboole_0(A_103) ) ),
    inference(splitLeft,[status(thm)],[c_326])).

tff(c_533,plain,(
    ! [A_26] : ~ v1_xboole_0(A_26) ),
    inference(resolution,[status(thm)],[c_275,c_523])).

tff(c_547,plain,(
    ! [A_106,B_107] :
      ( r1_tarski(A_106,B_107)
      | ~ v1_zfmisc_1(A_106) ) ),
    inference(negUnitSimplification,[status(thm)],[c_533,c_533,c_46])).

tff(c_213,plain,(
    ! [B_70,A_71] :
      ( B_70 = A_71
      | ~ r1_tarski(B_70,A_71)
      | ~ r1_tarski(A_71,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_221,plain,(
    ! [A_26] :
      ( '#skF_3'(A_26) = A_26
      | ~ r1_tarski(A_26,'#skF_3'(A_26)) ) ),
    inference(resolution,[status(thm)],[c_141,c_213])).

tff(c_560,plain,(
    ! [A_108] :
      ( '#skF_3'(A_108) = A_108
      | ~ v1_zfmisc_1(A_108) ) ),
    inference(resolution,[status(thm)],[c_547,c_221])).

tff(c_564,plain,(
    '#skF_3'('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_48,c_560])).

tff(c_34,plain,(
    ! [A_26] : ~ v1_subset_1('#skF_3'(A_26),A_26) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_583,plain,(
    ~ v1_subset_1('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_564,c_34])).

tff(c_597,plain,(
    ! [A_109,B_110] :
      ( k3_xboole_0(A_109,B_110) = A_109
      | ~ v1_zfmisc_1(A_109) ) ),
    inference(resolution,[status(thm)],[c_547,c_24])).

tff(c_601,plain,(
    ! [B_111] : k3_xboole_0('#skF_4',B_111) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_48,c_597])).

tff(c_614,plain,(
    ! [B_111] : k3_xboole_0(B_111,'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_601,c_2])).

tff(c_42,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(k6_domain_1(A_30,B_31),k1_zfmisc_1(A_30))
      | ~ m1_subset_1(B_31,A_30)
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_721,plain,(
    ! [A_115,B_116] :
      ( m1_subset_1(k6_domain_1(A_115,B_116),k1_zfmisc_1(A_115))
      | ~ m1_subset_1(B_116,A_115) ) ),
    inference(negUnitSimplification,[status(thm)],[c_533,c_42])).

tff(c_733,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_721])).

tff(c_739,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_733])).

tff(c_747,plain,(
    r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_739,c_38])).

tff(c_752,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),'#skF_4') = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_747,c_24])).

tff(c_755,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_614,c_752])).

tff(c_758,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_755,c_307])).

tff(c_763,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_583,c_758])).

tff(c_764,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_326])).

tff(c_142,plain,(
    ! [A_57] : r1_tarski('#skF_3'(A_57),A_57) ),
    inference(resolution,[status(thm)],[c_36,c_137])).

tff(c_146,plain,(
    ! [A_57] : k3_xboole_0('#skF_3'(A_57),A_57) = '#skF_3'(A_57) ),
    inference(resolution,[status(thm)],[c_142,c_24])).

tff(c_406,plain,(
    ! [A_99,B_100] :
      ( r1_tarski(A_99,B_100)
      | v1_xboole_0(k3_xboole_0(A_99,B_100))
      | ~ v1_zfmisc_1(A_99)
      | v1_xboole_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2432,plain,(
    ! [A_169,B_170] :
      ( r1_tarski(A_169,B_170)
      | v1_xboole_0(k3_xboole_0(B_170,A_169))
      | ~ v1_zfmisc_1(A_169)
      | v1_xboole_0(A_169) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_406])).

tff(c_3777,plain,(
    ! [B_222,A_223] :
      ( k3_xboole_0(B_222,A_223) = k1_xboole_0
      | r1_tarski(A_223,B_222)
      | ~ v1_zfmisc_1(A_223)
      | v1_xboole_0(A_223) ) ),
    inference(resolution,[status(thm)],[c_2432,c_14])).

tff(c_3807,plain,(
    ! [A_223] :
      ( '#skF_3'(A_223) = A_223
      | k3_xboole_0('#skF_3'(A_223),A_223) = k1_xboole_0
      | ~ v1_zfmisc_1(A_223)
      | v1_xboole_0(A_223) ) ),
    inference(resolution,[status(thm)],[c_3777,c_221])).

tff(c_3933,plain,(
    ! [A_227] :
      ( '#skF_3'(A_227) = A_227
      | '#skF_3'(A_227) = k1_xboole_0
      | ~ v1_zfmisc_1(A_227)
      | v1_xboole_0(A_227) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_3807])).

tff(c_3936,plain,
    ( '#skF_3'('#skF_4') = '#skF_4'
    | '#skF_3'('#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_3933])).

tff(c_3939,plain,
    ( '#skF_3'('#skF_4') = '#skF_4'
    | '#skF_3'('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_3936])).

tff(c_3946,plain,(
    '#skF_3'('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3939])).

tff(c_379,plain,(
    ! [B_93,A_94] :
      ( ~ v1_xboole_0(B_93)
      | v1_subset_1(B_93,A_94)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(A_94))
      | v1_xboole_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_385,plain,(
    ! [A_26] :
      ( ~ v1_xboole_0('#skF_3'(A_26))
      | v1_subset_1('#skF_3'(A_26),A_26)
      | v1_xboole_0(A_26) ) ),
    inference(resolution,[status(thm)],[c_36,c_379])).

tff(c_389,plain,(
    ! [A_26] :
      ( ~ v1_xboole_0('#skF_3'(A_26))
      | v1_xboole_0(A_26) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_385])).

tff(c_3995,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3946,c_389])).

tff(c_4038,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_764,c_3995])).

tff(c_4040,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_4038])).

tff(c_4041,plain,(
    '#skF_3'('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3939])).

tff(c_4115,plain,(
    ~ v1_subset_1('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4041,c_34])).

tff(c_4146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2338,c_4115])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:52:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.90/1.97  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.19/1.98  
% 5.19/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.19/1.98  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2
% 5.19/1.98  
% 5.19/1.98  %Foreground sorts:
% 5.19/1.98  
% 5.19/1.98  
% 5.19/1.98  %Background operators:
% 5.19/1.98  
% 5.19/1.98  
% 5.19/1.98  %Foreground operators:
% 5.19/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.19/1.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.19/1.98  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 5.19/1.98  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.19/1.98  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.19/1.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.19/1.98  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 5.19/1.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.19/1.98  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.19/1.98  tff('#skF_5', type, '#skF_5': $i).
% 5.19/1.98  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.19/1.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.19/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.19/1.98  tff('#skF_4', type, '#skF_4': $i).
% 5.19/1.98  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.19/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.19/1.98  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.19/1.98  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 5.19/1.98  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.19/1.98  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.19/1.98  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.19/1.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.19/1.98  
% 5.19/2.00  tff(f_122, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 5.19/2.00  tff(f_99, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 5.19/2.00  tff(f_92, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 5.19/2.00  tff(f_85, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.19/2.00  tff(f_52, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 5.19/2.00  tff(f_63, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 5.19/2.00  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.19/2.00  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.19/2.00  tff(f_110, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tex_2)).
% 5.19/2.00  tff(f_44, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.19/2.00  tff(f_50, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.19/2.00  tff(f_81, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 5.19/2.00  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.19/2.00  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.19/2.00  tff(f_75, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_subset_1(B, A) => ~v1_xboole_0(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_subset_1)).
% 5.19/2.00  tff(c_54, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.19/2.00  tff(c_52, plain, (m1_subset_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.19/2.00  tff(c_292, plain, (![A_88, B_89]: (k6_domain_1(A_88, B_89)=k1_tarski(B_89) | ~m1_subset_1(B_89, A_88) | v1_xboole_0(A_88))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.19/2.00  tff(c_301, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_292])).
% 5.19/2.00  tff(c_306, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_54, c_301])).
% 5.19/2.00  tff(c_854, plain, (![A_117, B_118]: (m1_subset_1(k6_domain_1(A_117, B_118), k1_zfmisc_1(A_117)) | ~m1_subset_1(B_118, A_117) | v1_xboole_0(A_117))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.19/2.00  tff(c_866, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', '#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_306, c_854])).
% 5.19/2.00  tff(c_871, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_866])).
% 5.19/2.00  tff(c_872, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_54, c_871])).
% 5.19/2.00  tff(c_38, plain, (![A_28, B_29]: (r1_tarski(A_28, B_29) | ~m1_subset_1(A_28, k1_zfmisc_1(B_29)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.19/2.00  tff(c_887, plain, (r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_872, c_38])).
% 5.19/2.00  tff(c_22, plain, (![A_15]: (k2_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.19/2.00  tff(c_77, plain, (![A_43, B_44]: (k2_xboole_0(k1_tarski(A_43), B_44)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.19/2.00  tff(c_81, plain, (![A_43]: (k1_tarski(A_43)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_77])).
% 5.19/2.00  tff(c_48, plain, (v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.19/2.00  tff(c_24, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.19/2.00  tff(c_902, plain, (k3_xboole_0(k1_tarski('#skF_5'), '#skF_4')=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_887, c_24])).
% 5.19/2.00  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.19/2.00  tff(c_2262, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_5'))=k1_tarski('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_902, c_2])).
% 5.19/2.00  tff(c_46, plain, (![A_34, B_36]: (r1_tarski(A_34, B_36) | v1_xboole_0(k3_xboole_0(A_34, B_36)) | ~v1_zfmisc_1(A_34) | v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.19/2.00  tff(c_2279, plain, (r1_tarski('#skF_4', k1_tarski('#skF_5')) | v1_xboole_0(k1_tarski('#skF_5')) | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2262, c_46])).
% 5.19/2.00  tff(c_2283, plain, (r1_tarski('#skF_4', k1_tarski('#skF_5')) | v1_xboole_0(k1_tarski('#skF_5')) | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2279])).
% 5.19/2.00  tff(c_2284, plain, (r1_tarski('#skF_4', k1_tarski('#skF_5')) | v1_xboole_0(k1_tarski('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_54, c_2283])).
% 5.19/2.00  tff(c_2287, plain, (v1_xboole_0(k1_tarski('#skF_5'))), inference(splitLeft, [status(thm)], [c_2284])).
% 5.19/2.00  tff(c_14, plain, (![A_12]: (k1_xboole_0=A_12 | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.19/2.00  tff(c_2302, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_2287, c_14])).
% 5.19/2.00  tff(c_2311, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_2302])).
% 5.19/2.00  tff(c_2312, plain, (r1_tarski('#skF_4', k1_tarski('#skF_5'))), inference(splitRight, [status(thm)], [c_2284])).
% 5.19/2.00  tff(c_16, plain, (![B_14, A_13]: (B_14=A_13 | ~r1_tarski(B_14, A_13) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.19/2.00  tff(c_2321, plain, (k1_tarski('#skF_5')='#skF_4' | ~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_2312, c_16])).
% 5.19/2.00  tff(c_2330, plain, (k1_tarski('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_887, c_2321])).
% 5.19/2.00  tff(c_50, plain, (v1_subset_1(k6_domain_1('#skF_4', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.19/2.00  tff(c_307, plain, (v1_subset_1(k1_tarski('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_306, c_50])).
% 5.19/2.00  tff(c_2338, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2330, c_307])).
% 5.19/2.00  tff(c_36, plain, (![A_26]: (m1_subset_1('#skF_3'(A_26), k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.19/2.00  tff(c_137, plain, (![A_55, B_56]: (r1_tarski(A_55, B_56) | ~m1_subset_1(A_55, k1_zfmisc_1(B_56)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.19/2.00  tff(c_141, plain, (![A_26]: (r1_tarski('#skF_3'(A_26), A_26))), inference(resolution, [status(thm)], [c_36, c_137])).
% 5.19/2.00  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.19/2.00  tff(c_249, plain, (![C_80, B_81, A_82]: (r2_hidden(C_80, B_81) | ~r2_hidden(C_80, A_82) | ~r1_tarski(A_82, B_81))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.19/2.00  tff(c_256, plain, (![A_83, B_84]: (r2_hidden('#skF_1'(A_83), B_84) | ~r1_tarski(A_83, B_84) | v1_xboole_0(A_83))), inference(resolution, [status(thm)], [c_6, c_249])).
% 5.19/2.00  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.19/2.00  tff(c_264, plain, (![B_85, A_86]: (~v1_xboole_0(B_85) | ~r1_tarski(A_86, B_85) | v1_xboole_0(A_86))), inference(resolution, [status(thm)], [c_256, c_4])).
% 5.19/2.00  tff(c_275, plain, (![A_26]: (~v1_xboole_0(A_26) | v1_xboole_0('#skF_3'(A_26)))), inference(resolution, [status(thm)], [c_141, c_264])).
% 5.19/2.00  tff(c_277, plain, (![A_87]: (~v1_xboole_0(A_87) | v1_xboole_0('#skF_3'(A_87)))), inference(resolution, [status(thm)], [c_141, c_264])).
% 5.19/2.00  tff(c_312, plain, (![A_90]: ('#skF_3'(A_90)=k1_xboole_0 | ~v1_xboole_0(A_90))), inference(resolution, [status(thm)], [c_277, c_14])).
% 5.19/2.00  tff(c_317, plain, (![A_91]: ('#skF_3'('#skF_3'(A_91))=k1_xboole_0 | ~v1_xboole_0(A_91))), inference(resolution, [status(thm)], [c_275, c_312])).
% 5.19/2.00  tff(c_326, plain, (![A_91]: (~v1_xboole_0('#skF_3'(A_91)) | v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(A_91))), inference(superposition, [status(thm), theory('equality')], [c_317, c_275])).
% 5.19/2.00  tff(c_523, plain, (![A_103]: (~v1_xboole_0('#skF_3'(A_103)) | ~v1_xboole_0(A_103))), inference(splitLeft, [status(thm)], [c_326])).
% 5.19/2.00  tff(c_533, plain, (![A_26]: (~v1_xboole_0(A_26))), inference(resolution, [status(thm)], [c_275, c_523])).
% 5.19/2.00  tff(c_547, plain, (![A_106, B_107]: (r1_tarski(A_106, B_107) | ~v1_zfmisc_1(A_106))), inference(negUnitSimplification, [status(thm)], [c_533, c_533, c_46])).
% 5.19/2.00  tff(c_213, plain, (![B_70, A_71]: (B_70=A_71 | ~r1_tarski(B_70, A_71) | ~r1_tarski(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.19/2.00  tff(c_221, plain, (![A_26]: ('#skF_3'(A_26)=A_26 | ~r1_tarski(A_26, '#skF_3'(A_26)))), inference(resolution, [status(thm)], [c_141, c_213])).
% 5.19/2.00  tff(c_560, plain, (![A_108]: ('#skF_3'(A_108)=A_108 | ~v1_zfmisc_1(A_108))), inference(resolution, [status(thm)], [c_547, c_221])).
% 5.19/2.00  tff(c_564, plain, ('#skF_3'('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_48, c_560])).
% 5.19/2.00  tff(c_34, plain, (![A_26]: (~v1_subset_1('#skF_3'(A_26), A_26))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.19/2.00  tff(c_583, plain, (~v1_subset_1('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_564, c_34])).
% 5.19/2.00  tff(c_597, plain, (![A_109, B_110]: (k3_xboole_0(A_109, B_110)=A_109 | ~v1_zfmisc_1(A_109))), inference(resolution, [status(thm)], [c_547, c_24])).
% 5.19/2.00  tff(c_601, plain, (![B_111]: (k3_xboole_0('#skF_4', B_111)='#skF_4')), inference(resolution, [status(thm)], [c_48, c_597])).
% 5.19/2.00  tff(c_614, plain, (![B_111]: (k3_xboole_0(B_111, '#skF_4')='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_601, c_2])).
% 5.19/2.00  tff(c_42, plain, (![A_30, B_31]: (m1_subset_1(k6_domain_1(A_30, B_31), k1_zfmisc_1(A_30)) | ~m1_subset_1(B_31, A_30) | v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.19/2.00  tff(c_721, plain, (![A_115, B_116]: (m1_subset_1(k6_domain_1(A_115, B_116), k1_zfmisc_1(A_115)) | ~m1_subset_1(B_116, A_115))), inference(negUnitSimplification, [status(thm)], [c_533, c_42])).
% 5.19/2.00  tff(c_733, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_306, c_721])).
% 5.19/2.00  tff(c_739, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_733])).
% 5.19/2.00  tff(c_747, plain, (r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_739, c_38])).
% 5.19/2.00  tff(c_752, plain, (k3_xboole_0(k1_tarski('#skF_5'), '#skF_4')=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_747, c_24])).
% 5.19/2.00  tff(c_755, plain, (k1_tarski('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_614, c_752])).
% 5.19/2.00  tff(c_758, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_755, c_307])).
% 5.19/2.00  tff(c_763, plain, $false, inference(negUnitSimplification, [status(thm)], [c_583, c_758])).
% 5.19/2.00  tff(c_764, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_326])).
% 5.19/2.00  tff(c_142, plain, (![A_57]: (r1_tarski('#skF_3'(A_57), A_57))), inference(resolution, [status(thm)], [c_36, c_137])).
% 5.19/2.00  tff(c_146, plain, (![A_57]: (k3_xboole_0('#skF_3'(A_57), A_57)='#skF_3'(A_57))), inference(resolution, [status(thm)], [c_142, c_24])).
% 5.19/2.00  tff(c_406, plain, (![A_99, B_100]: (r1_tarski(A_99, B_100) | v1_xboole_0(k3_xboole_0(A_99, B_100)) | ~v1_zfmisc_1(A_99) | v1_xboole_0(A_99))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.19/2.00  tff(c_2432, plain, (![A_169, B_170]: (r1_tarski(A_169, B_170) | v1_xboole_0(k3_xboole_0(B_170, A_169)) | ~v1_zfmisc_1(A_169) | v1_xboole_0(A_169))), inference(superposition, [status(thm), theory('equality')], [c_2, c_406])).
% 5.19/2.00  tff(c_3777, plain, (![B_222, A_223]: (k3_xboole_0(B_222, A_223)=k1_xboole_0 | r1_tarski(A_223, B_222) | ~v1_zfmisc_1(A_223) | v1_xboole_0(A_223))), inference(resolution, [status(thm)], [c_2432, c_14])).
% 5.19/2.00  tff(c_3807, plain, (![A_223]: ('#skF_3'(A_223)=A_223 | k3_xboole_0('#skF_3'(A_223), A_223)=k1_xboole_0 | ~v1_zfmisc_1(A_223) | v1_xboole_0(A_223))), inference(resolution, [status(thm)], [c_3777, c_221])).
% 5.19/2.00  tff(c_3933, plain, (![A_227]: ('#skF_3'(A_227)=A_227 | '#skF_3'(A_227)=k1_xboole_0 | ~v1_zfmisc_1(A_227) | v1_xboole_0(A_227))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_3807])).
% 5.19/2.00  tff(c_3936, plain, ('#skF_3'('#skF_4')='#skF_4' | '#skF_3'('#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_3933])).
% 5.19/2.00  tff(c_3939, plain, ('#skF_3'('#skF_4')='#skF_4' | '#skF_3'('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_54, c_3936])).
% 5.19/2.00  tff(c_3946, plain, ('#skF_3'('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3939])).
% 5.19/2.00  tff(c_379, plain, (![B_93, A_94]: (~v1_xboole_0(B_93) | v1_subset_1(B_93, A_94) | ~m1_subset_1(B_93, k1_zfmisc_1(A_94)) | v1_xboole_0(A_94))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.19/2.00  tff(c_385, plain, (![A_26]: (~v1_xboole_0('#skF_3'(A_26)) | v1_subset_1('#skF_3'(A_26), A_26) | v1_xboole_0(A_26))), inference(resolution, [status(thm)], [c_36, c_379])).
% 5.19/2.00  tff(c_389, plain, (![A_26]: (~v1_xboole_0('#skF_3'(A_26)) | v1_xboole_0(A_26))), inference(negUnitSimplification, [status(thm)], [c_34, c_385])).
% 5.19/2.00  tff(c_3995, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3946, c_389])).
% 5.19/2.00  tff(c_4038, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_764, c_3995])).
% 5.19/2.00  tff(c_4040, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_4038])).
% 5.19/2.00  tff(c_4041, plain, ('#skF_3'('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_3939])).
% 5.19/2.00  tff(c_4115, plain, (~v1_subset_1('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4041, c_34])).
% 5.19/2.00  tff(c_4146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2338, c_4115])).
% 5.19/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.19/2.00  
% 5.19/2.00  Inference rules
% 5.19/2.00  ----------------------
% 5.19/2.00  #Ref     : 0
% 5.19/2.00  #Sup     : 957
% 5.19/2.00  #Fact    : 0
% 5.19/2.00  #Define  : 0
% 5.19/2.00  #Split   : 11
% 5.19/2.00  #Chain   : 0
% 5.19/2.00  #Close   : 0
% 5.19/2.00  
% 5.19/2.00  Ordering : KBO
% 5.19/2.00  
% 5.19/2.00  Simplification rules
% 5.19/2.00  ----------------------
% 5.19/2.00  #Subsume      : 263
% 5.19/2.00  #Demod        : 537
% 5.19/2.00  #Tautology    : 398
% 5.19/2.00  #SimpNegUnit  : 88
% 5.19/2.00  #BackRed      : 36
% 5.19/2.00  
% 5.19/2.00  #Partial instantiations: 0
% 5.19/2.00  #Strategies tried      : 1
% 5.19/2.00  
% 5.19/2.00  Timing (in seconds)
% 5.19/2.00  ----------------------
% 5.19/2.01  Preprocessing        : 0.36
% 5.19/2.01  Parsing              : 0.19
% 5.19/2.01  CNF conversion       : 0.03
% 5.19/2.01  Main loop            : 0.81
% 5.19/2.01  Inferencing          : 0.28
% 5.19/2.01  Reduction            : 0.26
% 5.19/2.01  Demodulation         : 0.18
% 5.19/2.01  BG Simplification    : 0.03
% 5.19/2.01  Subsumption          : 0.17
% 5.19/2.01  Abstraction          : 0.04
% 5.19/2.01  MUC search           : 0.00
% 5.19/2.01  Cooper               : 0.00
% 5.19/2.01  Total                : 1.22
% 5.19/2.01  Index Insertion      : 0.00
% 5.19/2.01  Index Deletion       : 0.00
% 5.19/2.01  Index Matching       : 0.00
% 5.19/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
