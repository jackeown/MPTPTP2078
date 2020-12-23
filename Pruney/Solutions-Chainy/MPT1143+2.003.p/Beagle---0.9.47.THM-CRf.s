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
% DateTime   : Thu Dec  3 10:19:22 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 382 expanded)
%              Number of leaves         :   41 ( 138 expanded)
%              Depth                    :   17
%              Number of atoms          :  180 ( 969 expanded)
%              Number of equality atoms :   16 ( 110 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > v6_orders_2 > r7_relat_2 > r2_hidden > m1_subset_1 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(r7_relat_2,type,(
    r7_relat_2: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_138,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v6_orders_2(k6_domain_1(u1_struct_0(A),B),A)
              & m1_subset_1(k6_domain_1(u1_struct_0(A),B),k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_orders_2)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_111,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_51,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_123,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,B,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_orders_2(B,A)
          <=> r7_relat_2(u1_orders_2(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_orders_2)).

tff(f_43,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r7_relat_2(A,B)
        <=> ! [C,D] :
              ~ ( r2_hidden(C,B)
                & r2_hidden(D,B)
                & ~ r2_hidden(k4_tarski(C,D),A)
                & ~ r2_hidden(k4_tarski(D,C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_54,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_42,plain,(
    ! [A_42] :
      ( l1_struct_0(A_42)
      | ~ l1_orders_2(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_361,plain,(
    ! [A_114,B_115] :
      ( k6_domain_1(A_114,B_115) = k1_tarski(B_115)
      | ~ m1_subset_1(B_115,A_114)
      | v1_xboole_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_365,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_52,c_361])).

tff(c_372,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_365])).

tff(c_20,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(u1_struct_0(A_12))
      | ~ l1_struct_0(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_375,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_372,c_20])).

tff(c_378,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_375])).

tff(c_381,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_378])).

tff(c_385,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_381])).

tff(c_387,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_365])).

tff(c_386,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_365])).

tff(c_56,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_191,plain,(
    ! [A_88,B_89] :
      ( r1_orders_2(A_88,B_89,B_89)
      | ~ m1_subset_1(B_89,u1_struct_0(A_88))
      | ~ l1_orders_2(A_88)
      | ~ v3_orders_2(A_88)
      | v2_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_193,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_191])).

tff(c_196,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_193])).

tff(c_197,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_196])).

tff(c_331,plain,(
    ! [B_106,C_107,A_108] :
      ( r2_hidden(k4_tarski(B_106,C_107),u1_orders_2(A_108))
      | ~ r1_orders_2(A_108,B_106,C_107)
      | ~ m1_subset_1(C_107,u1_struct_0(A_108))
      | ~ m1_subset_1(B_106,u1_struct_0(A_108))
      | ~ l1_orders_2(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_92,plain,(
    ! [A_64,B_65] :
      ( k6_domain_1(A_64,B_65) = k1_tarski(B_65)
      | ~ m1_subset_1(B_65,A_64)
      | v1_xboole_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_96,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_52,c_92])).

tff(c_97,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_100,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_97,c_20])).

tff(c_103,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_100])).

tff(c_106,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_103])).

tff(c_110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_106])).

tff(c_111,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_50,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ v6_orders_2(k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_77,plain,(
    ~ v6_orders_2(k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_113,plain,(
    ~ v6_orders_2(k1_tarski('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_77])).

tff(c_112,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_118,plain,(
    ! [A_66,B_67] :
      ( m1_subset_1(k6_domain_1(A_66,B_67),k1_zfmisc_1(A_66))
      | ~ m1_subset_1(B_67,A_66)
      | v1_xboole_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_127,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_118])).

tff(c_131,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_127])).

tff(c_132,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_131])).

tff(c_199,plain,(
    ! [B_92,A_93] :
      ( v6_orders_2(B_92,A_93)
      | ~ r7_relat_2(u1_orders_2(A_93),B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_orders_2(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_202,plain,
    ( v6_orders_2(k1_tarski('#skF_6'),'#skF_5')
    | ~ r7_relat_2(u1_orders_2('#skF_5'),k1_tarski('#skF_6'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_132,c_199])).

tff(c_209,plain,
    ( v6_orders_2(k1_tarski('#skF_6'),'#skF_5')
    | ~ r7_relat_2(u1_orders_2('#skF_5'),k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_202])).

tff(c_210,plain,(
    ~ r7_relat_2(u1_orders_2('#skF_5'),k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_209])).

tff(c_18,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_143,plain,(
    ! [A_70] :
      ( m1_subset_1(u1_orders_2(A_70),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_70),u1_struct_0(A_70))))
      | ~ l1_orders_2(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_16,plain,(
    ! [B_9,A_7] :
      ( v1_relat_1(B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_7))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_149,plain,(
    ! [A_70] :
      ( v1_relat_1(u1_orders_2(A_70))
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(A_70),u1_struct_0(A_70)))
      | ~ l1_orders_2(A_70) ) ),
    inference(resolution,[status(thm)],[c_143,c_16])).

tff(c_153,plain,(
    ! [A_70] :
      ( v1_relat_1(u1_orders_2(A_70))
      | ~ l1_orders_2(A_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_149])).

tff(c_86,plain,(
    ! [A_62,B_63] :
      ( r2_hidden('#skF_4'(A_62,B_63),B_63)
      | r7_relat_2(A_62,B_63)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_91,plain,(
    ! [A_62,A_1] :
      ( '#skF_4'(A_62,k1_tarski(A_1)) = A_1
      | r7_relat_2(A_62,k1_tarski(A_1))
      | ~ v1_relat_1(A_62) ) ),
    inference(resolution,[status(thm)],[c_86,c_2])).

tff(c_218,plain,
    ( '#skF_4'(u1_orders_2('#skF_5'),k1_tarski('#skF_6')) = '#skF_6'
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_91,c_210])).

tff(c_220,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_224,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_153,c_220])).

tff(c_228,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_224])).

tff(c_230,plain,(
    v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_229,plain,(
    '#skF_4'(u1_orders_2('#skF_5'),k1_tarski('#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_80,plain,(
    ! [A_60,B_61] :
      ( r2_hidden('#skF_3'(A_60,B_61),B_61)
      | r7_relat_2(A_60,B_61)
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_85,plain,(
    ! [A_60,A_1] :
      ( '#skF_3'(A_60,k1_tarski(A_1)) = A_1
      | r7_relat_2(A_60,k1_tarski(A_1))
      | ~ v1_relat_1(A_60) ) ),
    inference(resolution,[status(thm)],[c_80,c_2])).

tff(c_219,plain,
    ( '#skF_3'(u1_orders_2('#skF_5'),k1_tarski('#skF_6')) = '#skF_6'
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_85,c_210])).

tff(c_254,plain,(
    '#skF_3'(u1_orders_2('#skF_5'),k1_tarski('#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_219])).

tff(c_30,plain,(
    ! [A_16,B_26] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(A_16,B_26),'#skF_4'(A_16,B_26)),A_16)
      | r7_relat_2(A_16,B_26)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_258,plain,
    ( ~ r2_hidden(k4_tarski('#skF_6','#skF_4'(u1_orders_2('#skF_5'),k1_tarski('#skF_6'))),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k1_tarski('#skF_6'))
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_30])).

tff(c_268,plain,
    ( ~ r2_hidden(k4_tarski('#skF_6','#skF_6'),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_229,c_258])).

tff(c_269,plain,(
    ~ r2_hidden(k4_tarski('#skF_6','#skF_6'),u1_orders_2('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_210,c_268])).

tff(c_337,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_331,c_269])).

tff(c_350,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_197,c_337])).

tff(c_351,plain,(
    ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_388,plain,(
    ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_351])).

tff(c_394,plain,(
    ! [A_118,B_119] :
      ( m1_subset_1(k6_domain_1(A_118,B_119),k1_zfmisc_1(A_118))
      | ~ m1_subset_1(B_119,A_118)
      | v1_xboole_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_403,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_386,c_394])).

tff(c_407,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_403])).

tff(c_409,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_387,c_388,c_407])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:19:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.36  
% 2.57/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.36  %$ r1_orders_2 > v6_orders_2 > r7_relat_2 > r2_hidden > m1_subset_1 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 2.57/1.36  
% 2.57/1.36  %Foreground sorts:
% 2.57/1.36  
% 2.57/1.36  
% 2.57/1.36  %Background operators:
% 2.57/1.36  
% 2.57/1.36  
% 2.57/1.36  %Foreground operators:
% 2.57/1.36  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.57/1.36  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.57/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.57/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.57/1.36  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.57/1.36  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.57/1.36  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.57/1.36  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.57/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.57/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.57/1.36  tff('#skF_6', type, '#skF_6': $i).
% 2.57/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.57/1.36  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.57/1.36  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.57/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.57/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.57/1.36  tff(r7_relat_2, type, r7_relat_2: ($i * $i) > $o).
% 2.57/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.36  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.57/1.36  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.57/1.36  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.57/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.57/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.57/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.57/1.36  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.57/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.57/1.36  
% 2.79/1.38  tff(f_138, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v6_orders_2(k6_domain_1(u1_struct_0(A), B), A) & m1_subset_1(k6_domain_1(u1_struct_0(A), B), k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_orders_2)).
% 2.79/1.38  tff(f_100, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.79/1.38  tff(f_111, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.79/1.38  tff(f_51, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.79/1.38  tff(f_123, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, B, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_orders_2)).
% 2.79/1.38  tff(f_89, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) <=> r2_hidden(k4_tarski(B, C), u1_orders_2(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_orders_2)).
% 2.79/1.38  tff(f_96, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.79/1.38  tff(f_60, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_orders_2(B, A) <=> r7_relat_2(u1_orders_2(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_orders_2)).
% 2.79/1.38  tff(f_43, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.79/1.38  tff(f_104, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 2.79/1.38  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.79/1.38  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (![B]: (r7_relat_2(A, B) <=> (![C, D]: ~(((r2_hidden(C, B) & r2_hidden(D, B)) & ~r2_hidden(k4_tarski(C, D), A)) & ~r2_hidden(k4_tarski(D, C), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_relat_2)).
% 2.79/1.38  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.79/1.38  tff(c_54, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.79/1.38  tff(c_42, plain, (![A_42]: (l1_struct_0(A_42) | ~l1_orders_2(A_42))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.79/1.38  tff(c_58, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.79/1.38  tff(c_52, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.79/1.38  tff(c_361, plain, (![A_114, B_115]: (k6_domain_1(A_114, B_115)=k1_tarski(B_115) | ~m1_subset_1(B_115, A_114) | v1_xboole_0(A_114))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.79/1.38  tff(c_365, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_52, c_361])).
% 2.79/1.38  tff(c_372, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_365])).
% 2.79/1.38  tff(c_20, plain, (![A_12]: (~v1_xboole_0(u1_struct_0(A_12)) | ~l1_struct_0(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.79/1.38  tff(c_375, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_372, c_20])).
% 2.79/1.38  tff(c_378, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_58, c_375])).
% 2.79/1.38  tff(c_381, plain, (~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_42, c_378])).
% 2.79/1.38  tff(c_385, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_381])).
% 2.79/1.38  tff(c_387, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_365])).
% 2.79/1.38  tff(c_386, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_365])).
% 2.79/1.38  tff(c_56, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.79/1.38  tff(c_191, plain, (![A_88, B_89]: (r1_orders_2(A_88, B_89, B_89) | ~m1_subset_1(B_89, u1_struct_0(A_88)) | ~l1_orders_2(A_88) | ~v3_orders_2(A_88) | v2_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.79/1.38  tff(c_193, plain, (r1_orders_2('#skF_5', '#skF_6', '#skF_6') | ~l1_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_52, c_191])).
% 2.79/1.38  tff(c_196, plain, (r1_orders_2('#skF_5', '#skF_6', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_193])).
% 2.79/1.38  tff(c_197, plain, (r1_orders_2('#skF_5', '#skF_6', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_58, c_196])).
% 2.79/1.38  tff(c_331, plain, (![B_106, C_107, A_108]: (r2_hidden(k4_tarski(B_106, C_107), u1_orders_2(A_108)) | ~r1_orders_2(A_108, B_106, C_107) | ~m1_subset_1(C_107, u1_struct_0(A_108)) | ~m1_subset_1(B_106, u1_struct_0(A_108)) | ~l1_orders_2(A_108))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.79/1.38  tff(c_92, plain, (![A_64, B_65]: (k6_domain_1(A_64, B_65)=k1_tarski(B_65) | ~m1_subset_1(B_65, A_64) | v1_xboole_0(A_64))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.79/1.38  tff(c_96, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_52, c_92])).
% 2.79/1.38  tff(c_97, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_96])).
% 2.79/1.38  tff(c_100, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_97, c_20])).
% 2.79/1.38  tff(c_103, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_58, c_100])).
% 2.79/1.38  tff(c_106, plain, (~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_42, c_103])).
% 2.79/1.38  tff(c_110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_106])).
% 2.79/1.38  tff(c_111, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_96])).
% 2.79/1.38  tff(c_50, plain, (~m1_subset_1(k6_domain_1(u1_struct_0('#skF_5'), '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v6_orders_2(k6_domain_1(u1_struct_0('#skF_5'), '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.79/1.38  tff(c_77, plain, (~v6_orders_2(k6_domain_1(u1_struct_0('#skF_5'), '#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_50])).
% 2.79/1.38  tff(c_113, plain, (~v6_orders_2(k1_tarski('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_77])).
% 2.79/1.38  tff(c_112, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_96])).
% 2.79/1.38  tff(c_118, plain, (![A_66, B_67]: (m1_subset_1(k6_domain_1(A_66, B_67), k1_zfmisc_1(A_66)) | ~m1_subset_1(B_67, A_66) | v1_xboole_0(A_66))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.79/1.38  tff(c_127, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_111, c_118])).
% 2.79/1.38  tff(c_131, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_127])).
% 2.79/1.38  tff(c_132, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_112, c_131])).
% 2.79/1.38  tff(c_199, plain, (![B_92, A_93]: (v6_orders_2(B_92, A_93) | ~r7_relat_2(u1_orders_2(A_93), B_92) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_orders_2(A_93))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.79/1.38  tff(c_202, plain, (v6_orders_2(k1_tarski('#skF_6'), '#skF_5') | ~r7_relat_2(u1_orders_2('#skF_5'), k1_tarski('#skF_6')) | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_132, c_199])).
% 2.79/1.38  tff(c_209, plain, (v6_orders_2(k1_tarski('#skF_6'), '#skF_5') | ~r7_relat_2(u1_orders_2('#skF_5'), k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_202])).
% 2.79/1.38  tff(c_210, plain, (~r7_relat_2(u1_orders_2('#skF_5'), k1_tarski('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_113, c_209])).
% 2.79/1.38  tff(c_18, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.79/1.38  tff(c_143, plain, (![A_70]: (m1_subset_1(u1_orders_2(A_70), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_70), u1_struct_0(A_70)))) | ~l1_orders_2(A_70))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.79/1.38  tff(c_16, plain, (![B_9, A_7]: (v1_relat_1(B_9) | ~m1_subset_1(B_9, k1_zfmisc_1(A_7)) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.79/1.38  tff(c_149, plain, (![A_70]: (v1_relat_1(u1_orders_2(A_70)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(A_70), u1_struct_0(A_70))) | ~l1_orders_2(A_70))), inference(resolution, [status(thm)], [c_143, c_16])).
% 2.79/1.38  tff(c_153, plain, (![A_70]: (v1_relat_1(u1_orders_2(A_70)) | ~l1_orders_2(A_70))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_149])).
% 2.79/1.38  tff(c_86, plain, (![A_62, B_63]: (r2_hidden('#skF_4'(A_62, B_63), B_63) | r7_relat_2(A_62, B_63) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.79/1.38  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.79/1.38  tff(c_91, plain, (![A_62, A_1]: ('#skF_4'(A_62, k1_tarski(A_1))=A_1 | r7_relat_2(A_62, k1_tarski(A_1)) | ~v1_relat_1(A_62))), inference(resolution, [status(thm)], [c_86, c_2])).
% 2.79/1.38  tff(c_218, plain, ('#skF_4'(u1_orders_2('#skF_5'), k1_tarski('#skF_6'))='#skF_6' | ~v1_relat_1(u1_orders_2('#skF_5'))), inference(resolution, [status(thm)], [c_91, c_210])).
% 2.79/1.38  tff(c_220, plain, (~v1_relat_1(u1_orders_2('#skF_5'))), inference(splitLeft, [status(thm)], [c_218])).
% 2.79/1.38  tff(c_224, plain, (~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_153, c_220])).
% 2.79/1.38  tff(c_228, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_224])).
% 2.79/1.38  tff(c_230, plain, (v1_relat_1(u1_orders_2('#skF_5'))), inference(splitRight, [status(thm)], [c_218])).
% 2.79/1.38  tff(c_229, plain, ('#skF_4'(u1_orders_2('#skF_5'), k1_tarski('#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_218])).
% 2.79/1.38  tff(c_80, plain, (![A_60, B_61]: (r2_hidden('#skF_3'(A_60, B_61), B_61) | r7_relat_2(A_60, B_61) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.79/1.38  tff(c_85, plain, (![A_60, A_1]: ('#skF_3'(A_60, k1_tarski(A_1))=A_1 | r7_relat_2(A_60, k1_tarski(A_1)) | ~v1_relat_1(A_60))), inference(resolution, [status(thm)], [c_80, c_2])).
% 2.79/1.38  tff(c_219, plain, ('#skF_3'(u1_orders_2('#skF_5'), k1_tarski('#skF_6'))='#skF_6' | ~v1_relat_1(u1_orders_2('#skF_5'))), inference(resolution, [status(thm)], [c_85, c_210])).
% 2.79/1.38  tff(c_254, plain, ('#skF_3'(u1_orders_2('#skF_5'), k1_tarski('#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_230, c_219])).
% 2.79/1.38  tff(c_30, plain, (![A_16, B_26]: (~r2_hidden(k4_tarski('#skF_3'(A_16, B_26), '#skF_4'(A_16, B_26)), A_16) | r7_relat_2(A_16, B_26) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.79/1.38  tff(c_258, plain, (~r2_hidden(k4_tarski('#skF_6', '#skF_4'(u1_orders_2('#skF_5'), k1_tarski('#skF_6'))), u1_orders_2('#skF_5')) | r7_relat_2(u1_orders_2('#skF_5'), k1_tarski('#skF_6')) | ~v1_relat_1(u1_orders_2('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_254, c_30])).
% 2.79/1.38  tff(c_268, plain, (~r2_hidden(k4_tarski('#skF_6', '#skF_6'), u1_orders_2('#skF_5')) | r7_relat_2(u1_orders_2('#skF_5'), k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_230, c_229, c_258])).
% 2.79/1.38  tff(c_269, plain, (~r2_hidden(k4_tarski('#skF_6', '#skF_6'), u1_orders_2('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_210, c_268])).
% 2.79/1.38  tff(c_337, plain, (~r1_orders_2('#skF_5', '#skF_6', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_331, c_269])).
% 2.79/1.38  tff(c_350, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_197, c_337])).
% 2.79/1.38  tff(c_351, plain, (~m1_subset_1(k6_domain_1(u1_struct_0('#skF_5'), '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_50])).
% 2.79/1.38  tff(c_388, plain, (~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_386, c_351])).
% 2.79/1.38  tff(c_394, plain, (![A_118, B_119]: (m1_subset_1(k6_domain_1(A_118, B_119), k1_zfmisc_1(A_118)) | ~m1_subset_1(B_119, A_118) | v1_xboole_0(A_118))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.79/1.38  tff(c_403, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_386, c_394])).
% 2.79/1.38  tff(c_407, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_403])).
% 2.79/1.38  tff(c_409, plain, $false, inference(negUnitSimplification, [status(thm)], [c_387, c_388, c_407])).
% 2.79/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.38  
% 2.79/1.38  Inference rules
% 2.79/1.38  ----------------------
% 2.79/1.38  #Ref     : 0
% 2.79/1.38  #Sup     : 64
% 2.79/1.38  #Fact    : 0
% 2.79/1.38  #Define  : 0
% 2.79/1.38  #Split   : 6
% 2.79/1.38  #Chain   : 0
% 2.79/1.38  #Close   : 0
% 2.79/1.38  
% 2.79/1.38  Ordering : KBO
% 2.79/1.38  
% 2.79/1.38  Simplification rules
% 2.79/1.38  ----------------------
% 2.79/1.38  #Subsume      : 5
% 2.79/1.38  #Demod        : 35
% 2.79/1.38  #Tautology    : 22
% 2.79/1.38  #SimpNegUnit  : 14
% 2.79/1.38  #BackRed      : 3
% 2.79/1.38  
% 2.79/1.38  #Partial instantiations: 0
% 2.79/1.38  #Strategies tried      : 1
% 2.79/1.38  
% 2.79/1.38  Timing (in seconds)
% 2.79/1.38  ----------------------
% 2.79/1.38  Preprocessing        : 0.35
% 2.79/1.38  Parsing              : 0.17
% 2.79/1.38  CNF conversion       : 0.03
% 2.79/1.38  Main loop            : 0.27
% 2.79/1.38  Inferencing          : 0.10
% 2.79/1.38  Reduction            : 0.08
% 2.79/1.38  Demodulation         : 0.05
% 2.79/1.38  BG Simplification    : 0.02
% 2.79/1.38  Subsumption          : 0.04
% 2.79/1.38  Abstraction          : 0.02
% 2.79/1.38  MUC search           : 0.00
% 2.79/1.38  Cooper               : 0.00
% 2.79/1.38  Total                : 0.67
% 2.79/1.38  Index Insertion      : 0.00
% 2.79/1.38  Index Deletion       : 0.00
% 2.79/1.38  Index Matching       : 0.00
% 2.79/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
