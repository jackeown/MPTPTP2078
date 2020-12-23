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
% DateTime   : Thu Dec  3 10:19:43 EST 2020

% Result     : Theorem 6.62s
% Output     : CNFRefutation 6.62s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 432 expanded)
%              Number of leaves         :   37 ( 172 expanded)
%              Depth                    :   18
%              Number of atoms          :  271 (1661 expanded)
%              Number of equality atoms :   34 ( 107 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(a_2_1_orders_2,type,(
    a_2_1_orders_2: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k2_orders_2,type,(
    k2_orders_2: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_134,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r2_orders_2(A,B,C)
                <=> r2_hidden(B,k2_orders_2(A,k6_domain_1(u1_struct_0(A),C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_orders_2)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_44,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_112,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v6_orders_2(k6_domain_1(u1_struct_0(A),B),A)
            & m1_subset_1(k6_domain_1(u1_struct_0(A),B),k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_orders_2)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_orders_2(A,B) = a_2_1_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v3_orders_2(B)
        & v4_orders_2(B)
        & v5_orders_2(B)
        & l1_orders_2(B)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
     => ( r2_hidden(A,a_2_1_orders_2(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & ! [E] :
                ( m1_subset_1(E,u1_struct_0(B))
               => ( r2_hidden(E,C)
                 => r2_orders_2(B,D,E) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_56,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_54,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_52,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_50,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_46,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_26,plain,(
    ! [A_12] :
      ( l1_struct_0(A_12)
      | ~ l1_orders_2(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_5759,plain,(
    ! [A_7127,B_7128] :
      ( k6_domain_1(A_7127,B_7128) = k1_tarski(B_7128)
      | ~ m1_subset_1(B_7128,A_7127)
      | v1_xboole_0(A_7127) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_5766,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_46,c_5759])).

tff(c_5768,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_5766])).

tff(c_22,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(u1_struct_0(A_8))
      | ~ l1_struct_0(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_5772,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_5768,c_22])).

tff(c_5775,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_5772])).

tff(c_5778,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_5775])).

tff(c_5782,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_5778])).

tff(c_5783,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_5766])).

tff(c_5811,plain,(
    ! [A_7143,B_7144] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_7143),B_7144),k1_zfmisc_1(u1_struct_0(A_7143)))
      | ~ m1_subset_1(B_7144,u1_struct_0(A_7143))
      | ~ l1_orders_2(A_7143)
      | ~ v3_orders_2(A_7143)
      | v2_struct_0(A_7143) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_5817,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5783,c_5811])).

tff(c_5823,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_50,c_46,c_5817])).

tff(c_5824,plain,(
    m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_5823])).

tff(c_7220,plain,(
    ! [A_10327,B_10328] :
      ( k2_orders_2(A_10327,B_10328) = a_2_1_orders_2(A_10327,B_10328)
      | ~ m1_subset_1(B_10328,k1_zfmisc_1(u1_struct_0(A_10327)))
      | ~ l1_orders_2(A_10327)
      | ~ v5_orders_2(A_10327)
      | ~ v4_orders_2(A_10327)
      | ~ v3_orders_2(A_10327)
      | v2_struct_0(A_10327) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_7232,plain,
    ( k2_orders_2('#skF_5',k1_tarski('#skF_7')) = a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_5824,c_7220])).

tff(c_7242,plain,
    ( k2_orders_2('#skF_5',k1_tarski('#skF_7')) = a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_7232])).

tff(c_7243,plain,(
    k2_orders_2('#skF_5',k1_tarski('#skF_7')) = a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_7242])).

tff(c_109,plain,(
    ! [A_48,B_49] :
      ( k6_domain_1(A_48,B_49) = k1_tarski(B_49)
      | ~ m1_subset_1(B_49,A_48)
      | v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_116,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_46,c_109])).

tff(c_118,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_123,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_118,c_22])).

tff(c_126,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_123])).

tff(c_129,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_126])).

tff(c_133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_129])).

tff(c_134,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_66,plain,
    ( r2_orders_2('#skF_5','#skF_6','#skF_7')
    | r2_hidden('#skF_6',k2_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_69,plain,(
    r2_hidden('#skF_6',k2_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7'))) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_136,plain,(
    r2_hidden('#skF_6',k2_orders_2('#skF_5',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_69])).

tff(c_60,plain,
    ( ~ r2_hidden('#skF_6',k2_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7')))
    | ~ r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_142,plain,(
    ~ r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_134,c_60])).

tff(c_70,plain,(
    ! [A_38] : k2_tarski(A_38,A_38) = k1_tarski(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_6,plain,(
    ! [D_6,B_2] : r2_hidden(D_6,k2_tarski(D_6,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_76,plain,(
    ! [A_38] : r2_hidden(A_38,k1_tarski(A_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_6])).

tff(c_164,plain,(
    ! [A_61,B_62] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_61),B_62),k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ m1_subset_1(B_62,u1_struct_0(A_61))
      | ~ l1_orders_2(A_61)
      | ~ v3_orders_2(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_173,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_164])).

tff(c_179,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_50,c_46,c_173])).

tff(c_180,plain,(
    m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_179])).

tff(c_1601,plain,(
    ! [A_3366,B_3367] :
      ( k2_orders_2(A_3366,B_3367) = a_2_1_orders_2(A_3366,B_3367)
      | ~ m1_subset_1(B_3367,k1_zfmisc_1(u1_struct_0(A_3366)))
      | ~ l1_orders_2(A_3366)
      | ~ v5_orders_2(A_3366)
      | ~ v4_orders_2(A_3366)
      | ~ v3_orders_2(A_3366)
      | v2_struct_0(A_3366) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1608,plain,
    ( k2_orders_2('#skF_5',k1_tarski('#skF_7')) = a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_180,c_1601])).

tff(c_1619,plain,
    ( k2_orders_2('#skF_5',k1_tarski('#skF_7')) = a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_1608])).

tff(c_1620,plain,(
    k2_orders_2('#skF_5',k1_tarski('#skF_7')) = a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1619])).

tff(c_1626,plain,(
    r2_hidden('#skF_6',a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1620,c_136])).

tff(c_2030,plain,(
    ! [A_3880,B_3881,C_3882] :
      ( '#skF_3'(A_3880,B_3881,C_3882) = A_3880
      | ~ r2_hidden(A_3880,a_2_1_orders_2(B_3881,C_3882))
      | ~ m1_subset_1(C_3882,k1_zfmisc_1(u1_struct_0(B_3881)))
      | ~ l1_orders_2(B_3881)
      | ~ v5_orders_2(B_3881)
      | ~ v4_orders_2(B_3881)
      | ~ v3_orders_2(B_3881)
      | v2_struct_0(B_3881) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2032,plain,
    ( '#skF_3'('#skF_6','#skF_5',k1_tarski('#skF_7')) = '#skF_6'
    | ~ m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1626,c_2030])).

tff(c_2041,plain,
    ( '#skF_3'('#skF_6','#skF_5',k1_tarski('#skF_7')) = '#skF_6'
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_180,c_2032])).

tff(c_2042,plain,(
    '#skF_3'('#skF_6','#skF_5',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2041])).

tff(c_4363,plain,(
    ! [B_6013,A_6014,C_6015,E_6016] :
      ( r2_orders_2(B_6013,'#skF_3'(A_6014,B_6013,C_6015),E_6016)
      | ~ r2_hidden(E_6016,C_6015)
      | ~ m1_subset_1(E_6016,u1_struct_0(B_6013))
      | ~ r2_hidden(A_6014,a_2_1_orders_2(B_6013,C_6015))
      | ~ m1_subset_1(C_6015,k1_zfmisc_1(u1_struct_0(B_6013)))
      | ~ l1_orders_2(B_6013)
      | ~ v5_orders_2(B_6013)
      | ~ v4_orders_2(B_6013)
      | ~ v3_orders_2(B_6013)
      | v2_struct_0(B_6013) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4369,plain,(
    ! [A_6014,E_6016] :
      ( r2_orders_2('#skF_5','#skF_3'(A_6014,'#skF_5',k1_tarski('#skF_7')),E_6016)
      | ~ r2_hidden(E_6016,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_6016,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_6014,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_180,c_4363])).

tff(c_4378,plain,(
    ! [A_6014,E_6016] :
      ( r2_orders_2('#skF_5','#skF_3'(A_6014,'#skF_5',k1_tarski('#skF_7')),E_6016)
      | ~ r2_hidden(E_6016,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_6016,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_6014,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_4369])).

tff(c_5527,plain,(
    ! [A_6822,E_6823] :
      ( r2_orders_2('#skF_5','#skF_3'(A_6822,'#skF_5',k1_tarski('#skF_7')),E_6823)
      | ~ r2_hidden(E_6823,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_6823,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_6822,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4378])).

tff(c_5533,plain,(
    ! [E_6823] :
      ( r2_orders_2('#skF_5','#skF_6',E_6823)
      | ~ r2_hidden(E_6823,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_6823,u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_6',a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2042,c_5527])).

tff(c_5693,plain,(
    ! [E_7044] :
      ( r2_orders_2('#skF_5','#skF_6',E_7044)
      | ~ r2_hidden(E_7044,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_7044,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1626,c_5533])).

tff(c_5708,plain,
    ( r2_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_76,c_5693])).

tff(c_5713,plain,(
    r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_5708])).

tff(c_5715,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_5713])).

tff(c_5716,plain,(
    r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_5738,plain,(
    ~ r2_hidden('#skF_6',k2_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5716,c_60])).

tff(c_5790,plain,(
    ~ r2_hidden('#skF_6',k2_orders_2('#skF_5',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5783,c_5738])).

tff(c_7298,plain,(
    ~ r2_hidden('#skF_6',a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7243,c_5790])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_7927,plain,(
    ! [D_11358,B_11359,C_11360] :
      ( r2_hidden('#skF_4'(D_11358,B_11359,C_11360,D_11358),C_11360)
      | r2_hidden(D_11358,a_2_1_orders_2(B_11359,C_11360))
      | ~ m1_subset_1(D_11358,u1_struct_0(B_11359))
      | ~ m1_subset_1(C_11360,k1_zfmisc_1(u1_struct_0(B_11359)))
      | ~ l1_orders_2(B_11359)
      | ~ v5_orders_2(B_11359)
      | ~ v4_orders_2(B_11359)
      | ~ v3_orders_2(B_11359)
      | v2_struct_0(B_11359) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_7937,plain,(
    ! [D_11358] :
      ( r2_hidden('#skF_4'(D_11358,'#skF_5',k1_tarski('#skF_7'),D_11358),k1_tarski('#skF_7'))
      | r2_hidden(D_11358,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
      | ~ m1_subset_1(D_11358,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5824,c_7927])).

tff(c_7946,plain,(
    ! [D_11358] :
      ( r2_hidden('#skF_4'(D_11358,'#skF_5',k1_tarski('#skF_7'),D_11358),k1_tarski('#skF_7'))
      | r2_hidden(D_11358,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
      | ~ m1_subset_1(D_11358,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_7937])).

tff(c_8368,plain,(
    ! [D_11730] :
      ( r2_hidden('#skF_4'(D_11730,'#skF_5',k1_tarski('#skF_7'),D_11730),k1_tarski('#skF_7'))
      | r2_hidden(D_11730,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
      | ~ m1_subset_1(D_11730,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_7946])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_5739,plain,(
    ! [D_7122,B_7123,A_7124] :
      ( D_7122 = B_7123
      | D_7122 = A_7124
      | ~ r2_hidden(D_7122,k2_tarski(A_7124,B_7123)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_5745,plain,(
    ! [D_7122,A_7] :
      ( D_7122 = A_7
      | D_7122 = A_7
      | ~ r2_hidden(D_7122,k1_tarski(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_5739])).

tff(c_8457,plain,(
    ! [D_11803] :
      ( '#skF_4'(D_11803,'#skF_5',k1_tarski('#skF_7'),D_11803) = '#skF_7'
      | r2_hidden(D_11803,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
      | ~ m1_subset_1(D_11803,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_8368,c_5745])).

tff(c_8476,plain,
    ( '#skF_4'('#skF_6','#skF_5',k1_tarski('#skF_7'),'#skF_6') = '#skF_7'
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_8457,c_7298])).

tff(c_8571,plain,(
    '#skF_4'('#skF_6','#skF_5',k1_tarski('#skF_7'),'#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_8476])).

tff(c_28,plain,(
    ! [B_14,D_24,C_15] :
      ( ~ r2_orders_2(B_14,D_24,'#skF_4'(D_24,B_14,C_15,D_24))
      | r2_hidden(D_24,a_2_1_orders_2(B_14,C_15))
      | ~ m1_subset_1(D_24,u1_struct_0(B_14))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(u1_struct_0(B_14)))
      | ~ l1_orders_2(B_14)
      | ~ v5_orders_2(B_14)
      | ~ v4_orders_2(B_14)
      | ~ v3_orders_2(B_14)
      | v2_struct_0(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_8579,plain,
    ( ~ r2_orders_2('#skF_5','#skF_6','#skF_7')
    | r2_hidden('#skF_6',a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_8571,c_28])).

tff(c_8622,plain,
    ( r2_hidden('#skF_6',a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_5824,c_48,c_5716,c_8579])).

tff(c_8624,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_7298,c_8622])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:32:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.62/2.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.62/2.33  
% 6.62/2.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.62/2.33  %$ r2_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 6.62/2.33  
% 6.62/2.33  %Foreground sorts:
% 6.62/2.33  
% 6.62/2.33  
% 6.62/2.33  %Background operators:
% 6.62/2.33  
% 6.62/2.33  
% 6.62/2.33  %Foreground operators:
% 6.62/2.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.62/2.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.62/2.33  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 6.62/2.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.62/2.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.62/2.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.62/2.33  tff('#skF_7', type, '#skF_7': $i).
% 6.62/2.33  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 6.62/2.33  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 6.62/2.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.62/2.33  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 6.62/2.33  tff('#skF_5', type, '#skF_5': $i).
% 6.62/2.33  tff('#skF_6', type, '#skF_6': $i).
% 6.62/2.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.62/2.33  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 6.62/2.33  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 6.62/2.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.62/2.33  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.62/2.33  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 6.62/2.33  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 6.62/2.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.62/2.33  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.62/2.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.62/2.33  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 6.62/2.33  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 6.62/2.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.62/2.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.62/2.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.62/2.33  
% 6.62/2.35  tff(f_134, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> r2_hidden(B, k2_orders_2(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_orders_2)).
% 6.62/2.35  tff(f_64, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 6.62/2.35  tff(f_98, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 6.62/2.35  tff(f_44, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 6.62/2.35  tff(f_112, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v6_orders_2(k6_domain_1(u1_struct_0(A), B), A) & m1_subset_1(k6_domain_1(u1_struct_0(A), B), k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_orders_2)).
% 6.62/2.35  tff(f_60, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_orders_2)).
% 6.62/2.35  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.62/2.35  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 6.62/2.35  tff(f_91, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 6.62/2.35  tff(c_58, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.62/2.35  tff(c_56, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.62/2.35  tff(c_54, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.62/2.35  tff(c_52, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.62/2.35  tff(c_50, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.62/2.35  tff(c_46, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.62/2.35  tff(c_26, plain, (![A_12]: (l1_struct_0(A_12) | ~l1_orders_2(A_12))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.62/2.35  tff(c_5759, plain, (![A_7127, B_7128]: (k6_domain_1(A_7127, B_7128)=k1_tarski(B_7128) | ~m1_subset_1(B_7128, A_7127) | v1_xboole_0(A_7127))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.62/2.35  tff(c_5766, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')=k1_tarski('#skF_7') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_46, c_5759])).
% 6.62/2.35  tff(c_5768, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_5766])).
% 6.62/2.35  tff(c_22, plain, (![A_8]: (~v1_xboole_0(u1_struct_0(A_8)) | ~l1_struct_0(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.62/2.35  tff(c_5772, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_5768, c_22])).
% 6.62/2.35  tff(c_5775, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_58, c_5772])).
% 6.62/2.35  tff(c_5778, plain, (~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_26, c_5775])).
% 6.62/2.35  tff(c_5782, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_5778])).
% 6.62/2.35  tff(c_5783, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_5766])).
% 6.62/2.35  tff(c_5811, plain, (![A_7143, B_7144]: (m1_subset_1(k6_domain_1(u1_struct_0(A_7143), B_7144), k1_zfmisc_1(u1_struct_0(A_7143))) | ~m1_subset_1(B_7144, u1_struct_0(A_7143)) | ~l1_orders_2(A_7143) | ~v3_orders_2(A_7143) | v2_struct_0(A_7143))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.62/2.35  tff(c_5817, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5783, c_5811])).
% 6.62/2.35  tff(c_5823, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_50, c_46, c_5817])).
% 6.62/2.35  tff(c_5824, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_5823])).
% 6.62/2.35  tff(c_7220, plain, (![A_10327, B_10328]: (k2_orders_2(A_10327, B_10328)=a_2_1_orders_2(A_10327, B_10328) | ~m1_subset_1(B_10328, k1_zfmisc_1(u1_struct_0(A_10327))) | ~l1_orders_2(A_10327) | ~v5_orders_2(A_10327) | ~v4_orders_2(A_10327) | ~v3_orders_2(A_10327) | v2_struct_0(A_10327))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.62/2.35  tff(c_7232, plain, (k2_orders_2('#skF_5', k1_tarski('#skF_7'))=a_2_1_orders_2('#skF_5', k1_tarski('#skF_7')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_5824, c_7220])).
% 6.62/2.35  tff(c_7242, plain, (k2_orders_2('#skF_5', k1_tarski('#skF_7'))=a_2_1_orders_2('#skF_5', k1_tarski('#skF_7')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_7232])).
% 6.62/2.35  tff(c_7243, plain, (k2_orders_2('#skF_5', k1_tarski('#skF_7'))=a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_58, c_7242])).
% 6.62/2.35  tff(c_109, plain, (![A_48, B_49]: (k6_domain_1(A_48, B_49)=k1_tarski(B_49) | ~m1_subset_1(B_49, A_48) | v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.62/2.35  tff(c_116, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')=k1_tarski('#skF_7') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_46, c_109])).
% 6.62/2.35  tff(c_118, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_116])).
% 6.62/2.35  tff(c_123, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_118, c_22])).
% 6.62/2.35  tff(c_126, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_58, c_123])).
% 6.62/2.35  tff(c_129, plain, (~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_26, c_126])).
% 6.62/2.35  tff(c_133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_129])).
% 6.62/2.35  tff(c_134, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_116])).
% 6.62/2.35  tff(c_66, plain, (r2_orders_2('#skF_5', '#skF_6', '#skF_7') | r2_hidden('#skF_6', k2_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.62/2.35  tff(c_69, plain, (r2_hidden('#skF_6', k2_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')))), inference(splitLeft, [status(thm)], [c_66])).
% 6.62/2.35  tff(c_136, plain, (r2_hidden('#skF_6', k2_orders_2('#skF_5', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_69])).
% 6.62/2.35  tff(c_60, plain, (~r2_hidden('#skF_6', k2_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7'))) | ~r2_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.62/2.35  tff(c_142, plain, (~r2_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_134, c_60])).
% 6.62/2.35  tff(c_70, plain, (![A_38]: (k2_tarski(A_38, A_38)=k1_tarski(A_38))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.62/2.35  tff(c_6, plain, (![D_6, B_2]: (r2_hidden(D_6, k2_tarski(D_6, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.62/2.35  tff(c_76, plain, (![A_38]: (r2_hidden(A_38, k1_tarski(A_38)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_6])).
% 6.62/2.35  tff(c_164, plain, (![A_61, B_62]: (m1_subset_1(k6_domain_1(u1_struct_0(A_61), B_62), k1_zfmisc_1(u1_struct_0(A_61))) | ~m1_subset_1(B_62, u1_struct_0(A_61)) | ~l1_orders_2(A_61) | ~v3_orders_2(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.62/2.35  tff(c_173, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_134, c_164])).
% 6.62/2.35  tff(c_179, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_50, c_46, c_173])).
% 6.62/2.35  tff(c_180, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_179])).
% 6.62/2.35  tff(c_1601, plain, (![A_3366, B_3367]: (k2_orders_2(A_3366, B_3367)=a_2_1_orders_2(A_3366, B_3367) | ~m1_subset_1(B_3367, k1_zfmisc_1(u1_struct_0(A_3366))) | ~l1_orders_2(A_3366) | ~v5_orders_2(A_3366) | ~v4_orders_2(A_3366) | ~v3_orders_2(A_3366) | v2_struct_0(A_3366))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.62/2.35  tff(c_1608, plain, (k2_orders_2('#skF_5', k1_tarski('#skF_7'))=a_2_1_orders_2('#skF_5', k1_tarski('#skF_7')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_180, c_1601])).
% 6.62/2.35  tff(c_1619, plain, (k2_orders_2('#skF_5', k1_tarski('#skF_7'))=a_2_1_orders_2('#skF_5', k1_tarski('#skF_7')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_1608])).
% 6.62/2.35  tff(c_1620, plain, (k2_orders_2('#skF_5', k1_tarski('#skF_7'))=a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_58, c_1619])).
% 6.62/2.35  tff(c_1626, plain, (r2_hidden('#skF_6', a_2_1_orders_2('#skF_5', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_1620, c_136])).
% 6.62/2.35  tff(c_2030, plain, (![A_3880, B_3881, C_3882]: ('#skF_3'(A_3880, B_3881, C_3882)=A_3880 | ~r2_hidden(A_3880, a_2_1_orders_2(B_3881, C_3882)) | ~m1_subset_1(C_3882, k1_zfmisc_1(u1_struct_0(B_3881))) | ~l1_orders_2(B_3881) | ~v5_orders_2(B_3881) | ~v4_orders_2(B_3881) | ~v3_orders_2(B_3881) | v2_struct_0(B_3881))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.62/2.35  tff(c_2032, plain, ('#skF_3'('#skF_6', '#skF_5', k1_tarski('#skF_7'))='#skF_6' | ~m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1626, c_2030])).
% 6.62/2.35  tff(c_2041, plain, ('#skF_3'('#skF_6', '#skF_5', k1_tarski('#skF_7'))='#skF_6' | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_180, c_2032])).
% 6.62/2.35  tff(c_2042, plain, ('#skF_3'('#skF_6', '#skF_5', k1_tarski('#skF_7'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_58, c_2041])).
% 6.62/2.35  tff(c_4363, plain, (![B_6013, A_6014, C_6015, E_6016]: (r2_orders_2(B_6013, '#skF_3'(A_6014, B_6013, C_6015), E_6016) | ~r2_hidden(E_6016, C_6015) | ~m1_subset_1(E_6016, u1_struct_0(B_6013)) | ~r2_hidden(A_6014, a_2_1_orders_2(B_6013, C_6015)) | ~m1_subset_1(C_6015, k1_zfmisc_1(u1_struct_0(B_6013))) | ~l1_orders_2(B_6013) | ~v5_orders_2(B_6013) | ~v4_orders_2(B_6013) | ~v3_orders_2(B_6013) | v2_struct_0(B_6013))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.62/2.35  tff(c_4369, plain, (![A_6014, E_6016]: (r2_orders_2('#skF_5', '#skF_3'(A_6014, '#skF_5', k1_tarski('#skF_7')), E_6016) | ~r2_hidden(E_6016, k1_tarski('#skF_7')) | ~m1_subset_1(E_6016, u1_struct_0('#skF_5')) | ~r2_hidden(A_6014, a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_180, c_4363])).
% 6.62/2.35  tff(c_4378, plain, (![A_6014, E_6016]: (r2_orders_2('#skF_5', '#skF_3'(A_6014, '#skF_5', k1_tarski('#skF_7')), E_6016) | ~r2_hidden(E_6016, k1_tarski('#skF_7')) | ~m1_subset_1(E_6016, u1_struct_0('#skF_5')) | ~r2_hidden(A_6014, a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_4369])).
% 6.62/2.35  tff(c_5527, plain, (![A_6822, E_6823]: (r2_orders_2('#skF_5', '#skF_3'(A_6822, '#skF_5', k1_tarski('#skF_7')), E_6823) | ~r2_hidden(E_6823, k1_tarski('#skF_7')) | ~m1_subset_1(E_6823, u1_struct_0('#skF_5')) | ~r2_hidden(A_6822, a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_4378])).
% 6.62/2.35  tff(c_5533, plain, (![E_6823]: (r2_orders_2('#skF_5', '#skF_6', E_6823) | ~r2_hidden(E_6823, k1_tarski('#skF_7')) | ~m1_subset_1(E_6823, u1_struct_0('#skF_5')) | ~r2_hidden('#skF_6', a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_2042, c_5527])).
% 6.62/2.35  tff(c_5693, plain, (![E_7044]: (r2_orders_2('#skF_5', '#skF_6', E_7044) | ~r2_hidden(E_7044, k1_tarski('#skF_7')) | ~m1_subset_1(E_7044, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_1626, c_5533])).
% 6.62/2.35  tff(c_5708, plain, (r2_orders_2('#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_76, c_5693])).
% 6.62/2.35  tff(c_5713, plain, (r2_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_5708])).
% 6.62/2.35  tff(c_5715, plain, $false, inference(negUnitSimplification, [status(thm)], [c_142, c_5713])).
% 6.62/2.35  tff(c_5716, plain, (r2_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_66])).
% 6.62/2.35  tff(c_5738, plain, (~r2_hidden('#skF_6', k2_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_5716, c_60])).
% 6.62/2.35  tff(c_5790, plain, (~r2_hidden('#skF_6', k2_orders_2('#skF_5', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_5783, c_5738])).
% 6.62/2.35  tff(c_7298, plain, (~r2_hidden('#skF_6', a_2_1_orders_2('#skF_5', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_7243, c_5790])).
% 6.62/2.35  tff(c_48, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.62/2.35  tff(c_7927, plain, (![D_11358, B_11359, C_11360]: (r2_hidden('#skF_4'(D_11358, B_11359, C_11360, D_11358), C_11360) | r2_hidden(D_11358, a_2_1_orders_2(B_11359, C_11360)) | ~m1_subset_1(D_11358, u1_struct_0(B_11359)) | ~m1_subset_1(C_11360, k1_zfmisc_1(u1_struct_0(B_11359))) | ~l1_orders_2(B_11359) | ~v5_orders_2(B_11359) | ~v4_orders_2(B_11359) | ~v3_orders_2(B_11359) | v2_struct_0(B_11359))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.62/2.35  tff(c_7937, plain, (![D_11358]: (r2_hidden('#skF_4'(D_11358, '#skF_5', k1_tarski('#skF_7'), D_11358), k1_tarski('#skF_7')) | r2_hidden(D_11358, a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | ~m1_subset_1(D_11358, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_5824, c_7927])).
% 6.62/2.35  tff(c_7946, plain, (![D_11358]: (r2_hidden('#skF_4'(D_11358, '#skF_5', k1_tarski('#skF_7'), D_11358), k1_tarski('#skF_7')) | r2_hidden(D_11358, a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | ~m1_subset_1(D_11358, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_7937])).
% 6.62/2.35  tff(c_8368, plain, (![D_11730]: (r2_hidden('#skF_4'(D_11730, '#skF_5', k1_tarski('#skF_7'), D_11730), k1_tarski('#skF_7')) | r2_hidden(D_11730, a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | ~m1_subset_1(D_11730, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_7946])).
% 6.62/2.35  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.62/2.35  tff(c_5739, plain, (![D_7122, B_7123, A_7124]: (D_7122=B_7123 | D_7122=A_7124 | ~r2_hidden(D_7122, k2_tarski(A_7124, B_7123)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.62/2.35  tff(c_5745, plain, (![D_7122, A_7]: (D_7122=A_7 | D_7122=A_7 | ~r2_hidden(D_7122, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_5739])).
% 6.62/2.35  tff(c_8457, plain, (![D_11803]: ('#skF_4'(D_11803, '#skF_5', k1_tarski('#skF_7'), D_11803)='#skF_7' | r2_hidden(D_11803, a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | ~m1_subset_1(D_11803, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_8368, c_5745])).
% 6.62/2.35  tff(c_8476, plain, ('#skF_4'('#skF_6', '#skF_5', k1_tarski('#skF_7'), '#skF_6')='#skF_7' | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_8457, c_7298])).
% 6.62/2.35  tff(c_8571, plain, ('#skF_4'('#skF_6', '#skF_5', k1_tarski('#skF_7'), '#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_8476])).
% 6.62/2.35  tff(c_28, plain, (![B_14, D_24, C_15]: (~r2_orders_2(B_14, D_24, '#skF_4'(D_24, B_14, C_15, D_24)) | r2_hidden(D_24, a_2_1_orders_2(B_14, C_15)) | ~m1_subset_1(D_24, u1_struct_0(B_14)) | ~m1_subset_1(C_15, k1_zfmisc_1(u1_struct_0(B_14))) | ~l1_orders_2(B_14) | ~v5_orders_2(B_14) | ~v4_orders_2(B_14) | ~v3_orders_2(B_14) | v2_struct_0(B_14))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.62/2.35  tff(c_8579, plain, (~r2_orders_2('#skF_5', '#skF_6', '#skF_7') | r2_hidden('#skF_6', a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_8571, c_28])).
% 6.62/2.35  tff(c_8622, plain, (r2_hidden('#skF_6', a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_5824, c_48, c_5716, c_8579])).
% 6.62/2.35  tff(c_8624, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_7298, c_8622])).
% 6.62/2.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.62/2.35  
% 6.62/2.35  Inference rules
% 6.62/2.35  ----------------------
% 6.62/2.35  #Ref     : 0
% 6.62/2.35  #Sup     : 1177
% 6.62/2.35  #Fact    : 40
% 6.62/2.35  #Define  : 0
% 6.62/2.35  #Split   : 23
% 6.62/2.35  #Chain   : 0
% 6.62/2.35  #Close   : 0
% 6.62/2.35  
% 6.62/2.35  Ordering : KBO
% 6.62/2.35  
% 6.62/2.35  Simplification rules
% 6.62/2.35  ----------------------
% 6.62/2.35  #Subsume      : 419
% 6.62/2.35  #Demod        : 340
% 6.62/2.35  #Tautology    : 355
% 6.62/2.35  #SimpNegUnit  : 53
% 6.62/2.35  #BackRed      : 4
% 6.62/2.35  
% 6.62/2.35  #Partial instantiations: 6804
% 6.62/2.35  #Strategies tried      : 1
% 6.62/2.35  
% 6.62/2.35  Timing (in seconds)
% 6.62/2.35  ----------------------
% 6.62/2.35  Preprocessing        : 0.33
% 6.62/2.35  Parsing              : 0.16
% 6.62/2.35  CNF conversion       : 0.03
% 6.62/2.35  Main loop            : 1.25
% 6.62/2.35  Inferencing          : 0.60
% 6.62/2.35  Reduction            : 0.29
% 6.62/2.35  Demodulation         : 0.20
% 6.62/2.35  BG Simplification    : 0.05
% 6.62/2.35  Subsumption          : 0.24
% 6.62/2.35  Abstraction          : 0.06
% 6.62/2.35  MUC search           : 0.00
% 6.62/2.35  Cooper               : 0.00
% 6.62/2.35  Total                : 1.62
% 6.62/2.35  Index Insertion      : 0.00
% 6.62/2.35  Index Deletion       : 0.00
% 6.62/2.35  Index Matching       : 0.00
% 6.62/2.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
