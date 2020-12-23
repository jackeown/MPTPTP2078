%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1637+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:09 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 463 expanded)
%              Number of leaves         :   33 ( 168 expanded)
%              Depth                    :   19
%              Number of atoms          :  226 (1275 expanded)
%              Number of equality atoms :   38 ( 170 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > r2_hidden > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k5_waybel_0 > k3_waybel_0 > a_2_0_waybel_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_waybel_0,type,(
    k3_waybel_0: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k5_waybel_0,type,(
    k5_waybel_0: ( $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(a_2_0_waybel_0,type,(
    a_2_0_waybel_0: ( $i * $i ) > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r2_hidden(C,k5_waybel_0(A,B))
                <=> r1_orders_2(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_waybel_0)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_98,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k3_waybel_0(A,B) = a_2_0_waybel_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_waybel_0)).

tff(f_34,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k5_waybel_0(A,B) = k3_waybel_0(A,k6_domain_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_waybel_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & l1_orders_2(B)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
     => ( r2_hidden(A,a_2_0_waybel_0(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & ? [E] :
                ( m1_subset_1(E,u1_struct_0(B))
                & r1_orders_2(B,D,E)
                & r2_hidden(E,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_waybel_0)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_52,plain,
    ( r2_hidden('#skF_7',k5_waybel_0('#skF_5','#skF_6'))
    | r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_62,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_38,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_42,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_18,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_orders_2(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_64,plain,(
    ! [A_40,B_41] :
      ( k6_domain_1(A_40,B_41) = k1_tarski(B_41)
      | ~ m1_subset_1(B_41,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_71,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_38,c_64])).

tff(c_73,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_20,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(u1_struct_0(A_12))
      | ~ l1_struct_0(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_76,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_73,c_20])).

tff(c_79,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_76])).

tff(c_83,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_79])).

tff(c_87,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_83])).

tff(c_89,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_72,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_40,c_64])).

tff(c_94,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_72])).

tff(c_100,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1(k6_domain_1(A_46,B_47),k1_zfmisc_1(A_46))
      | ~ m1_subset_1(B_47,A_46)
      | v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_106,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_100])).

tff(c_112,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_106])).

tff(c_113,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_112])).

tff(c_163,plain,(
    ! [A_56,B_57] :
      ( k3_waybel_0(A_56,B_57) = a_2_0_waybel_0(A_56,B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_orders_2(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_169,plain,
    ( k3_waybel_0('#skF_5',k1_tarski('#skF_6')) = a_2_0_waybel_0('#skF_5',k1_tarski('#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_113,c_163])).

tff(c_180,plain,
    ( k3_waybel_0('#skF_5',k1_tarski('#skF_6')) = a_2_0_waybel_0('#skF_5',k1_tarski('#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_169])).

tff(c_181,plain,(
    k3_waybel_0('#skF_5',k1_tarski('#skF_6')) = a_2_0_waybel_0('#skF_5',k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_180])).

tff(c_192,plain,(
    ! [A_60,B_61] :
      ( k3_waybel_0(A_60,k6_domain_1(u1_struct_0(A_60),B_61)) = k5_waybel_0(A_60,B_61)
      | ~ m1_subset_1(B_61,u1_struct_0(A_60))
      | ~ l1_orders_2(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_201,plain,
    ( k3_waybel_0('#skF_5',k1_tarski('#skF_6')) = k5_waybel_0('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_192])).

tff(c_208,plain,
    ( a_2_0_waybel_0('#skF_5',k1_tarski('#skF_6')) = k5_waybel_0('#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_181,c_201])).

tff(c_209,plain,(
    a_2_0_waybel_0('#skF_5',k1_tarski('#skF_6')) = k5_waybel_0('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_208])).

tff(c_6,plain,(
    ! [C_8] : r2_hidden(C_8,k1_tarski(C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_441,plain,(
    ! [D_89,B_90,C_91,E_92] :
      ( r2_hidden(D_89,a_2_0_waybel_0(B_90,C_91))
      | ~ r2_hidden(E_92,C_91)
      | ~ r1_orders_2(B_90,D_89,E_92)
      | ~ m1_subset_1(E_92,u1_struct_0(B_90))
      | ~ m1_subset_1(D_89,u1_struct_0(B_90))
      | ~ m1_subset_1(C_91,k1_zfmisc_1(u1_struct_0(B_90)))
      | ~ l1_orders_2(B_90)
      | v2_struct_0(B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_525,plain,(
    ! [D_100,B_101,C_102] :
      ( r2_hidden(D_100,a_2_0_waybel_0(B_101,k1_tarski(C_102)))
      | ~ r1_orders_2(B_101,D_100,C_102)
      | ~ m1_subset_1(C_102,u1_struct_0(B_101))
      | ~ m1_subset_1(D_100,u1_struct_0(B_101))
      | ~ m1_subset_1(k1_tarski(C_102),k1_zfmisc_1(u1_struct_0(B_101)))
      | ~ l1_orders_2(B_101)
      | v2_struct_0(B_101) ) ),
    inference(resolution,[status(thm)],[c_6,c_441])).

tff(c_529,plain,(
    ! [D_100] :
      ( r2_hidden(D_100,a_2_0_waybel_0('#skF_5',k1_tarski('#skF_6')))
      | ~ r1_orders_2('#skF_5',D_100,'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(D_100,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_113,c_525])).

tff(c_536,plain,(
    ! [D_100] :
      ( r2_hidden(D_100,k5_waybel_0('#skF_5','#skF_6'))
      | ~ r1_orders_2('#skF_5',D_100,'#skF_6')
      | ~ m1_subset_1(D_100,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_209,c_529])).

tff(c_559,plain,(
    ! [D_104] :
      ( r2_hidden(D_104,k5_waybel_0('#skF_5','#skF_6'))
      | ~ r1_orders_2('#skF_5',D_104,'#skF_6')
      | ~ m1_subset_1(D_104,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_536])).

tff(c_46,plain,
    ( ~ r1_orders_2('#skF_5','#skF_7','#skF_6')
    | ~ r2_hidden('#skF_7',k5_waybel_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_63,plain,(
    ~ r2_hidden('#skF_7',k5_waybel_0('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_577,plain,
    ( ~ r1_orders_2('#skF_5','#skF_7','#skF_6')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_559,c_63])).

tff(c_586,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_62,c_577])).

tff(c_587,plain,(
    ~ r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_590,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_587])).

tff(c_592,plain,(
    ~ r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_595,plain,(
    ! [A_105,B_106] :
      ( k6_domain_1(A_105,B_106) = k1_tarski(B_106)
      | ~ m1_subset_1(B_106,A_105)
      | v1_xboole_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_602,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_38,c_595])).

tff(c_604,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_602])).

tff(c_607,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_604,c_20])).

tff(c_610,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_607])).

tff(c_613,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_610])).

tff(c_617,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_613])).

tff(c_619,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_602])).

tff(c_603,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_40,c_595])).

tff(c_625,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_619,c_603])).

tff(c_630,plain,(
    ! [A_109,B_110] :
      ( m1_subset_1(k6_domain_1(A_109,B_110),k1_zfmisc_1(A_109))
      | ~ m1_subset_1(B_110,A_109)
      | v1_xboole_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_636,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_625,c_630])).

tff(c_642,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_636])).

tff(c_643,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_619,c_642])).

tff(c_591,plain,(
    r2_hidden('#skF_7',k5_waybel_0('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_669,plain,(
    ! [A_117,B_118] :
      ( k3_waybel_0(A_117,B_118) = a_2_0_waybel_0(A_117,B_118)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_orders_2(A_117)
      | v2_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_675,plain,
    ( k3_waybel_0('#skF_5',k1_tarski('#skF_6')) = a_2_0_waybel_0('#skF_5',k1_tarski('#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_643,c_669])).

tff(c_686,plain,
    ( k3_waybel_0('#skF_5',k1_tarski('#skF_6')) = a_2_0_waybel_0('#skF_5',k1_tarski('#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_675])).

tff(c_687,plain,(
    k3_waybel_0('#skF_5',k1_tarski('#skF_6')) = a_2_0_waybel_0('#skF_5',k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_686])).

tff(c_722,plain,(
    ! [A_123,B_124] :
      ( k3_waybel_0(A_123,k6_domain_1(u1_struct_0(A_123),B_124)) = k5_waybel_0(A_123,B_124)
      | ~ m1_subset_1(B_124,u1_struct_0(A_123))
      | ~ l1_orders_2(A_123)
      | v2_struct_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_731,plain,
    ( k3_waybel_0('#skF_5',k1_tarski('#skF_6')) = k5_waybel_0('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_625,c_722])).

tff(c_738,plain,
    ( a_2_0_waybel_0('#skF_5',k1_tarski('#skF_6')) = k5_waybel_0('#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_687,c_731])).

tff(c_739,plain,(
    a_2_0_waybel_0('#skF_5',k1_tarski('#skF_6')) = k5_waybel_0('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_738])).

tff(c_753,plain,(
    ! [A_125,B_126,C_127] :
      ( '#skF_3'(A_125,B_126,C_127) = A_125
      | ~ r2_hidden(A_125,a_2_0_waybel_0(B_126,C_127))
      | ~ m1_subset_1(C_127,k1_zfmisc_1(u1_struct_0(B_126)))
      | ~ l1_orders_2(B_126)
      | v2_struct_0(B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_757,plain,(
    ! [A_125] :
      ( '#skF_3'(A_125,'#skF_5',k1_tarski('#skF_6')) = A_125
      | ~ r2_hidden(A_125,k5_waybel_0('#skF_5','#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_739,c_753])).

tff(c_768,plain,(
    ! [A_125] :
      ( '#skF_3'(A_125,'#skF_5',k1_tarski('#skF_6')) = A_125
      | ~ r2_hidden(A_125,k5_waybel_0('#skF_5','#skF_6'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_643,c_757])).

tff(c_791,plain,(
    ! [A_129] :
      ( '#skF_3'(A_129,'#skF_5',k1_tarski('#skF_6')) = A_129
      | ~ r2_hidden(A_129,k5_waybel_0('#skF_5','#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_768])).

tff(c_805,plain,(
    '#skF_3'('#skF_7','#skF_5',k1_tarski('#skF_6')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_591,c_791])).

tff(c_840,plain,(
    ! [A_132,B_133,C_134] :
      ( r2_hidden('#skF_4'(A_132,B_133,C_134),C_134)
      | ~ r2_hidden(A_132,a_2_0_waybel_0(B_133,C_134))
      | ~ m1_subset_1(C_134,k1_zfmisc_1(u1_struct_0(B_133)))
      | ~ l1_orders_2(B_133)
      | v2_struct_0(B_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_844,plain,(
    ! [A_132] :
      ( r2_hidden('#skF_4'(A_132,'#skF_5',k1_tarski('#skF_6')),k1_tarski('#skF_6'))
      | ~ r2_hidden(A_132,a_2_0_waybel_0('#skF_5',k1_tarski('#skF_6')))
      | ~ l1_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_643,c_840])).

tff(c_854,plain,(
    ! [A_132] :
      ( r2_hidden('#skF_4'(A_132,'#skF_5',k1_tarski('#skF_6')),k1_tarski('#skF_6'))
      | ~ r2_hidden(A_132,k5_waybel_0('#skF_5','#skF_6'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_739,c_844])).

tff(c_878,plain,(
    ! [A_140] :
      ( r2_hidden('#skF_4'(A_140,'#skF_5',k1_tarski('#skF_6')),k1_tarski('#skF_6'))
      | ~ r2_hidden(A_140,k5_waybel_0('#skF_5','#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_854])).

tff(c_4,plain,(
    ! [C_8,A_4] :
      ( C_8 = A_4
      | ~ r2_hidden(C_8,k1_tarski(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_883,plain,(
    ! [A_141] :
      ( '#skF_4'(A_141,'#skF_5',k1_tarski('#skF_6')) = '#skF_6'
      | ~ r2_hidden(A_141,k5_waybel_0('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_878,c_4])).

tff(c_897,plain,(
    '#skF_4'('#skF_7','#skF_5',k1_tarski('#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_591,c_883])).

tff(c_1006,plain,(
    ! [B_150,A_151,C_152] :
      ( r1_orders_2(B_150,'#skF_3'(A_151,B_150,C_152),'#skF_4'(A_151,B_150,C_152))
      | ~ r2_hidden(A_151,a_2_0_waybel_0(B_150,C_152))
      | ~ m1_subset_1(C_152,k1_zfmisc_1(u1_struct_0(B_150)))
      | ~ l1_orders_2(B_150)
      | v2_struct_0(B_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1018,plain,
    ( r1_orders_2('#skF_5','#skF_3'('#skF_7','#skF_5',k1_tarski('#skF_6')),'#skF_6')
    | ~ r2_hidden('#skF_7',a_2_0_waybel_0('#skF_5',k1_tarski('#skF_6')))
    | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_897,c_1006])).

tff(c_1032,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_643,c_591,c_739,c_805,c_1018])).

tff(c_1034,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_592,c_1032])).

%------------------------------------------------------------------------------
