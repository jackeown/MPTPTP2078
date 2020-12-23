%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:42 EST 2020

% Result     : Theorem 3.30s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 406 expanded)
%              Number of leaves         :   35 ( 155 expanded)
%              Depth                    :   18
%              Number of atoms          :  253 (1443 expanded)
%              Number of equality atoms :   27 ( 114 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_125,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_orders_2)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_42,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_orders_2(A,B) = a_2_1_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_96,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_48,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_46,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_44,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_42,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_22,plain,(
    ! [A_13] :
      ( l1_struct_0(A_13)
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_38,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_791,plain,(
    ! [A_108,B_109] :
      ( k6_domain_1(A_108,B_109) = k1_tarski(B_109)
      | ~ m1_subset_1(B_109,A_108)
      | v1_xboole_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_798,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_38,c_791])).

tff(c_800,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_798])).

tff(c_16,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(u1_struct_0(A_7))
      | ~ l1_struct_0(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_803,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_800,c_16])).

tff(c_806,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_803])).

tff(c_809,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_806])).

tff(c_813,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_809])).

tff(c_815,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_798])).

tff(c_814,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_798])).

tff(c_827,plain,(
    ! [A_112,B_113] :
      ( m1_subset_1(k6_domain_1(A_112,B_113),k1_zfmisc_1(A_112))
      | ~ m1_subset_1(B_113,A_112)
      | v1_xboole_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_836,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_814,c_827])).

tff(c_842,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_836])).

tff(c_843,plain,(
    m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_815,c_842])).

tff(c_866,plain,(
    ! [A_120,B_121] :
      ( k2_orders_2(A_120,B_121) = a_2_1_orders_2(A_120,B_121)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_orders_2(A_120)
      | ~ v5_orders_2(A_120)
      | ~ v4_orders_2(A_120)
      | ~ v3_orders_2(A_120)
      | v2_struct_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_869,plain,
    ( k2_orders_2('#skF_5',k1_tarski('#skF_7')) = a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_843,c_866])).

tff(c_879,plain,
    ( k2_orders_2('#skF_5',k1_tarski('#skF_7')) = a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_869])).

tff(c_880,plain,(
    k2_orders_2('#skF_5',k1_tarski('#skF_7')) = a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_879])).

tff(c_58,plain,
    ( r2_orders_2('#skF_5','#skF_6','#skF_7')
    | r2_hidden('#skF_6',k2_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_61,plain,(
    r2_hidden('#skF_6',k2_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7'))) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_52,plain,
    ( ~ r2_hidden('#skF_6',k2_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7')))
    | ~ r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_109,plain,(
    ~ r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_52])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_78,plain,(
    ! [A_39,B_40] :
      ( k6_domain_1(A_39,B_40) = k1_tarski(B_40)
      | ~ m1_subset_1(B_40,A_39)
      | v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_85,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_38,c_78])).

tff(c_92,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_95,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_92,c_16])).

tff(c_98,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_95])).

tff(c_101,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_98])).

tff(c_105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_101])).

tff(c_107,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_106,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k6_domain_1(A_11,B_12),k1_zfmisc_1(A_11))
      | ~ m1_subset_1(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_114,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_20])).

tff(c_118,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_114])).

tff(c_119,plain,(
    m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_118])).

tff(c_180,plain,(
    ! [A_55,B_56] :
      ( k2_orders_2(A_55,B_56) = a_2_1_orders_2(A_55,B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_orders_2(A_55)
      | ~ v5_orders_2(A_55)
      | ~ v4_orders_2(A_55)
      | ~ v3_orders_2(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_186,plain,
    ( k2_orders_2('#skF_5',k1_tarski('#skF_7')) = a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_119,c_180])).

tff(c_197,plain,
    ( k2_orders_2('#skF_5',k1_tarski('#skF_7')) = a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_186])).

tff(c_198,plain,(
    k2_orders_2('#skF_5',k1_tarski('#skF_7')) = a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_197])).

tff(c_110,plain,(
    r2_hidden('#skF_6',k2_orders_2('#skF_5',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_61])).

tff(c_204,plain,(
    r2_hidden('#skF_6',a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_110])).

tff(c_209,plain,(
    ! [A_57,B_58,C_59] :
      ( '#skF_3'(A_57,B_58,C_59) = A_57
      | ~ r2_hidden(A_57,a_2_1_orders_2(B_58,C_59))
      | ~ m1_subset_1(C_59,k1_zfmisc_1(u1_struct_0(B_58)))
      | ~ l1_orders_2(B_58)
      | ~ v5_orders_2(B_58)
      | ~ v4_orders_2(B_58)
      | ~ v3_orders_2(B_58)
      | v2_struct_0(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_211,plain,
    ( '#skF_3'('#skF_6','#skF_5',k1_tarski('#skF_7')) = '#skF_6'
    | ~ m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_204,c_209])).

tff(c_220,plain,
    ( '#skF_3'('#skF_6','#skF_5',k1_tarski('#skF_7')) = '#skF_6'
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_119,c_211])).

tff(c_221,plain,(
    '#skF_3'('#skF_6','#skF_5',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_220])).

tff(c_696,plain,(
    ! [B_95,A_96,C_97,E_98] :
      ( r2_orders_2(B_95,'#skF_3'(A_96,B_95,C_97),E_98)
      | ~ r2_hidden(E_98,C_97)
      | ~ m1_subset_1(E_98,u1_struct_0(B_95))
      | ~ r2_hidden(A_96,a_2_1_orders_2(B_95,C_97))
      | ~ m1_subset_1(C_97,k1_zfmisc_1(u1_struct_0(B_95)))
      | ~ l1_orders_2(B_95)
      | ~ v5_orders_2(B_95)
      | ~ v4_orders_2(B_95)
      | ~ v3_orders_2(B_95)
      | v2_struct_0(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_700,plain,(
    ! [A_96,E_98] :
      ( r2_orders_2('#skF_5','#skF_3'(A_96,'#skF_5',k1_tarski('#skF_7')),E_98)
      | ~ r2_hidden(E_98,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_98,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_96,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_119,c_696])).

tff(c_710,plain,(
    ! [A_96,E_98] :
      ( r2_orders_2('#skF_5','#skF_3'(A_96,'#skF_5',k1_tarski('#skF_7')),E_98)
      | ~ r2_hidden(E_98,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_98,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_96,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_700])).

tff(c_724,plain,(
    ! [A_101,E_102] :
      ( r2_orders_2('#skF_5','#skF_3'(A_101,'#skF_5',k1_tarski('#skF_7')),E_102)
      | ~ r2_hidden(E_102,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_102,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_101,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_710])).

tff(c_736,plain,(
    ! [E_102] :
      ( r2_orders_2('#skF_5','#skF_6',E_102)
      | ~ r2_hidden(E_102,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_102,u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_6',a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_724])).

tff(c_743,plain,(
    ! [E_103] :
      ( r2_orders_2('#skF_5','#skF_6',E_103)
      | ~ r2_hidden(E_103,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_103,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_736])).

tff(c_758,plain,
    ( r2_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_4,c_743])).

tff(c_764,plain,(
    r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_758])).

tff(c_766,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_764])).

tff(c_768,plain,(
    ~ r2_hidden('#skF_6',k2_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_816,plain,(
    ~ r2_hidden('#skF_6',k2_orders_2('#skF_5',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_814,c_768])).

tff(c_886,plain,(
    ~ r2_hidden('#skF_6',a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_880,c_816])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_767,plain,(
    r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1005,plain,(
    ! [D_138,B_139,C_140] :
      ( r2_hidden('#skF_4'(D_138,B_139,C_140,D_138),C_140)
      | r2_hidden(D_138,a_2_1_orders_2(B_139,C_140))
      | ~ m1_subset_1(D_138,u1_struct_0(B_139))
      | ~ m1_subset_1(C_140,k1_zfmisc_1(u1_struct_0(B_139)))
      | ~ l1_orders_2(B_139)
      | ~ v5_orders_2(B_139)
      | ~ v4_orders_2(B_139)
      | ~ v3_orders_2(B_139)
      | v2_struct_0(B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1007,plain,(
    ! [D_138] :
      ( r2_hidden('#skF_4'(D_138,'#skF_5',k1_tarski('#skF_7'),D_138),k1_tarski('#skF_7'))
      | r2_hidden(D_138,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
      | ~ m1_subset_1(D_138,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_843,c_1005])).

tff(c_1015,plain,(
    ! [D_138] :
      ( r2_hidden('#skF_4'(D_138,'#skF_5',k1_tarski('#skF_7'),D_138),k1_tarski('#skF_7'))
      | r2_hidden(D_138,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
      | ~ m1_subset_1(D_138,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_1007])).

tff(c_1022,plain,(
    ! [D_141] :
      ( r2_hidden('#skF_4'(D_141,'#skF_5',k1_tarski('#skF_7'),D_141),k1_tarski('#skF_7'))
      | r2_hidden(D_141,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
      | ~ m1_subset_1(D_141,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1015])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1027,plain,(
    ! [D_142] :
      ( '#skF_4'(D_142,'#skF_5',k1_tarski('#skF_7'),D_142) = '#skF_7'
      | r2_hidden(D_142,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
      | ~ m1_subset_1(D_142,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1022,c_2])).

tff(c_1038,plain,
    ( '#skF_4'('#skF_6','#skF_5',k1_tarski('#skF_7'),'#skF_6') = '#skF_7'
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1027,c_886])).

tff(c_1052,plain,(
    '#skF_4'('#skF_6','#skF_5',k1_tarski('#skF_7'),'#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1038])).

tff(c_1093,plain,(
    ! [B_144,D_145,C_146] :
      ( ~ r2_orders_2(B_144,D_145,'#skF_4'(D_145,B_144,C_146,D_145))
      | r2_hidden(D_145,a_2_1_orders_2(B_144,C_146))
      | ~ m1_subset_1(D_145,u1_struct_0(B_144))
      | ~ m1_subset_1(C_146,k1_zfmisc_1(u1_struct_0(B_144)))
      | ~ l1_orders_2(B_144)
      | ~ v5_orders_2(B_144)
      | ~ v4_orders_2(B_144)
      | ~ v3_orders_2(B_144)
      | v2_struct_0(B_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1097,plain,
    ( ~ r2_orders_2('#skF_5','#skF_6','#skF_7')
    | r2_hidden('#skF_6',a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1052,c_1093])).

tff(c_1104,plain,
    ( r2_hidden('#skF_6',a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_843,c_40,c_767,c_1097])).

tff(c_1106,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_886,c_1104])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:11:59 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.30/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.54  
% 3.30/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.55  %$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 3.30/1.55  
% 3.30/1.55  %Foreground sorts:
% 3.30/1.55  
% 3.30/1.55  
% 3.30/1.55  %Background operators:
% 3.30/1.55  
% 3.30/1.55  
% 3.30/1.55  %Foreground operators:
% 3.30/1.55  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.30/1.55  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.30/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.30/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.30/1.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.30/1.55  tff('#skF_7', type, '#skF_7': $i).
% 3.30/1.55  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.30/1.55  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 3.30/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.30/1.55  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 3.30/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.30/1.55  tff('#skF_6', type, '#skF_6': $i).
% 3.30/1.55  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.30/1.55  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.30/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.30/1.55  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.30/1.55  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.30/1.55  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.30/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.30/1.55  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.30/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.30/1.55  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.30/1.55  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 3.30/1.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.30/1.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.30/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.30/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.30/1.55  
% 3.60/1.57  tff(f_125, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> r2_hidden(B, k2_orders_2(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_orders_2)).
% 3.60/1.57  tff(f_69, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.60/1.57  tff(f_103, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.60/1.57  tff(f_42, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.60/1.57  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.60/1.57  tff(f_58, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_orders_2)).
% 3.60/1.57  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.60/1.57  tff(f_96, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 3.60/1.57  tff(c_50, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.60/1.57  tff(c_48, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.60/1.57  tff(c_46, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.60/1.57  tff(c_44, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.60/1.57  tff(c_42, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.60/1.57  tff(c_22, plain, (![A_13]: (l1_struct_0(A_13) | ~l1_orders_2(A_13))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.60/1.57  tff(c_38, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.60/1.57  tff(c_791, plain, (![A_108, B_109]: (k6_domain_1(A_108, B_109)=k1_tarski(B_109) | ~m1_subset_1(B_109, A_108) | v1_xboole_0(A_108))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.60/1.57  tff(c_798, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')=k1_tarski('#skF_7') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_791])).
% 3.60/1.57  tff(c_800, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_798])).
% 3.60/1.57  tff(c_16, plain, (![A_7]: (~v1_xboole_0(u1_struct_0(A_7)) | ~l1_struct_0(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.60/1.57  tff(c_803, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_800, c_16])).
% 3.60/1.57  tff(c_806, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_50, c_803])).
% 3.60/1.57  tff(c_809, plain, (~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_22, c_806])).
% 3.60/1.57  tff(c_813, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_809])).
% 3.60/1.57  tff(c_815, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_798])).
% 3.60/1.57  tff(c_814, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_798])).
% 3.60/1.57  tff(c_827, plain, (![A_112, B_113]: (m1_subset_1(k6_domain_1(A_112, B_113), k1_zfmisc_1(A_112)) | ~m1_subset_1(B_113, A_112) | v1_xboole_0(A_112))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.60/1.57  tff(c_836, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_814, c_827])).
% 3.60/1.57  tff(c_842, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_836])).
% 3.60/1.57  tff(c_843, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_815, c_842])).
% 3.60/1.57  tff(c_866, plain, (![A_120, B_121]: (k2_orders_2(A_120, B_121)=a_2_1_orders_2(A_120, B_121) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_orders_2(A_120) | ~v5_orders_2(A_120) | ~v4_orders_2(A_120) | ~v3_orders_2(A_120) | v2_struct_0(A_120))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.60/1.57  tff(c_869, plain, (k2_orders_2('#skF_5', k1_tarski('#skF_7'))=a_2_1_orders_2('#skF_5', k1_tarski('#skF_7')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_843, c_866])).
% 3.60/1.57  tff(c_879, plain, (k2_orders_2('#skF_5', k1_tarski('#skF_7'))=a_2_1_orders_2('#skF_5', k1_tarski('#skF_7')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_869])).
% 3.60/1.57  tff(c_880, plain, (k2_orders_2('#skF_5', k1_tarski('#skF_7'))=a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_50, c_879])).
% 3.60/1.57  tff(c_58, plain, (r2_orders_2('#skF_5', '#skF_6', '#skF_7') | r2_hidden('#skF_6', k2_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.60/1.57  tff(c_61, plain, (r2_hidden('#skF_6', k2_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')))), inference(splitLeft, [status(thm)], [c_58])).
% 3.60/1.57  tff(c_52, plain, (~r2_hidden('#skF_6', k2_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7'))) | ~r2_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.60/1.57  tff(c_109, plain, (~r2_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_52])).
% 3.60/1.57  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.60/1.57  tff(c_78, plain, (![A_39, B_40]: (k6_domain_1(A_39, B_40)=k1_tarski(B_40) | ~m1_subset_1(B_40, A_39) | v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.60/1.57  tff(c_85, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')=k1_tarski('#skF_7') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_78])).
% 3.60/1.57  tff(c_92, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_85])).
% 3.60/1.57  tff(c_95, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_92, c_16])).
% 3.60/1.57  tff(c_98, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_50, c_95])).
% 3.60/1.57  tff(c_101, plain, (~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_22, c_98])).
% 3.60/1.57  tff(c_105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_101])).
% 3.60/1.57  tff(c_107, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_85])).
% 3.60/1.57  tff(c_106, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_85])).
% 3.60/1.57  tff(c_20, plain, (![A_11, B_12]: (m1_subset_1(k6_domain_1(A_11, B_12), k1_zfmisc_1(A_11)) | ~m1_subset_1(B_12, A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.60/1.57  tff(c_114, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_106, c_20])).
% 3.60/1.57  tff(c_118, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_114])).
% 3.60/1.57  tff(c_119, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_107, c_118])).
% 3.60/1.57  tff(c_180, plain, (![A_55, B_56]: (k2_orders_2(A_55, B_56)=a_2_1_orders_2(A_55, B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_orders_2(A_55) | ~v5_orders_2(A_55) | ~v4_orders_2(A_55) | ~v3_orders_2(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.60/1.57  tff(c_186, plain, (k2_orders_2('#skF_5', k1_tarski('#skF_7'))=a_2_1_orders_2('#skF_5', k1_tarski('#skF_7')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_119, c_180])).
% 3.60/1.57  tff(c_197, plain, (k2_orders_2('#skF_5', k1_tarski('#skF_7'))=a_2_1_orders_2('#skF_5', k1_tarski('#skF_7')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_186])).
% 3.60/1.57  tff(c_198, plain, (k2_orders_2('#skF_5', k1_tarski('#skF_7'))=a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_50, c_197])).
% 3.60/1.57  tff(c_110, plain, (r2_hidden('#skF_6', k2_orders_2('#skF_5', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_61])).
% 3.60/1.57  tff(c_204, plain, (r2_hidden('#skF_6', a_2_1_orders_2('#skF_5', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_198, c_110])).
% 3.60/1.57  tff(c_209, plain, (![A_57, B_58, C_59]: ('#skF_3'(A_57, B_58, C_59)=A_57 | ~r2_hidden(A_57, a_2_1_orders_2(B_58, C_59)) | ~m1_subset_1(C_59, k1_zfmisc_1(u1_struct_0(B_58))) | ~l1_orders_2(B_58) | ~v5_orders_2(B_58) | ~v4_orders_2(B_58) | ~v3_orders_2(B_58) | v2_struct_0(B_58))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.60/1.57  tff(c_211, plain, ('#skF_3'('#skF_6', '#skF_5', k1_tarski('#skF_7'))='#skF_6' | ~m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_204, c_209])).
% 3.60/1.57  tff(c_220, plain, ('#skF_3'('#skF_6', '#skF_5', k1_tarski('#skF_7'))='#skF_6' | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_119, c_211])).
% 3.60/1.57  tff(c_221, plain, ('#skF_3'('#skF_6', '#skF_5', k1_tarski('#skF_7'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_50, c_220])).
% 3.60/1.57  tff(c_696, plain, (![B_95, A_96, C_97, E_98]: (r2_orders_2(B_95, '#skF_3'(A_96, B_95, C_97), E_98) | ~r2_hidden(E_98, C_97) | ~m1_subset_1(E_98, u1_struct_0(B_95)) | ~r2_hidden(A_96, a_2_1_orders_2(B_95, C_97)) | ~m1_subset_1(C_97, k1_zfmisc_1(u1_struct_0(B_95))) | ~l1_orders_2(B_95) | ~v5_orders_2(B_95) | ~v4_orders_2(B_95) | ~v3_orders_2(B_95) | v2_struct_0(B_95))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.60/1.57  tff(c_700, plain, (![A_96, E_98]: (r2_orders_2('#skF_5', '#skF_3'(A_96, '#skF_5', k1_tarski('#skF_7')), E_98) | ~r2_hidden(E_98, k1_tarski('#skF_7')) | ~m1_subset_1(E_98, u1_struct_0('#skF_5')) | ~r2_hidden(A_96, a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_119, c_696])).
% 3.60/1.57  tff(c_710, plain, (![A_96, E_98]: (r2_orders_2('#skF_5', '#skF_3'(A_96, '#skF_5', k1_tarski('#skF_7')), E_98) | ~r2_hidden(E_98, k1_tarski('#skF_7')) | ~m1_subset_1(E_98, u1_struct_0('#skF_5')) | ~r2_hidden(A_96, a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_700])).
% 3.60/1.57  tff(c_724, plain, (![A_101, E_102]: (r2_orders_2('#skF_5', '#skF_3'(A_101, '#skF_5', k1_tarski('#skF_7')), E_102) | ~r2_hidden(E_102, k1_tarski('#skF_7')) | ~m1_subset_1(E_102, u1_struct_0('#skF_5')) | ~r2_hidden(A_101, a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_710])).
% 3.60/1.57  tff(c_736, plain, (![E_102]: (r2_orders_2('#skF_5', '#skF_6', E_102) | ~r2_hidden(E_102, k1_tarski('#skF_7')) | ~m1_subset_1(E_102, u1_struct_0('#skF_5')) | ~r2_hidden('#skF_6', a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_221, c_724])).
% 3.60/1.57  tff(c_743, plain, (![E_103]: (r2_orders_2('#skF_5', '#skF_6', E_103) | ~r2_hidden(E_103, k1_tarski('#skF_7')) | ~m1_subset_1(E_103, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_736])).
% 3.60/1.57  tff(c_758, plain, (r2_orders_2('#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_4, c_743])).
% 3.60/1.57  tff(c_764, plain, (r2_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_758])).
% 3.60/1.57  tff(c_766, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_764])).
% 3.60/1.57  tff(c_768, plain, (~r2_hidden('#skF_6', k2_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')))), inference(splitRight, [status(thm)], [c_58])).
% 3.60/1.57  tff(c_816, plain, (~r2_hidden('#skF_6', k2_orders_2('#skF_5', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_814, c_768])).
% 3.60/1.57  tff(c_886, plain, (~r2_hidden('#skF_6', a_2_1_orders_2('#skF_5', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_880, c_816])).
% 3.60/1.57  tff(c_40, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.60/1.57  tff(c_767, plain, (r2_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_58])).
% 3.60/1.57  tff(c_1005, plain, (![D_138, B_139, C_140]: (r2_hidden('#skF_4'(D_138, B_139, C_140, D_138), C_140) | r2_hidden(D_138, a_2_1_orders_2(B_139, C_140)) | ~m1_subset_1(D_138, u1_struct_0(B_139)) | ~m1_subset_1(C_140, k1_zfmisc_1(u1_struct_0(B_139))) | ~l1_orders_2(B_139) | ~v5_orders_2(B_139) | ~v4_orders_2(B_139) | ~v3_orders_2(B_139) | v2_struct_0(B_139))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.60/1.57  tff(c_1007, plain, (![D_138]: (r2_hidden('#skF_4'(D_138, '#skF_5', k1_tarski('#skF_7'), D_138), k1_tarski('#skF_7')) | r2_hidden(D_138, a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | ~m1_subset_1(D_138, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_843, c_1005])).
% 3.60/1.57  tff(c_1015, plain, (![D_138]: (r2_hidden('#skF_4'(D_138, '#skF_5', k1_tarski('#skF_7'), D_138), k1_tarski('#skF_7')) | r2_hidden(D_138, a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | ~m1_subset_1(D_138, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_1007])).
% 3.60/1.57  tff(c_1022, plain, (![D_141]: (r2_hidden('#skF_4'(D_141, '#skF_5', k1_tarski('#skF_7'), D_141), k1_tarski('#skF_7')) | r2_hidden(D_141, a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | ~m1_subset_1(D_141, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_50, c_1015])).
% 3.60/1.57  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.60/1.57  tff(c_1027, plain, (![D_142]: ('#skF_4'(D_142, '#skF_5', k1_tarski('#skF_7'), D_142)='#skF_7' | r2_hidden(D_142, a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | ~m1_subset_1(D_142, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_1022, c_2])).
% 3.60/1.57  tff(c_1038, plain, ('#skF_4'('#skF_6', '#skF_5', k1_tarski('#skF_7'), '#skF_6')='#skF_7' | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_1027, c_886])).
% 3.60/1.57  tff(c_1052, plain, ('#skF_4'('#skF_6', '#skF_5', k1_tarski('#skF_7'), '#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1038])).
% 3.60/1.57  tff(c_1093, plain, (![B_144, D_145, C_146]: (~r2_orders_2(B_144, D_145, '#skF_4'(D_145, B_144, C_146, D_145)) | r2_hidden(D_145, a_2_1_orders_2(B_144, C_146)) | ~m1_subset_1(D_145, u1_struct_0(B_144)) | ~m1_subset_1(C_146, k1_zfmisc_1(u1_struct_0(B_144))) | ~l1_orders_2(B_144) | ~v5_orders_2(B_144) | ~v4_orders_2(B_144) | ~v3_orders_2(B_144) | v2_struct_0(B_144))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.60/1.57  tff(c_1097, plain, (~r2_orders_2('#skF_5', '#skF_6', '#skF_7') | r2_hidden('#skF_6', a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1052, c_1093])).
% 3.60/1.57  tff(c_1104, plain, (r2_hidden('#skF_6', a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_843, c_40, c_767, c_1097])).
% 3.60/1.57  tff(c_1106, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_886, c_1104])).
% 3.60/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.57  
% 3.60/1.57  Inference rules
% 3.60/1.57  ----------------------
% 3.60/1.57  #Ref     : 0
% 3.60/1.57  #Sup     : 209
% 3.60/1.57  #Fact    : 0
% 3.60/1.57  #Define  : 0
% 3.60/1.57  #Split   : 13
% 3.60/1.57  #Chain   : 0
% 3.60/1.57  #Close   : 0
% 3.60/1.57  
% 3.60/1.57  Ordering : KBO
% 3.60/1.57  
% 3.60/1.57  Simplification rules
% 3.60/1.57  ----------------------
% 3.60/1.57  #Subsume      : 8
% 3.60/1.57  #Demod        : 312
% 3.60/1.57  #Tautology    : 102
% 3.60/1.57  #SimpNegUnit  : 67
% 3.60/1.57  #BackRed      : 4
% 3.60/1.57  
% 3.60/1.57  #Partial instantiations: 0
% 3.60/1.57  #Strategies tried      : 1
% 3.60/1.57  
% 3.60/1.57  Timing (in seconds)
% 3.60/1.57  ----------------------
% 3.60/1.57  Preprocessing        : 0.31
% 3.60/1.57  Parsing              : 0.15
% 3.60/1.57  CNF conversion       : 0.03
% 3.60/1.57  Main loop            : 0.45
% 3.60/1.57  Inferencing          : 0.16
% 3.60/1.57  Reduction            : 0.14
% 3.60/1.57  Demodulation         : 0.10
% 3.60/1.57  BG Simplification    : 0.03
% 3.60/1.57  Subsumption          : 0.08
% 3.60/1.57  Abstraction          : 0.03
% 3.60/1.57  MUC search           : 0.00
% 3.60/1.57  Cooper               : 0.00
% 3.60/1.57  Total                : 0.80
% 3.60/1.57  Index Insertion      : 0.00
% 3.60/1.57  Index Deletion       : 0.00
% 3.60/1.57  Index Matching       : 0.00
% 3.60/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
