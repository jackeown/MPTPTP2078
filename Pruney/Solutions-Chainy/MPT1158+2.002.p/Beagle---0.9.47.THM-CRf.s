%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:42 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 410 expanded)
%              Number of leaves         :   36 ( 165 expanded)
%              Depth                    :   18
%              Number of atoms          :  262 (1599 expanded)
%              Number of equality atoms :   27 (  90 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

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

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_132,negated_conjecture,(
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

tff(f_62,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_42,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_110,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v6_orders_2(k6_domain_1(u1_struct_0(A),B),A)
            & m1_subset_1(k6_domain_1(u1_struct_0(A),B),k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_orders_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_89,axiom,(
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

tff(c_52,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_50,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_48,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_46,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_44,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_40,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_20,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_orders_2(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_719,plain,(
    ! [A_104,B_105] :
      ( k6_domain_1(A_104,B_105) = k1_tarski(B_105)
      | ~ m1_subset_1(B_105,A_104)
      | v1_xboole_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_726,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_40,c_719])).

tff(c_729,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_726])).

tff(c_16,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(u1_struct_0(A_7))
      | ~ l1_struct_0(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_732,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_729,c_16])).

tff(c_735,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_732])).

tff(c_738,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_735])).

tff(c_742,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_738])).

tff(c_743,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_726])).

tff(c_808,plain,(
    ! [A_120,B_121] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_120),B_121),k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ m1_subset_1(B_121,u1_struct_0(A_120))
      | ~ l1_orders_2(A_120)
      | ~ v3_orders_2(A_120)
      | v2_struct_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_817,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_743,c_808])).

tff(c_823,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_40,c_817])).

tff(c_824,plain,(
    m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_823])).

tff(c_836,plain,(
    ! [A_122,B_123] :
      ( k2_orders_2(A_122,B_123) = a_2_1_orders_2(A_122,B_123)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_orders_2(A_122)
      | ~ v5_orders_2(A_122)
      | ~ v4_orders_2(A_122)
      | ~ v3_orders_2(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_839,plain,
    ( k2_orders_2('#skF_5',k1_tarski('#skF_7')) = a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_824,c_836])).

tff(c_848,plain,
    ( k2_orders_2('#skF_5',k1_tarski('#skF_7')) = a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_839])).

tff(c_849,plain,(
    k2_orders_2('#skF_5',k1_tarski('#skF_7')) = a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_848])).

tff(c_54,plain,
    ( ~ r2_hidden('#skF_6',k2_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7')))
    | ~ r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_63,plain,(
    ~ r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_80,plain,(
    ! [A_40,B_41] :
      ( k6_domain_1(A_40,B_41) = k1_tarski(B_41)
      | ~ m1_subset_1(B_41,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_87,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_40,c_80])).

tff(c_90,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_93,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_16])).

tff(c_96,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_93])).

tff(c_99,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_96])).

tff(c_103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_99])).

tff(c_104,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_167,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_56),B_57),k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ m1_subset_1(B_57,u1_struct_0(A_56))
      | ~ l1_orders_2(A_56)
      | ~ v3_orders_2(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_176,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_167])).

tff(c_182,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_40,c_176])).

tff(c_183,plain,(
    m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_182])).

tff(c_192,plain,(
    ! [A_58,B_59] :
      ( k2_orders_2(A_58,B_59) = a_2_1_orders_2(A_58,B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_orders_2(A_58)
      | ~ v5_orders_2(A_58)
      | ~ v4_orders_2(A_58)
      | ~ v3_orders_2(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_195,plain,
    ( k2_orders_2('#skF_5',k1_tarski('#skF_7')) = a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_183,c_192])).

tff(c_204,plain,
    ( k2_orders_2('#skF_5',k1_tarski('#skF_7')) = a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_195])).

tff(c_205,plain,(
    k2_orders_2('#skF_5',k1_tarski('#skF_7')) = a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_204])).

tff(c_60,plain,
    ( r2_orders_2('#skF_5','#skF_6','#skF_7')
    | r2_hidden('#skF_6',k2_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_106,plain,(
    r2_hidden('#skF_6',k2_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_60])).

tff(c_107,plain,(
    r2_hidden('#skF_6',k2_orders_2('#skF_5',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_106])).

tff(c_211,plain,(
    r2_hidden('#skF_6',a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_107])).

tff(c_222,plain,(
    ! [A_60,B_61,C_62] :
      ( '#skF_3'(A_60,B_61,C_62) = A_60
      | ~ r2_hidden(A_60,a_2_1_orders_2(B_61,C_62))
      | ~ m1_subset_1(C_62,k1_zfmisc_1(u1_struct_0(B_61)))
      | ~ l1_orders_2(B_61)
      | ~ v5_orders_2(B_61)
      | ~ v4_orders_2(B_61)
      | ~ v3_orders_2(B_61)
      | v2_struct_0(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_224,plain,
    ( '#skF_3'('#skF_6','#skF_5',k1_tarski('#skF_7')) = '#skF_6'
    | ~ m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_211,c_222])).

tff(c_233,plain,
    ( '#skF_3'('#skF_6','#skF_5',k1_tarski('#skF_7')) = '#skF_6'
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_183,c_224])).

tff(c_234,plain,(
    '#skF_3'('#skF_6','#skF_5',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_233])).

tff(c_641,plain,(
    ! [B_93,A_94,C_95,E_96] :
      ( r2_orders_2(B_93,'#skF_3'(A_94,B_93,C_95),E_96)
      | ~ r2_hidden(E_96,C_95)
      | ~ m1_subset_1(E_96,u1_struct_0(B_93))
      | ~ r2_hidden(A_94,a_2_1_orders_2(B_93,C_95))
      | ~ m1_subset_1(C_95,k1_zfmisc_1(u1_struct_0(B_93)))
      | ~ l1_orders_2(B_93)
      | ~ v5_orders_2(B_93)
      | ~ v4_orders_2(B_93)
      | ~ v3_orders_2(B_93)
      | v2_struct_0(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_643,plain,(
    ! [A_94,E_96] :
      ( r2_orders_2('#skF_5','#skF_3'(A_94,'#skF_5',k1_tarski('#skF_7')),E_96)
      | ~ r2_hidden(E_96,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_96,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_94,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_183,c_641])).

tff(c_650,plain,(
    ! [A_94,E_96] :
      ( r2_orders_2('#skF_5','#skF_3'(A_94,'#skF_5',k1_tarski('#skF_7')),E_96)
      | ~ r2_hidden(E_96,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_96,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_94,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_643])).

tff(c_657,plain,(
    ! [A_97,E_98] :
      ( r2_orders_2('#skF_5','#skF_3'(A_97,'#skF_5',k1_tarski('#skF_7')),E_98)
      | ~ r2_hidden(E_98,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_98,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_97,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_650])).

tff(c_669,plain,(
    ! [E_98] :
      ( r2_orders_2('#skF_5','#skF_6',E_98)
      | ~ r2_hidden(E_98,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_98,u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_6',a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_657])).

tff(c_676,plain,(
    ! [E_99] :
      ( r2_orders_2('#skF_5','#skF_6',E_99)
      | ~ r2_hidden(E_99,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_99,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_669])).

tff(c_691,plain,
    ( r2_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_4,c_676])).

tff(c_697,plain,(
    r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_691])).

tff(c_699,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_697])).

tff(c_700,plain,(
    ~ r2_hidden('#skF_6',k2_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_749,plain,(
    ~ r2_hidden('#skF_6',k2_orders_2('#skF_5',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_743,c_700])).

tff(c_855,plain,(
    ~ r2_hidden('#skF_6',a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_849,c_749])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_701,plain,(
    r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_899,plain,(
    ! [D_132,B_133,C_134] :
      ( r2_hidden('#skF_4'(D_132,B_133,C_134,D_132),C_134)
      | r2_hidden(D_132,a_2_1_orders_2(B_133,C_134))
      | ~ m1_subset_1(D_132,u1_struct_0(B_133))
      | ~ m1_subset_1(C_134,k1_zfmisc_1(u1_struct_0(B_133)))
      | ~ l1_orders_2(B_133)
      | ~ v5_orders_2(B_133)
      | ~ v4_orders_2(B_133)
      | ~ v3_orders_2(B_133)
      | v2_struct_0(B_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_901,plain,(
    ! [D_132] :
      ( r2_hidden('#skF_4'(D_132,'#skF_5',k1_tarski('#skF_7'),D_132),k1_tarski('#skF_7'))
      | r2_hidden(D_132,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
      | ~ m1_subset_1(D_132,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_824,c_899])).

tff(c_908,plain,(
    ! [D_132] :
      ( r2_hidden('#skF_4'(D_132,'#skF_5',k1_tarski('#skF_7'),D_132),k1_tarski('#skF_7'))
      | r2_hidden(D_132,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
      | ~ m1_subset_1(D_132,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_901])).

tff(c_915,plain,(
    ! [D_135] :
      ( r2_hidden('#skF_4'(D_135,'#skF_5',k1_tarski('#skF_7'),D_135),k1_tarski('#skF_7'))
      | r2_hidden(D_135,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
      | ~ m1_subset_1(D_135,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_908])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_920,plain,(
    ! [D_136] :
      ( '#skF_4'(D_136,'#skF_5',k1_tarski('#skF_7'),D_136) = '#skF_7'
      | r2_hidden(D_136,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
      | ~ m1_subset_1(D_136,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_915,c_2])).

tff(c_931,plain,
    ( '#skF_4'('#skF_6','#skF_5',k1_tarski('#skF_7'),'#skF_6') = '#skF_7'
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_920,c_855])).

tff(c_945,plain,(
    '#skF_4'('#skF_6','#skF_5',k1_tarski('#skF_7'),'#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_931])).

tff(c_975,plain,(
    ! [B_138,D_139,C_140] :
      ( ~ r2_orders_2(B_138,D_139,'#skF_4'(D_139,B_138,C_140,D_139))
      | r2_hidden(D_139,a_2_1_orders_2(B_138,C_140))
      | ~ m1_subset_1(D_139,u1_struct_0(B_138))
      | ~ m1_subset_1(C_140,k1_zfmisc_1(u1_struct_0(B_138)))
      | ~ l1_orders_2(B_138)
      | ~ v5_orders_2(B_138)
      | ~ v4_orders_2(B_138)
      | ~ v3_orders_2(B_138)
      | v2_struct_0(B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_977,plain,
    ( ~ r2_orders_2('#skF_5','#skF_6','#skF_7')
    | r2_hidden('#skF_6',a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_945,c_975])).

tff(c_981,plain,
    ( r2_hidden('#skF_6',a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_824,c_42,c_701,c_977])).

tff(c_983,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_855,c_981])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:05:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.33/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.51  
% 3.33/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.52  %$ r2_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 3.33/1.52  
% 3.33/1.52  %Foreground sorts:
% 3.33/1.52  
% 3.33/1.52  
% 3.33/1.52  %Background operators:
% 3.33/1.52  
% 3.33/1.52  
% 3.33/1.52  %Foreground operators:
% 3.33/1.52  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.33/1.52  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.33/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.33/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.33/1.52  tff('#skF_7', type, '#skF_7': $i).
% 3.33/1.52  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.33/1.52  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 3.33/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.33/1.52  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 3.33/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.33/1.52  tff('#skF_6', type, '#skF_6': $i).
% 3.33/1.52  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.33/1.52  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.33/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.33/1.52  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.33/1.52  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.33/1.52  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.33/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.52  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.33/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.33/1.52  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 3.33/1.52  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 3.33/1.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.33/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.33/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.33/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.33/1.52  
% 3.57/1.54  tff(f_132, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> r2_hidden(B, k2_orders_2(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_orders_2)).
% 3.57/1.54  tff(f_62, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.57/1.54  tff(f_96, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.57/1.54  tff(f_42, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.57/1.54  tff(f_110, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v6_orders_2(k6_domain_1(u1_struct_0(A), B), A) & m1_subset_1(k6_domain_1(u1_struct_0(A), B), k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_orders_2)).
% 3.57/1.54  tff(f_58, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_orders_2)).
% 3.57/1.54  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.57/1.54  tff(f_89, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 3.57/1.54  tff(c_52, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.57/1.54  tff(c_50, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.57/1.54  tff(c_48, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.57/1.54  tff(c_46, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.57/1.54  tff(c_44, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.57/1.54  tff(c_40, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.57/1.54  tff(c_20, plain, (![A_11]: (l1_struct_0(A_11) | ~l1_orders_2(A_11))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.57/1.54  tff(c_719, plain, (![A_104, B_105]: (k6_domain_1(A_104, B_105)=k1_tarski(B_105) | ~m1_subset_1(B_105, A_104) | v1_xboole_0(A_104))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.57/1.54  tff(c_726, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')=k1_tarski('#skF_7') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_719])).
% 3.57/1.54  tff(c_729, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_726])).
% 3.57/1.54  tff(c_16, plain, (![A_7]: (~v1_xboole_0(u1_struct_0(A_7)) | ~l1_struct_0(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.57/1.54  tff(c_732, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_729, c_16])).
% 3.57/1.54  tff(c_735, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_52, c_732])).
% 3.57/1.54  tff(c_738, plain, (~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_20, c_735])).
% 3.57/1.54  tff(c_742, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_738])).
% 3.57/1.54  tff(c_743, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_726])).
% 3.57/1.54  tff(c_808, plain, (![A_120, B_121]: (m1_subset_1(k6_domain_1(u1_struct_0(A_120), B_121), k1_zfmisc_1(u1_struct_0(A_120))) | ~m1_subset_1(B_121, u1_struct_0(A_120)) | ~l1_orders_2(A_120) | ~v3_orders_2(A_120) | v2_struct_0(A_120))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.57/1.54  tff(c_817, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_743, c_808])).
% 3.57/1.54  tff(c_823, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_40, c_817])).
% 3.57/1.54  tff(c_824, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_52, c_823])).
% 3.57/1.54  tff(c_836, plain, (![A_122, B_123]: (k2_orders_2(A_122, B_123)=a_2_1_orders_2(A_122, B_123) | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_orders_2(A_122) | ~v5_orders_2(A_122) | ~v4_orders_2(A_122) | ~v3_orders_2(A_122) | v2_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.57/1.54  tff(c_839, plain, (k2_orders_2('#skF_5', k1_tarski('#skF_7'))=a_2_1_orders_2('#skF_5', k1_tarski('#skF_7')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_824, c_836])).
% 3.57/1.54  tff(c_848, plain, (k2_orders_2('#skF_5', k1_tarski('#skF_7'))=a_2_1_orders_2('#skF_5', k1_tarski('#skF_7')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_839])).
% 3.57/1.54  tff(c_849, plain, (k2_orders_2('#skF_5', k1_tarski('#skF_7'))=a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_52, c_848])).
% 3.57/1.54  tff(c_54, plain, (~r2_hidden('#skF_6', k2_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7'))) | ~r2_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.57/1.54  tff(c_63, plain, (~r2_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_54])).
% 3.57/1.54  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.57/1.54  tff(c_80, plain, (![A_40, B_41]: (k6_domain_1(A_40, B_41)=k1_tarski(B_41) | ~m1_subset_1(B_41, A_40) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.57/1.54  tff(c_87, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')=k1_tarski('#skF_7') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_80])).
% 3.57/1.54  tff(c_90, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_87])).
% 3.57/1.54  tff(c_93, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_90, c_16])).
% 3.57/1.54  tff(c_96, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_52, c_93])).
% 3.57/1.54  tff(c_99, plain, (~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_20, c_96])).
% 3.57/1.54  tff(c_103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_99])).
% 3.57/1.54  tff(c_104, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_87])).
% 3.57/1.54  tff(c_167, plain, (![A_56, B_57]: (m1_subset_1(k6_domain_1(u1_struct_0(A_56), B_57), k1_zfmisc_1(u1_struct_0(A_56))) | ~m1_subset_1(B_57, u1_struct_0(A_56)) | ~l1_orders_2(A_56) | ~v3_orders_2(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.57/1.54  tff(c_176, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_104, c_167])).
% 3.57/1.54  tff(c_182, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_40, c_176])).
% 3.57/1.54  tff(c_183, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_52, c_182])).
% 3.57/1.54  tff(c_192, plain, (![A_58, B_59]: (k2_orders_2(A_58, B_59)=a_2_1_orders_2(A_58, B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_orders_2(A_58) | ~v5_orders_2(A_58) | ~v4_orders_2(A_58) | ~v3_orders_2(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.57/1.54  tff(c_195, plain, (k2_orders_2('#skF_5', k1_tarski('#skF_7'))=a_2_1_orders_2('#skF_5', k1_tarski('#skF_7')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_183, c_192])).
% 3.57/1.54  tff(c_204, plain, (k2_orders_2('#skF_5', k1_tarski('#skF_7'))=a_2_1_orders_2('#skF_5', k1_tarski('#skF_7')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_195])).
% 3.57/1.54  tff(c_205, plain, (k2_orders_2('#skF_5', k1_tarski('#skF_7'))=a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_52, c_204])).
% 3.57/1.54  tff(c_60, plain, (r2_orders_2('#skF_5', '#skF_6', '#skF_7') | r2_hidden('#skF_6', k2_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.57/1.54  tff(c_106, plain, (r2_hidden('#skF_6', k2_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_63, c_60])).
% 3.57/1.54  tff(c_107, plain, (r2_hidden('#skF_6', k2_orders_2('#skF_5', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_106])).
% 3.57/1.54  tff(c_211, plain, (r2_hidden('#skF_6', a_2_1_orders_2('#skF_5', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_107])).
% 3.57/1.54  tff(c_222, plain, (![A_60, B_61, C_62]: ('#skF_3'(A_60, B_61, C_62)=A_60 | ~r2_hidden(A_60, a_2_1_orders_2(B_61, C_62)) | ~m1_subset_1(C_62, k1_zfmisc_1(u1_struct_0(B_61))) | ~l1_orders_2(B_61) | ~v5_orders_2(B_61) | ~v4_orders_2(B_61) | ~v3_orders_2(B_61) | v2_struct_0(B_61))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.57/1.54  tff(c_224, plain, ('#skF_3'('#skF_6', '#skF_5', k1_tarski('#skF_7'))='#skF_6' | ~m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_211, c_222])).
% 3.57/1.54  tff(c_233, plain, ('#skF_3'('#skF_6', '#skF_5', k1_tarski('#skF_7'))='#skF_6' | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_183, c_224])).
% 3.57/1.54  tff(c_234, plain, ('#skF_3'('#skF_6', '#skF_5', k1_tarski('#skF_7'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_52, c_233])).
% 3.57/1.54  tff(c_641, plain, (![B_93, A_94, C_95, E_96]: (r2_orders_2(B_93, '#skF_3'(A_94, B_93, C_95), E_96) | ~r2_hidden(E_96, C_95) | ~m1_subset_1(E_96, u1_struct_0(B_93)) | ~r2_hidden(A_94, a_2_1_orders_2(B_93, C_95)) | ~m1_subset_1(C_95, k1_zfmisc_1(u1_struct_0(B_93))) | ~l1_orders_2(B_93) | ~v5_orders_2(B_93) | ~v4_orders_2(B_93) | ~v3_orders_2(B_93) | v2_struct_0(B_93))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.57/1.54  tff(c_643, plain, (![A_94, E_96]: (r2_orders_2('#skF_5', '#skF_3'(A_94, '#skF_5', k1_tarski('#skF_7')), E_96) | ~r2_hidden(E_96, k1_tarski('#skF_7')) | ~m1_subset_1(E_96, u1_struct_0('#skF_5')) | ~r2_hidden(A_94, a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_183, c_641])).
% 3.57/1.54  tff(c_650, plain, (![A_94, E_96]: (r2_orders_2('#skF_5', '#skF_3'(A_94, '#skF_5', k1_tarski('#skF_7')), E_96) | ~r2_hidden(E_96, k1_tarski('#skF_7')) | ~m1_subset_1(E_96, u1_struct_0('#skF_5')) | ~r2_hidden(A_94, a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_643])).
% 3.57/1.54  tff(c_657, plain, (![A_97, E_98]: (r2_orders_2('#skF_5', '#skF_3'(A_97, '#skF_5', k1_tarski('#skF_7')), E_98) | ~r2_hidden(E_98, k1_tarski('#skF_7')) | ~m1_subset_1(E_98, u1_struct_0('#skF_5')) | ~r2_hidden(A_97, a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_650])).
% 3.57/1.54  tff(c_669, plain, (![E_98]: (r2_orders_2('#skF_5', '#skF_6', E_98) | ~r2_hidden(E_98, k1_tarski('#skF_7')) | ~m1_subset_1(E_98, u1_struct_0('#skF_5')) | ~r2_hidden('#skF_6', a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_234, c_657])).
% 3.57/1.54  tff(c_676, plain, (![E_99]: (r2_orders_2('#skF_5', '#skF_6', E_99) | ~r2_hidden(E_99, k1_tarski('#skF_7')) | ~m1_subset_1(E_99, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_211, c_669])).
% 3.57/1.54  tff(c_691, plain, (r2_orders_2('#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_4, c_676])).
% 3.57/1.54  tff(c_697, plain, (r2_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_691])).
% 3.57/1.54  tff(c_699, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_697])).
% 3.57/1.54  tff(c_700, plain, (~r2_hidden('#skF_6', k2_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')))), inference(splitRight, [status(thm)], [c_54])).
% 3.57/1.54  tff(c_749, plain, (~r2_hidden('#skF_6', k2_orders_2('#skF_5', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_743, c_700])).
% 3.57/1.54  tff(c_855, plain, (~r2_hidden('#skF_6', a_2_1_orders_2('#skF_5', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_849, c_749])).
% 3.57/1.54  tff(c_42, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.57/1.54  tff(c_701, plain, (r2_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_54])).
% 3.57/1.54  tff(c_899, plain, (![D_132, B_133, C_134]: (r2_hidden('#skF_4'(D_132, B_133, C_134, D_132), C_134) | r2_hidden(D_132, a_2_1_orders_2(B_133, C_134)) | ~m1_subset_1(D_132, u1_struct_0(B_133)) | ~m1_subset_1(C_134, k1_zfmisc_1(u1_struct_0(B_133))) | ~l1_orders_2(B_133) | ~v5_orders_2(B_133) | ~v4_orders_2(B_133) | ~v3_orders_2(B_133) | v2_struct_0(B_133))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.57/1.54  tff(c_901, plain, (![D_132]: (r2_hidden('#skF_4'(D_132, '#skF_5', k1_tarski('#skF_7'), D_132), k1_tarski('#skF_7')) | r2_hidden(D_132, a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | ~m1_subset_1(D_132, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_824, c_899])).
% 3.57/1.54  tff(c_908, plain, (![D_132]: (r2_hidden('#skF_4'(D_132, '#skF_5', k1_tarski('#skF_7'), D_132), k1_tarski('#skF_7')) | r2_hidden(D_132, a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | ~m1_subset_1(D_132, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_901])).
% 3.57/1.54  tff(c_915, plain, (![D_135]: (r2_hidden('#skF_4'(D_135, '#skF_5', k1_tarski('#skF_7'), D_135), k1_tarski('#skF_7')) | r2_hidden(D_135, a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | ~m1_subset_1(D_135, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_52, c_908])).
% 3.57/1.54  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.57/1.54  tff(c_920, plain, (![D_136]: ('#skF_4'(D_136, '#skF_5', k1_tarski('#skF_7'), D_136)='#skF_7' | r2_hidden(D_136, a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | ~m1_subset_1(D_136, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_915, c_2])).
% 3.57/1.54  tff(c_931, plain, ('#skF_4'('#skF_6', '#skF_5', k1_tarski('#skF_7'), '#skF_6')='#skF_7' | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_920, c_855])).
% 3.57/1.54  tff(c_945, plain, ('#skF_4'('#skF_6', '#skF_5', k1_tarski('#skF_7'), '#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_931])).
% 3.57/1.54  tff(c_975, plain, (![B_138, D_139, C_140]: (~r2_orders_2(B_138, D_139, '#skF_4'(D_139, B_138, C_140, D_139)) | r2_hidden(D_139, a_2_1_orders_2(B_138, C_140)) | ~m1_subset_1(D_139, u1_struct_0(B_138)) | ~m1_subset_1(C_140, k1_zfmisc_1(u1_struct_0(B_138))) | ~l1_orders_2(B_138) | ~v5_orders_2(B_138) | ~v4_orders_2(B_138) | ~v3_orders_2(B_138) | v2_struct_0(B_138))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.57/1.54  tff(c_977, plain, (~r2_orders_2('#skF_5', '#skF_6', '#skF_7') | r2_hidden('#skF_6', a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_945, c_975])).
% 3.57/1.54  tff(c_981, plain, (r2_hidden('#skF_6', a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_824, c_42, c_701, c_977])).
% 3.57/1.54  tff(c_983, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_855, c_981])).
% 3.57/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.54  
% 3.57/1.54  Inference rules
% 3.57/1.54  ----------------------
% 3.57/1.54  #Ref     : 0
% 3.57/1.54  #Sup     : 180
% 3.57/1.54  #Fact    : 0
% 3.57/1.54  #Define  : 0
% 3.57/1.54  #Split   : 14
% 3.57/1.54  #Chain   : 0
% 3.57/1.54  #Close   : 0
% 3.57/1.54  
% 3.57/1.54  Ordering : KBO
% 3.57/1.54  
% 3.57/1.54  Simplification rules
% 3.57/1.54  ----------------------
% 3.57/1.54  #Subsume      : 7
% 3.57/1.54  #Demod        : 293
% 3.57/1.54  #Tautology    : 87
% 3.57/1.54  #SimpNegUnit  : 62
% 3.57/1.54  #BackRed      : 4
% 3.57/1.54  
% 3.57/1.54  #Partial instantiations: 0
% 3.57/1.54  #Strategies tried      : 1
% 3.57/1.54  
% 3.57/1.54  Timing (in seconds)
% 3.57/1.54  ----------------------
% 3.57/1.54  Preprocessing        : 0.34
% 3.57/1.54  Parsing              : 0.18
% 3.57/1.54  CNF conversion       : 0.02
% 3.57/1.54  Main loop            : 0.42
% 3.57/1.54  Inferencing          : 0.15
% 3.57/1.54  Reduction            : 0.14
% 3.57/1.54  Demodulation         : 0.09
% 3.57/1.54  BG Simplification    : 0.02
% 3.57/1.54  Subsumption          : 0.07
% 3.57/1.54  Abstraction          : 0.03
% 3.57/1.54  MUC search           : 0.00
% 3.57/1.54  Cooper               : 0.00
% 3.57/1.54  Total                : 0.80
% 3.57/1.54  Index Insertion      : 0.00
% 3.57/1.54  Index Deletion       : 0.00
% 3.57/1.54  Index Matching       : 0.00
% 3.57/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
