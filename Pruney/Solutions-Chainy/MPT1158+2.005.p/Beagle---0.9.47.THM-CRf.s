%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:42 EST 2020

% Result     : Theorem 7.13s
% Output     : CNFRefutation 7.24s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 425 expanded)
%              Number of leaves         :   36 ( 161 expanded)
%              Depth                    :   18
%              Number of atoms          :  262 (1493 expanded)
%              Number of equality atoms :   34 ( 131 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_127,negated_conjecture,(
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

tff(f_71,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_44,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_98,axiom,(
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

tff(c_56,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_54,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_52,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_50,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_48,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_28,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_orders_2(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_44,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_5502,plain,(
    ! [A_6758,B_6759] :
      ( k6_domain_1(A_6758,B_6759) = k1_tarski(B_6759)
      | ~ m1_subset_1(B_6759,A_6758)
      | v1_xboole_0(A_6758) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_5509,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_44,c_5502])).

tff(c_5511,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_5509])).

tff(c_22,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(u1_struct_0(A_8))
      | ~ l1_struct_0(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_5514,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_5511,c_22])).

tff(c_5517,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_5514])).

tff(c_5520,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_5517])).

tff(c_5524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_5520])).

tff(c_5526,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_5509])).

tff(c_5525,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_5509])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(k6_domain_1(A_12,B_13),k1_zfmisc_1(A_12))
      | ~ m1_subset_1(B_13,A_12)
      | v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_5536,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5525,c_26])).

tff(c_5540,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_5536])).

tff(c_5541,plain,(
    m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_5526,c_5540])).

tff(c_6927,plain,(
    ! [A_9740,B_9741] :
      ( k2_orders_2(A_9740,B_9741) = a_2_1_orders_2(A_9740,B_9741)
      | ~ m1_subset_1(B_9741,k1_zfmisc_1(u1_struct_0(A_9740)))
      | ~ l1_orders_2(A_9740)
      | ~ v5_orders_2(A_9740)
      | ~ v4_orders_2(A_9740)
      | ~ v3_orders_2(A_9740)
      | v2_struct_0(A_9740) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6939,plain,
    ( k2_orders_2('#skF_5',k1_tarski('#skF_7')) = a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_5541,c_6927])).

tff(c_6950,plain,
    ( k2_orders_2('#skF_5',k1_tarski('#skF_7')) = a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_6939])).

tff(c_6951,plain,(
    k2_orders_2('#skF_5',k1_tarski('#skF_7')) = a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_6950])).

tff(c_107,plain,(
    ! [A_47,B_48] :
      ( k6_domain_1(A_47,B_48) = k1_tarski(B_48)
      | ~ m1_subset_1(B_48,A_47)
      | v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_114,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_44,c_107])).

tff(c_116,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_121,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_116,c_22])).

tff(c_124,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_121])).

tff(c_127,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_124])).

tff(c_131,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_127])).

tff(c_132,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_64,plain,
    ( r2_orders_2('#skF_5','#skF_6','#skF_7')
    | r2_hidden('#skF_6',k2_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_67,plain,(
    r2_hidden('#skF_6',k2_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7'))) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_134,plain,(
    r2_hidden('#skF_6',k2_orders_2('#skF_5',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_67])).

tff(c_58,plain,
    ( ~ r2_hidden('#skF_6',k2_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7')))
    | ~ r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_170,plain,(
    ~ r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_132,c_58])).

tff(c_68,plain,(
    ! [A_37] : k2_tarski(A_37,A_37) = k1_tarski(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_6,plain,(
    ! [D_6,B_2] : r2_hidden(D_6,k2_tarski(D_6,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_74,plain,(
    ! [A_37] : r2_hidden(A_37,k1_tarski(A_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_6])).

tff(c_133,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_139,plain,(
    ! [A_49,B_50] :
      ( m1_subset_1(k6_domain_1(A_49,B_50),k1_zfmisc_1(A_49))
      | ~ m1_subset_1(B_50,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_145,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_139])).

tff(c_148,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_145])).

tff(c_149,plain,(
    m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_148])).

tff(c_2101,plain,(
    ! [A_3592,B_3593] :
      ( k2_orders_2(A_3592,B_3593) = a_2_1_orders_2(A_3592,B_3593)
      | ~ m1_subset_1(B_3593,k1_zfmisc_1(u1_struct_0(A_3592)))
      | ~ l1_orders_2(A_3592)
      | ~ v5_orders_2(A_3592)
      | ~ v4_orders_2(A_3592)
      | ~ v3_orders_2(A_3592)
      | v2_struct_0(A_3592) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2113,plain,
    ( k2_orders_2('#skF_5',k1_tarski('#skF_7')) = a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_149,c_2101])).

tff(c_2124,plain,
    ( k2_orders_2('#skF_5',k1_tarski('#skF_7')) = a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_2113])).

tff(c_2125,plain,(
    k2_orders_2('#skF_5',k1_tarski('#skF_7')) = a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2124])).

tff(c_2180,plain,(
    r2_hidden('#skF_6',a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2125,c_134])).

tff(c_2495,plain,(
    ! [A_4029,B_4030,C_4031] :
      ( '#skF_3'(A_4029,B_4030,C_4031) = A_4029
      | ~ r2_hidden(A_4029,a_2_1_orders_2(B_4030,C_4031))
      | ~ m1_subset_1(C_4031,k1_zfmisc_1(u1_struct_0(B_4030)))
      | ~ l1_orders_2(B_4030)
      | ~ v5_orders_2(B_4030)
      | ~ v4_orders_2(B_4030)
      | ~ v3_orders_2(B_4030)
      | v2_struct_0(B_4030) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2497,plain,
    ( '#skF_3'('#skF_6','#skF_5',k1_tarski('#skF_7')) = '#skF_6'
    | ~ m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_2180,c_2495])).

tff(c_2506,plain,
    ( '#skF_3'('#skF_6','#skF_5',k1_tarski('#skF_7')) = '#skF_6'
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_149,c_2497])).

tff(c_2507,plain,(
    '#skF_3'('#skF_6','#skF_5',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2506])).

tff(c_4457,plain,(
    ! [B_6082,A_6083,C_6084,E_6085] :
      ( r2_orders_2(B_6082,'#skF_3'(A_6083,B_6082,C_6084),E_6085)
      | ~ r2_hidden(E_6085,C_6084)
      | ~ m1_subset_1(E_6085,u1_struct_0(B_6082))
      | ~ r2_hidden(A_6083,a_2_1_orders_2(B_6082,C_6084))
      | ~ m1_subset_1(C_6084,k1_zfmisc_1(u1_struct_0(B_6082)))
      | ~ l1_orders_2(B_6082)
      | ~ v5_orders_2(B_6082)
      | ~ v4_orders_2(B_6082)
      | ~ v3_orders_2(B_6082)
      | v2_struct_0(B_6082) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4467,plain,(
    ! [A_6083,E_6085] :
      ( r2_orders_2('#skF_5','#skF_3'(A_6083,'#skF_5',k1_tarski('#skF_7')),E_6085)
      | ~ r2_hidden(E_6085,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_6085,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_6083,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_149,c_4457])).

tff(c_4477,plain,(
    ! [A_6083,E_6085] :
      ( r2_orders_2('#skF_5','#skF_3'(A_6083,'#skF_5',k1_tarski('#skF_7')),E_6085)
      | ~ r2_hidden(E_6085,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_6085,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_6083,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_4467])).

tff(c_5388,plain,(
    ! [A_6601,E_6602] :
      ( r2_orders_2('#skF_5','#skF_3'(A_6601,'#skF_5',k1_tarski('#skF_7')),E_6602)
      | ~ r2_hidden(E_6602,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_6602,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_6601,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_4477])).

tff(c_5394,plain,(
    ! [E_6602] :
      ( r2_orders_2('#skF_5','#skF_6',E_6602)
      | ~ r2_hidden(E_6602,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_6602,u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_6',a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2507,c_5388])).

tff(c_5436,plain,(
    ! [E_6675] :
      ( r2_orders_2('#skF_5','#skF_6',E_6675)
      | ~ r2_hidden(E_6675,k1_tarski('#skF_7'))
      | ~ m1_subset_1(E_6675,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2180,c_5394])).

tff(c_5451,plain,
    ( r2_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_74,c_5436])).

tff(c_5456,plain,(
    r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_5451])).

tff(c_5458,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_5456])).

tff(c_5460,plain,(
    ~ r2_hidden('#skF_6',k2_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_5532,plain,(
    ~ r2_hidden('#skF_6',k2_orders_2('#skF_5',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5525,c_5460])).

tff(c_7009,plain,(
    ~ r2_hidden('#skF_6',a_2_1_orders_2('#skF_5',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6951,c_5532])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_5459,plain,(
    r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_7763,plain,(
    ! [D_10916,B_10917,C_10918] :
      ( r2_hidden('#skF_4'(D_10916,B_10917,C_10918,D_10916),C_10918)
      | r2_hidden(D_10916,a_2_1_orders_2(B_10917,C_10918))
      | ~ m1_subset_1(D_10916,u1_struct_0(B_10917))
      | ~ m1_subset_1(C_10918,k1_zfmisc_1(u1_struct_0(B_10917)))
      | ~ l1_orders_2(B_10917)
      | ~ v5_orders_2(B_10917)
      | ~ v4_orders_2(B_10917)
      | ~ v3_orders_2(B_10917)
      | v2_struct_0(B_10917) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_7773,plain,(
    ! [D_10916] :
      ( r2_hidden('#skF_4'(D_10916,'#skF_5',k1_tarski('#skF_7'),D_10916),k1_tarski('#skF_7'))
      | r2_hidden(D_10916,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
      | ~ m1_subset_1(D_10916,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5541,c_7763])).

tff(c_7783,plain,(
    ! [D_10916] :
      ( r2_hidden('#skF_4'(D_10916,'#skF_5',k1_tarski('#skF_7'),D_10916),k1_tarski('#skF_7'))
      | r2_hidden(D_10916,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
      | ~ m1_subset_1(D_10916,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_7773])).

tff(c_8567,plain,(
    ! [D_11942] :
      ( r2_hidden('#skF_4'(D_11942,'#skF_5',k1_tarski('#skF_7'),D_11942),k1_tarski('#skF_7'))
      | r2_hidden(D_11942,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
      | ~ m1_subset_1(D_11942,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_7783])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_5480,plain,(
    ! [D_6753,B_6754,A_6755] :
      ( D_6753 = B_6754
      | D_6753 = A_6755
      | ~ r2_hidden(D_6753,k2_tarski(A_6755,B_6754)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_5486,plain,(
    ! [D_6753,A_7] :
      ( D_6753 = A_7
      | D_6753 = A_7
      | ~ r2_hidden(D_6753,k1_tarski(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_5480])).

tff(c_8656,plain,(
    ! [D_12015] :
      ( '#skF_4'(D_12015,'#skF_5',k1_tarski('#skF_7'),D_12015) = '#skF_7'
      | r2_hidden(D_12015,a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
      | ~ m1_subset_1(D_12015,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_8567,c_5486])).

tff(c_8678,plain,
    ( '#skF_4'('#skF_6','#skF_5',k1_tarski('#skF_7'),'#skF_6') = '#skF_7'
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_8656,c_7009])).

tff(c_8776,plain,(
    '#skF_4'('#skF_6','#skF_5',k1_tarski('#skF_7'),'#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8678])).

tff(c_30,plain,(
    ! [B_16,D_26,C_17] :
      ( ~ r2_orders_2(B_16,D_26,'#skF_4'(D_26,B_16,C_17,D_26))
      | r2_hidden(D_26,a_2_1_orders_2(B_16,C_17))
      | ~ m1_subset_1(D_26,u1_struct_0(B_16))
      | ~ m1_subset_1(C_17,k1_zfmisc_1(u1_struct_0(B_16)))
      | ~ l1_orders_2(B_16)
      | ~ v5_orders_2(B_16)
      | ~ v4_orders_2(B_16)
      | ~ v3_orders_2(B_16)
      | v2_struct_0(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_8787,plain,
    ( ~ r2_orders_2('#skF_5','#skF_6','#skF_7')
    | r2_hidden('#skF_6',a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_8776,c_30])).

tff(c_8833,plain,
    ( r2_hidden('#skF_6',a_2_1_orders_2('#skF_5',k1_tarski('#skF_7')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_5541,c_46,c_5459,c_8787])).

tff(c_8835,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_7009,c_8833])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:02:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.13/2.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.24/2.50  
% 7.24/2.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.24/2.50  %$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 7.24/2.50  
% 7.24/2.50  %Foreground sorts:
% 7.24/2.50  
% 7.24/2.50  
% 7.24/2.50  %Background operators:
% 7.24/2.50  
% 7.24/2.50  
% 7.24/2.50  %Foreground operators:
% 7.24/2.50  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.24/2.50  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.24/2.50  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 7.24/2.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.24/2.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.24/2.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.24/2.50  tff('#skF_7', type, '#skF_7': $i).
% 7.24/2.50  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 7.24/2.50  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 7.24/2.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.24/2.50  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 7.24/2.50  tff('#skF_5', type, '#skF_5': $i).
% 7.24/2.50  tff('#skF_6', type, '#skF_6': $i).
% 7.24/2.50  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.24/2.50  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 7.24/2.50  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 7.24/2.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.24/2.50  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.24/2.50  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 7.24/2.50  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 7.24/2.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.24/2.50  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.24/2.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.24/2.50  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 7.24/2.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.24/2.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.24/2.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.24/2.50  
% 7.24/2.52  tff(f_127, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> r2_hidden(B, k2_orders_2(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_orders_2)).
% 7.24/2.52  tff(f_71, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 7.24/2.52  tff(f_105, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 7.24/2.52  tff(f_44, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 7.24/2.52  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 7.24/2.52  tff(f_60, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_orders_2)).
% 7.24/2.52  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 7.24/2.52  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 7.24/2.52  tff(f_98, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 7.24/2.52  tff(c_56, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.24/2.52  tff(c_54, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.24/2.52  tff(c_52, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.24/2.52  tff(c_50, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.24/2.52  tff(c_48, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.24/2.52  tff(c_28, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_orders_2(A_14))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.24/2.52  tff(c_44, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.24/2.52  tff(c_5502, plain, (![A_6758, B_6759]: (k6_domain_1(A_6758, B_6759)=k1_tarski(B_6759) | ~m1_subset_1(B_6759, A_6758) | v1_xboole_0(A_6758))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.24/2.52  tff(c_5509, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')=k1_tarski('#skF_7') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_44, c_5502])).
% 7.24/2.52  tff(c_5511, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_5509])).
% 7.24/2.52  tff(c_22, plain, (![A_8]: (~v1_xboole_0(u1_struct_0(A_8)) | ~l1_struct_0(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.24/2.52  tff(c_5514, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_5511, c_22])).
% 7.24/2.52  tff(c_5517, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_5514])).
% 7.24/2.52  tff(c_5520, plain, (~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_28, c_5517])).
% 7.24/2.52  tff(c_5524, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_5520])).
% 7.24/2.52  tff(c_5526, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_5509])).
% 7.24/2.52  tff(c_5525, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_5509])).
% 7.24/2.52  tff(c_26, plain, (![A_12, B_13]: (m1_subset_1(k6_domain_1(A_12, B_13), k1_zfmisc_1(A_12)) | ~m1_subset_1(B_13, A_12) | v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.24/2.52  tff(c_5536, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5525, c_26])).
% 7.24/2.52  tff(c_5540, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_5536])).
% 7.24/2.52  tff(c_5541, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_5526, c_5540])).
% 7.24/2.52  tff(c_6927, plain, (![A_9740, B_9741]: (k2_orders_2(A_9740, B_9741)=a_2_1_orders_2(A_9740, B_9741) | ~m1_subset_1(B_9741, k1_zfmisc_1(u1_struct_0(A_9740))) | ~l1_orders_2(A_9740) | ~v5_orders_2(A_9740) | ~v4_orders_2(A_9740) | ~v3_orders_2(A_9740) | v2_struct_0(A_9740))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.24/2.52  tff(c_6939, plain, (k2_orders_2('#skF_5', k1_tarski('#skF_7'))=a_2_1_orders_2('#skF_5', k1_tarski('#skF_7')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_5541, c_6927])).
% 7.24/2.52  tff(c_6950, plain, (k2_orders_2('#skF_5', k1_tarski('#skF_7'))=a_2_1_orders_2('#skF_5', k1_tarski('#skF_7')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_6939])).
% 7.24/2.52  tff(c_6951, plain, (k2_orders_2('#skF_5', k1_tarski('#skF_7'))=a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_56, c_6950])).
% 7.24/2.52  tff(c_107, plain, (![A_47, B_48]: (k6_domain_1(A_47, B_48)=k1_tarski(B_48) | ~m1_subset_1(B_48, A_47) | v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.24/2.52  tff(c_114, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')=k1_tarski('#skF_7') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_44, c_107])).
% 7.24/2.52  tff(c_116, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_114])).
% 7.24/2.52  tff(c_121, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_116, c_22])).
% 7.24/2.52  tff(c_124, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_121])).
% 7.24/2.52  tff(c_127, plain, (~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_28, c_124])).
% 7.24/2.52  tff(c_131, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_127])).
% 7.24/2.52  tff(c_132, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_114])).
% 7.24/2.52  tff(c_64, plain, (r2_orders_2('#skF_5', '#skF_6', '#skF_7') | r2_hidden('#skF_6', k2_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.24/2.52  tff(c_67, plain, (r2_hidden('#skF_6', k2_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')))), inference(splitLeft, [status(thm)], [c_64])).
% 7.24/2.52  tff(c_134, plain, (r2_hidden('#skF_6', k2_orders_2('#skF_5', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_67])).
% 7.24/2.52  tff(c_58, plain, (~r2_hidden('#skF_6', k2_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7'))) | ~r2_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.24/2.52  tff(c_170, plain, (~r2_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_132, c_58])).
% 7.24/2.52  tff(c_68, plain, (![A_37]: (k2_tarski(A_37, A_37)=k1_tarski(A_37))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.24/2.52  tff(c_6, plain, (![D_6, B_2]: (r2_hidden(D_6, k2_tarski(D_6, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.24/2.52  tff(c_74, plain, (![A_37]: (r2_hidden(A_37, k1_tarski(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_6])).
% 7.24/2.52  tff(c_133, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_114])).
% 7.24/2.52  tff(c_139, plain, (![A_49, B_50]: (m1_subset_1(k6_domain_1(A_49, B_50), k1_zfmisc_1(A_49)) | ~m1_subset_1(B_50, A_49) | v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.24/2.52  tff(c_145, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_132, c_139])).
% 7.24/2.52  tff(c_148, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_145])).
% 7.24/2.52  tff(c_149, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_133, c_148])).
% 7.24/2.52  tff(c_2101, plain, (![A_3592, B_3593]: (k2_orders_2(A_3592, B_3593)=a_2_1_orders_2(A_3592, B_3593) | ~m1_subset_1(B_3593, k1_zfmisc_1(u1_struct_0(A_3592))) | ~l1_orders_2(A_3592) | ~v5_orders_2(A_3592) | ~v4_orders_2(A_3592) | ~v3_orders_2(A_3592) | v2_struct_0(A_3592))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.24/2.52  tff(c_2113, plain, (k2_orders_2('#skF_5', k1_tarski('#skF_7'))=a_2_1_orders_2('#skF_5', k1_tarski('#skF_7')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_149, c_2101])).
% 7.24/2.52  tff(c_2124, plain, (k2_orders_2('#skF_5', k1_tarski('#skF_7'))=a_2_1_orders_2('#skF_5', k1_tarski('#skF_7')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_2113])).
% 7.24/2.52  tff(c_2125, plain, (k2_orders_2('#skF_5', k1_tarski('#skF_7'))=a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_56, c_2124])).
% 7.24/2.52  tff(c_2180, plain, (r2_hidden('#skF_6', a_2_1_orders_2('#skF_5', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_2125, c_134])).
% 7.24/2.52  tff(c_2495, plain, (![A_4029, B_4030, C_4031]: ('#skF_3'(A_4029, B_4030, C_4031)=A_4029 | ~r2_hidden(A_4029, a_2_1_orders_2(B_4030, C_4031)) | ~m1_subset_1(C_4031, k1_zfmisc_1(u1_struct_0(B_4030))) | ~l1_orders_2(B_4030) | ~v5_orders_2(B_4030) | ~v4_orders_2(B_4030) | ~v3_orders_2(B_4030) | v2_struct_0(B_4030))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.24/2.52  tff(c_2497, plain, ('#skF_3'('#skF_6', '#skF_5', k1_tarski('#skF_7'))='#skF_6' | ~m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_2180, c_2495])).
% 7.24/2.52  tff(c_2506, plain, ('#skF_3'('#skF_6', '#skF_5', k1_tarski('#skF_7'))='#skF_6' | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_149, c_2497])).
% 7.24/2.52  tff(c_2507, plain, ('#skF_3'('#skF_6', '#skF_5', k1_tarski('#skF_7'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_56, c_2506])).
% 7.24/2.52  tff(c_4457, plain, (![B_6082, A_6083, C_6084, E_6085]: (r2_orders_2(B_6082, '#skF_3'(A_6083, B_6082, C_6084), E_6085) | ~r2_hidden(E_6085, C_6084) | ~m1_subset_1(E_6085, u1_struct_0(B_6082)) | ~r2_hidden(A_6083, a_2_1_orders_2(B_6082, C_6084)) | ~m1_subset_1(C_6084, k1_zfmisc_1(u1_struct_0(B_6082))) | ~l1_orders_2(B_6082) | ~v5_orders_2(B_6082) | ~v4_orders_2(B_6082) | ~v3_orders_2(B_6082) | v2_struct_0(B_6082))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.24/2.52  tff(c_4467, plain, (![A_6083, E_6085]: (r2_orders_2('#skF_5', '#skF_3'(A_6083, '#skF_5', k1_tarski('#skF_7')), E_6085) | ~r2_hidden(E_6085, k1_tarski('#skF_7')) | ~m1_subset_1(E_6085, u1_struct_0('#skF_5')) | ~r2_hidden(A_6083, a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_149, c_4457])).
% 7.24/2.52  tff(c_4477, plain, (![A_6083, E_6085]: (r2_orders_2('#skF_5', '#skF_3'(A_6083, '#skF_5', k1_tarski('#skF_7')), E_6085) | ~r2_hidden(E_6085, k1_tarski('#skF_7')) | ~m1_subset_1(E_6085, u1_struct_0('#skF_5')) | ~r2_hidden(A_6083, a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_4467])).
% 7.24/2.52  tff(c_5388, plain, (![A_6601, E_6602]: (r2_orders_2('#skF_5', '#skF_3'(A_6601, '#skF_5', k1_tarski('#skF_7')), E_6602) | ~r2_hidden(E_6602, k1_tarski('#skF_7')) | ~m1_subset_1(E_6602, u1_struct_0('#skF_5')) | ~r2_hidden(A_6601, a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_4477])).
% 7.24/2.52  tff(c_5394, plain, (![E_6602]: (r2_orders_2('#skF_5', '#skF_6', E_6602) | ~r2_hidden(E_6602, k1_tarski('#skF_7')) | ~m1_subset_1(E_6602, u1_struct_0('#skF_5')) | ~r2_hidden('#skF_6', a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_2507, c_5388])).
% 7.24/2.52  tff(c_5436, plain, (![E_6675]: (r2_orders_2('#skF_5', '#skF_6', E_6675) | ~r2_hidden(E_6675, k1_tarski('#skF_7')) | ~m1_subset_1(E_6675, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_2180, c_5394])).
% 7.24/2.52  tff(c_5451, plain, (r2_orders_2('#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_74, c_5436])).
% 7.24/2.52  tff(c_5456, plain, (r2_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_5451])).
% 7.24/2.52  tff(c_5458, plain, $false, inference(negUnitSimplification, [status(thm)], [c_170, c_5456])).
% 7.24/2.52  tff(c_5460, plain, (~r2_hidden('#skF_6', k2_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')))), inference(splitRight, [status(thm)], [c_64])).
% 7.24/2.52  tff(c_5532, plain, (~r2_hidden('#skF_6', k2_orders_2('#skF_5', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_5525, c_5460])).
% 7.24/2.52  tff(c_7009, plain, (~r2_hidden('#skF_6', a_2_1_orders_2('#skF_5', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_6951, c_5532])).
% 7.24/2.52  tff(c_46, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.24/2.52  tff(c_5459, plain, (r2_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_64])).
% 7.24/2.52  tff(c_7763, plain, (![D_10916, B_10917, C_10918]: (r2_hidden('#skF_4'(D_10916, B_10917, C_10918, D_10916), C_10918) | r2_hidden(D_10916, a_2_1_orders_2(B_10917, C_10918)) | ~m1_subset_1(D_10916, u1_struct_0(B_10917)) | ~m1_subset_1(C_10918, k1_zfmisc_1(u1_struct_0(B_10917))) | ~l1_orders_2(B_10917) | ~v5_orders_2(B_10917) | ~v4_orders_2(B_10917) | ~v3_orders_2(B_10917) | v2_struct_0(B_10917))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.24/2.52  tff(c_7773, plain, (![D_10916]: (r2_hidden('#skF_4'(D_10916, '#skF_5', k1_tarski('#skF_7'), D_10916), k1_tarski('#skF_7')) | r2_hidden(D_10916, a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | ~m1_subset_1(D_10916, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_5541, c_7763])).
% 7.24/2.52  tff(c_7783, plain, (![D_10916]: (r2_hidden('#skF_4'(D_10916, '#skF_5', k1_tarski('#skF_7'), D_10916), k1_tarski('#skF_7')) | r2_hidden(D_10916, a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | ~m1_subset_1(D_10916, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_7773])).
% 7.24/2.52  tff(c_8567, plain, (![D_11942]: (r2_hidden('#skF_4'(D_11942, '#skF_5', k1_tarski('#skF_7'), D_11942), k1_tarski('#skF_7')) | r2_hidden(D_11942, a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | ~m1_subset_1(D_11942, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_56, c_7783])).
% 7.24/2.52  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.24/2.52  tff(c_5480, plain, (![D_6753, B_6754, A_6755]: (D_6753=B_6754 | D_6753=A_6755 | ~r2_hidden(D_6753, k2_tarski(A_6755, B_6754)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.24/2.52  tff(c_5486, plain, (![D_6753, A_7]: (D_6753=A_7 | D_6753=A_7 | ~r2_hidden(D_6753, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_5480])).
% 7.24/2.52  tff(c_8656, plain, (![D_12015]: ('#skF_4'(D_12015, '#skF_5', k1_tarski('#skF_7'), D_12015)='#skF_7' | r2_hidden(D_12015, a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | ~m1_subset_1(D_12015, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_8567, c_5486])).
% 7.24/2.52  tff(c_8678, plain, ('#skF_4'('#skF_6', '#skF_5', k1_tarski('#skF_7'), '#skF_6')='#skF_7' | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_8656, c_7009])).
% 7.24/2.52  tff(c_8776, plain, ('#skF_4'('#skF_6', '#skF_5', k1_tarski('#skF_7'), '#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8678])).
% 7.24/2.52  tff(c_30, plain, (![B_16, D_26, C_17]: (~r2_orders_2(B_16, D_26, '#skF_4'(D_26, B_16, C_17, D_26)) | r2_hidden(D_26, a_2_1_orders_2(B_16, C_17)) | ~m1_subset_1(D_26, u1_struct_0(B_16)) | ~m1_subset_1(C_17, k1_zfmisc_1(u1_struct_0(B_16))) | ~l1_orders_2(B_16) | ~v5_orders_2(B_16) | ~v4_orders_2(B_16) | ~v3_orders_2(B_16) | v2_struct_0(B_16))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.24/2.52  tff(c_8787, plain, (~r2_orders_2('#skF_5', '#skF_6', '#skF_7') | r2_hidden('#skF_6', a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_8776, c_30])).
% 7.24/2.52  tff(c_8833, plain, (r2_hidden('#skF_6', a_2_1_orders_2('#skF_5', k1_tarski('#skF_7'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_5541, c_46, c_5459, c_8787])).
% 7.24/2.52  tff(c_8835, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_7009, c_8833])).
% 7.24/2.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.24/2.52  
% 7.24/2.52  Inference rules
% 7.24/2.52  ----------------------
% 7.24/2.52  #Ref     : 0
% 7.24/2.52  #Sup     : 1202
% 7.24/2.52  #Fact    : 40
% 7.24/2.52  #Define  : 0
% 7.24/2.52  #Split   : 27
% 7.24/2.52  #Chain   : 0
% 7.24/2.52  #Close   : 0
% 7.24/2.52  
% 7.24/2.52  Ordering : KBO
% 7.24/2.52  
% 7.24/2.52  Simplification rules
% 7.24/2.52  ----------------------
% 7.24/2.52  #Subsume      : 428
% 7.24/2.52  #Demod        : 415
% 7.24/2.52  #Tautology    : 374
% 7.24/2.52  #SimpNegUnit  : 67
% 7.24/2.52  #BackRed      : 4
% 7.24/2.52  
% 7.24/2.52  #Partial instantiations: 6930
% 7.24/2.52  #Strategies tried      : 1
% 7.24/2.52  
% 7.24/2.52  Timing (in seconds)
% 7.24/2.52  ----------------------
% 7.38/2.52  Preprocessing        : 0.34
% 7.38/2.52  Parsing              : 0.17
% 7.38/2.52  CNF conversion       : 0.02
% 7.38/2.52  Main loop            : 1.39
% 7.38/2.52  Inferencing          : 0.66
% 7.38/2.52  Reduction            : 0.34
% 7.38/2.52  Demodulation         : 0.24
% 7.38/2.52  BG Simplification    : 0.06
% 7.38/2.52  Subsumption          : 0.26
% 7.38/2.52  Abstraction          : 0.07
% 7.38/2.52  MUC search           : 0.00
% 7.38/2.52  Cooper               : 0.00
% 7.38/2.52  Total                : 1.78
% 7.38/2.52  Index Insertion      : 0.00
% 7.38/2.52  Index Deletion       : 0.00
% 7.38/2.52  Index Matching       : 0.00
% 7.38/2.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
