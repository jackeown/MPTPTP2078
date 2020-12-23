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
% DateTime   : Thu Dec  3 10:19:41 EST 2020

% Result     : Theorem 6.49s
% Output     : CNFRefutation 6.87s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 509 expanded)
%              Number of leaves         :   36 ( 189 expanded)
%              Depth                    :   19
%              Number of atoms          :  266 (1759 expanded)
%              Number of equality atoms :   36 ( 173 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(k1_orders_2,type,(
    k1_orders_2: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(a_2_0_orders_2,type,(
    a_2_0_orders_2: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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
                <=> r2_hidden(C,k1_orders_2(A,k6_domain_1(u1_struct_0(A),B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_orders_2)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_105,axiom,(
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

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_orders_2(A,B) = a_2_0_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).

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

tff(f_98,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v3_orders_2(B)
        & v4_orders_2(B)
        & v5_orders_2(B)
        & l1_orders_2(B)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
     => ( r2_hidden(A,a_2_0_orders_2(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & ! [E] :
                ( m1_subset_1(E,u1_struct_0(B))
               => ( r2_hidden(E,C)
                 => r2_orders_2(B,E,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

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

tff(c_46,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_5510,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_46,c_5502])).

tff(c_5546,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_5526,c_5510])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(k6_domain_1(A_12,B_13),k1_zfmisc_1(A_12))
      | ~ m1_subset_1(B_13,A_12)
      | v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_5551,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5546,c_26])).

tff(c_5555,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_5551])).

tff(c_5556,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_5526,c_5555])).

tff(c_6927,plain,(
    ! [A_9740,B_9741] :
      ( k1_orders_2(A_9740,B_9741) = a_2_0_orders_2(A_9740,B_9741)
      | ~ m1_subset_1(B_9741,k1_zfmisc_1(u1_struct_0(A_9740)))
      | ~ l1_orders_2(A_9740)
      | ~ v5_orders_2(A_9740)
      | ~ v4_orders_2(A_9740)
      | ~ v3_orders_2(A_9740)
      | v2_struct_0(A_9740) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6936,plain,
    ( k1_orders_2('#skF_5',k1_tarski('#skF_6')) = a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_5556,c_6927])).

tff(c_6946,plain,
    ( k1_orders_2('#skF_5',k1_tarski('#skF_6')) = a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_6936])).

tff(c_6947,plain,(
    k1_orders_2('#skF_5',k1_tarski('#skF_6')) = a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_6946])).

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

tff(c_133,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_115,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_46,c_107])).

tff(c_138,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_115])).

tff(c_64,plain,
    ( r2_orders_2('#skF_5','#skF_6','#skF_7')
    | r2_hidden('#skF_7',k1_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_67,plain,(
    r2_hidden('#skF_7',k1_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_139,plain,(
    r2_hidden('#skF_7',k1_orders_2('#skF_5',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_67])).

tff(c_58,plain,
    ( ~ r2_hidden('#skF_7',k1_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_6')))
    | ~ r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_170,plain,(
    ~ r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_138,c_58])).

tff(c_68,plain,(
    ! [A_37] : k2_tarski(A_37,A_37) = k1_tarski(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_6,plain,(
    ! [D_6,B_2] : r2_hidden(D_6,k2_tarski(D_6,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_74,plain,(
    ! [A_37] : r2_hidden(A_37,k1_tarski(A_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_6])).

tff(c_144,plain,(
    ! [A_49,B_50] :
      ( m1_subset_1(k6_domain_1(A_49,B_50),k1_zfmisc_1(A_49))
      | ~ m1_subset_1(B_50,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_150,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_144])).

tff(c_156,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_150])).

tff(c_157,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_156])).

tff(c_2101,plain,(
    ! [A_3592,B_3593] :
      ( k1_orders_2(A_3592,B_3593) = a_2_0_orders_2(A_3592,B_3593)
      | ~ m1_subset_1(B_3593,k1_zfmisc_1(u1_struct_0(A_3592)))
      | ~ l1_orders_2(A_3592)
      | ~ v5_orders_2(A_3592)
      | ~ v4_orders_2(A_3592)
      | ~ v3_orders_2(A_3592)
      | v2_struct_0(A_3592) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2113,plain,
    ( k1_orders_2('#skF_5',k1_tarski('#skF_6')) = a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_157,c_2101])).

tff(c_2124,plain,
    ( k1_orders_2('#skF_5',k1_tarski('#skF_6')) = a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_2113])).

tff(c_2125,plain,(
    k1_orders_2('#skF_5',k1_tarski('#skF_6')) = a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2124])).

tff(c_2180,plain,(
    r2_hidden('#skF_7',a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2125,c_139])).

tff(c_2495,plain,(
    ! [A_4029,B_4030,C_4031] :
      ( '#skF_3'(A_4029,B_4030,C_4031) = A_4029
      | ~ r2_hidden(A_4029,a_2_0_orders_2(B_4030,C_4031))
      | ~ m1_subset_1(C_4031,k1_zfmisc_1(u1_struct_0(B_4030)))
      | ~ l1_orders_2(B_4030)
      | ~ v5_orders_2(B_4030)
      | ~ v4_orders_2(B_4030)
      | ~ v3_orders_2(B_4030)
      | v2_struct_0(B_4030) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2497,plain,
    ( '#skF_3'('#skF_7','#skF_5',k1_tarski('#skF_6')) = '#skF_7'
    | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_2180,c_2495])).

tff(c_2506,plain,
    ( '#skF_3'('#skF_7','#skF_5',k1_tarski('#skF_6')) = '#skF_7'
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_157,c_2497])).

tff(c_2507,plain,(
    '#skF_3'('#skF_7','#skF_5',k1_tarski('#skF_6')) = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2506])).

tff(c_4457,plain,(
    ! [B_6082,E_6083,A_6084,C_6085] :
      ( r2_orders_2(B_6082,E_6083,'#skF_3'(A_6084,B_6082,C_6085))
      | ~ r2_hidden(E_6083,C_6085)
      | ~ m1_subset_1(E_6083,u1_struct_0(B_6082))
      | ~ r2_hidden(A_6084,a_2_0_orders_2(B_6082,C_6085))
      | ~ m1_subset_1(C_6085,k1_zfmisc_1(u1_struct_0(B_6082)))
      | ~ l1_orders_2(B_6082)
      | ~ v5_orders_2(B_6082)
      | ~ v4_orders_2(B_6082)
      | ~ v3_orders_2(B_6082)
      | v2_struct_0(B_6082) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4467,plain,(
    ! [E_6083,A_6084] :
      ( r2_orders_2('#skF_5',E_6083,'#skF_3'(A_6084,'#skF_5',k1_tarski('#skF_6')))
      | ~ r2_hidden(E_6083,k1_tarski('#skF_6'))
      | ~ m1_subset_1(E_6083,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_6084,a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_157,c_4457])).

tff(c_4477,plain,(
    ! [E_6083,A_6084] :
      ( r2_orders_2('#skF_5',E_6083,'#skF_3'(A_6084,'#skF_5',k1_tarski('#skF_6')))
      | ~ r2_hidden(E_6083,k1_tarski('#skF_6'))
      | ~ m1_subset_1(E_6083,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_6084,a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_4467])).

tff(c_5388,plain,(
    ! [E_6601,A_6602] :
      ( r2_orders_2('#skF_5',E_6601,'#skF_3'(A_6602,'#skF_5',k1_tarski('#skF_6')))
      | ~ r2_hidden(E_6601,k1_tarski('#skF_6'))
      | ~ m1_subset_1(E_6601,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_6602,a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_4477])).

tff(c_5394,plain,(
    ! [E_6601] :
      ( r2_orders_2('#skF_5',E_6601,'#skF_7')
      | ~ r2_hidden(E_6601,k1_tarski('#skF_6'))
      | ~ m1_subset_1(E_6601,u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_7',a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2507,c_5388])).

tff(c_5436,plain,(
    ! [E_6675] :
      ( r2_orders_2('#skF_5',E_6675,'#skF_7')
      | ~ r2_hidden(E_6675,k1_tarski('#skF_6'))
      | ~ m1_subset_1(E_6675,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2180,c_5394])).

tff(c_5451,plain,
    ( r2_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_74,c_5436])).

tff(c_5456,plain,(
    r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_5451])).

tff(c_5458,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_5456])).

tff(c_5460,plain,(
    ~ r2_hidden('#skF_7',k1_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_5547,plain,(
    ~ r2_hidden('#skF_7',k1_orders_2('#skF_5',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5546,c_5460])).

tff(c_6953,plain,(
    ~ r2_hidden('#skF_7',a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6947,c_5547])).

tff(c_5459,plain,(
    r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_7763,plain,(
    ! [D_10916,B_10917,C_10918] :
      ( r2_hidden('#skF_4'(D_10916,B_10917,C_10918,D_10916),C_10918)
      | r2_hidden(D_10916,a_2_0_orders_2(B_10917,C_10918))
      | ~ m1_subset_1(D_10916,u1_struct_0(B_10917))
      | ~ m1_subset_1(C_10918,k1_zfmisc_1(u1_struct_0(B_10917)))
      | ~ l1_orders_2(B_10917)
      | ~ v5_orders_2(B_10917)
      | ~ v4_orders_2(B_10917)
      | ~ v3_orders_2(B_10917)
      | v2_struct_0(B_10917) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_7771,plain,(
    ! [D_10916] :
      ( r2_hidden('#skF_4'(D_10916,'#skF_5',k1_tarski('#skF_6'),D_10916),k1_tarski('#skF_6'))
      | r2_hidden(D_10916,a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
      | ~ m1_subset_1(D_10916,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5556,c_7763])).

tff(c_7779,plain,(
    ! [D_10916] :
      ( r2_hidden('#skF_4'(D_10916,'#skF_5',k1_tarski('#skF_6'),D_10916),k1_tarski('#skF_6'))
      | r2_hidden(D_10916,a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
      | ~ m1_subset_1(D_10916,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_7771])).

tff(c_7943,plain,(
    ! [D_11065] :
      ( r2_hidden('#skF_4'(D_11065,'#skF_5',k1_tarski('#skF_6'),D_11065),k1_tarski('#skF_6'))
      | r2_hidden(D_11065,a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
      | ~ m1_subset_1(D_11065,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_7779])).

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

tff(c_8032,plain,(
    ! [D_11138] :
      ( '#skF_4'(D_11138,'#skF_5',k1_tarski('#skF_6'),D_11138) = '#skF_6'
      | r2_hidden(D_11138,a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
      | ~ m1_subset_1(D_11138,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_7943,c_5486])).

tff(c_8049,plain,
    ( '#skF_4'('#skF_7','#skF_5',k1_tarski('#skF_6'),'#skF_7') = '#skF_6'
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_8032,c_6953])).

tff(c_8141,plain,(
    '#skF_4'('#skF_7','#skF_5',k1_tarski('#skF_6'),'#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_8049])).

tff(c_8235,plain,(
    ! [B_11356,D_11357,C_11358] :
      ( ~ r2_orders_2(B_11356,'#skF_4'(D_11357,B_11356,C_11358,D_11357),D_11357)
      | r2_hidden(D_11357,a_2_0_orders_2(B_11356,C_11358))
      | ~ m1_subset_1(D_11357,u1_struct_0(B_11356))
      | ~ m1_subset_1(C_11358,k1_zfmisc_1(u1_struct_0(B_11356)))
      | ~ l1_orders_2(B_11356)
      | ~ v5_orders_2(B_11356)
      | ~ v4_orders_2(B_11356)
      | ~ v3_orders_2(B_11356)
      | v2_struct_0(B_11356) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_8237,plain,
    ( ~ r2_orders_2('#skF_5','#skF_6','#skF_7')
    | r2_hidden('#skF_7',a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_8141,c_8235])).

tff(c_8244,plain,
    ( r2_hidden('#skF_7',a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_5556,c_44,c_5459,c_8237])).

tff(c_8246,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_6953,c_8244])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:23:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.49/2.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.49/2.35  
% 6.49/2.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.49/2.35  %$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 6.49/2.35  
% 6.49/2.35  %Foreground sorts:
% 6.49/2.35  
% 6.49/2.35  
% 6.49/2.35  %Background operators:
% 6.49/2.35  
% 6.49/2.35  
% 6.49/2.35  %Foreground operators:
% 6.49/2.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.49/2.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.49/2.35  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 6.49/2.35  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 6.49/2.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.49/2.35  tff(a_2_0_orders_2, type, a_2_0_orders_2: ($i * $i) > $i).
% 6.49/2.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.49/2.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.49/2.35  tff('#skF_7', type, '#skF_7': $i).
% 6.49/2.35  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 6.49/2.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.49/2.35  tff('#skF_5', type, '#skF_5': $i).
% 6.49/2.35  tff('#skF_6', type, '#skF_6': $i).
% 6.49/2.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.49/2.35  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 6.49/2.35  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 6.49/2.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.49/2.35  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.49/2.35  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 6.49/2.35  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 6.49/2.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.49/2.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.49/2.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.49/2.35  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 6.49/2.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.49/2.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.49/2.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.49/2.35  
% 6.87/2.37  tff(f_127, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> r2_hidden(C, k1_orders_2(A, k6_domain_1(u1_struct_0(A), B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_orders_2)).
% 6.87/2.37  tff(f_71, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 6.87/2.37  tff(f_105, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 6.87/2.37  tff(f_44, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 6.87/2.37  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 6.87/2.37  tff(f_60, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_orders_2(A, B) = a_2_0_orders_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_orders_2)).
% 6.87/2.37  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.87/2.37  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 6.87/2.37  tff(f_98, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_0_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, E, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 6.87/2.37  tff(c_56, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.87/2.37  tff(c_54, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.87/2.37  tff(c_52, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.87/2.37  tff(c_50, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.87/2.37  tff(c_48, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.87/2.37  tff(c_28, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_orders_2(A_14))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.87/2.37  tff(c_44, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.87/2.37  tff(c_5502, plain, (![A_6758, B_6759]: (k6_domain_1(A_6758, B_6759)=k1_tarski(B_6759) | ~m1_subset_1(B_6759, A_6758) | v1_xboole_0(A_6758))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.87/2.37  tff(c_5509, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')=k1_tarski('#skF_7') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_44, c_5502])).
% 6.87/2.37  tff(c_5511, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_5509])).
% 6.87/2.37  tff(c_22, plain, (![A_8]: (~v1_xboole_0(u1_struct_0(A_8)) | ~l1_struct_0(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.87/2.37  tff(c_5514, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_5511, c_22])).
% 6.87/2.37  tff(c_5517, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_5514])).
% 6.87/2.37  tff(c_5520, plain, (~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_28, c_5517])).
% 6.87/2.37  tff(c_5524, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_5520])).
% 6.87/2.37  tff(c_5526, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_5509])).
% 6.87/2.37  tff(c_46, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.87/2.37  tff(c_5510, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_46, c_5502])).
% 6.87/2.37  tff(c_5546, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_5526, c_5510])).
% 6.87/2.37  tff(c_26, plain, (![A_12, B_13]: (m1_subset_1(k6_domain_1(A_12, B_13), k1_zfmisc_1(A_12)) | ~m1_subset_1(B_13, A_12) | v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.87/2.37  tff(c_5551, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5546, c_26])).
% 6.87/2.37  tff(c_5555, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_5551])).
% 6.87/2.37  tff(c_5556, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_5526, c_5555])).
% 6.87/2.37  tff(c_6927, plain, (![A_9740, B_9741]: (k1_orders_2(A_9740, B_9741)=a_2_0_orders_2(A_9740, B_9741) | ~m1_subset_1(B_9741, k1_zfmisc_1(u1_struct_0(A_9740))) | ~l1_orders_2(A_9740) | ~v5_orders_2(A_9740) | ~v4_orders_2(A_9740) | ~v3_orders_2(A_9740) | v2_struct_0(A_9740))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.87/2.37  tff(c_6936, plain, (k1_orders_2('#skF_5', k1_tarski('#skF_6'))=a_2_0_orders_2('#skF_5', k1_tarski('#skF_6')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_5556, c_6927])).
% 6.87/2.37  tff(c_6946, plain, (k1_orders_2('#skF_5', k1_tarski('#skF_6'))=a_2_0_orders_2('#skF_5', k1_tarski('#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_6936])).
% 6.87/2.37  tff(c_6947, plain, (k1_orders_2('#skF_5', k1_tarski('#skF_6'))=a_2_0_orders_2('#skF_5', k1_tarski('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_56, c_6946])).
% 6.87/2.37  tff(c_107, plain, (![A_47, B_48]: (k6_domain_1(A_47, B_48)=k1_tarski(B_48) | ~m1_subset_1(B_48, A_47) | v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.87/2.37  tff(c_114, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')=k1_tarski('#skF_7') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_44, c_107])).
% 6.87/2.37  tff(c_116, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_114])).
% 6.87/2.37  tff(c_121, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_116, c_22])).
% 6.87/2.37  tff(c_124, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_121])).
% 6.87/2.37  tff(c_127, plain, (~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_28, c_124])).
% 6.87/2.37  tff(c_131, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_127])).
% 6.87/2.37  tff(c_133, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_114])).
% 6.87/2.37  tff(c_115, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_46, c_107])).
% 6.87/2.37  tff(c_138, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_133, c_115])).
% 6.87/2.37  tff(c_64, plain, (r2_orders_2('#skF_5', '#skF_6', '#skF_7') | r2_hidden('#skF_7', k1_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.87/2.37  tff(c_67, plain, (r2_hidden('#skF_7', k1_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')))), inference(splitLeft, [status(thm)], [c_64])).
% 6.87/2.37  tff(c_139, plain, (r2_hidden('#skF_7', k1_orders_2('#skF_5', k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_67])).
% 6.87/2.37  tff(c_58, plain, (~r2_hidden('#skF_7', k1_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_6'))) | ~r2_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.87/2.37  tff(c_170, plain, (~r2_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_138, c_58])).
% 6.87/2.37  tff(c_68, plain, (![A_37]: (k2_tarski(A_37, A_37)=k1_tarski(A_37))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.87/2.37  tff(c_6, plain, (![D_6, B_2]: (r2_hidden(D_6, k2_tarski(D_6, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.87/2.37  tff(c_74, plain, (![A_37]: (r2_hidden(A_37, k1_tarski(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_6])).
% 6.87/2.37  tff(c_144, plain, (![A_49, B_50]: (m1_subset_1(k6_domain_1(A_49, B_50), k1_zfmisc_1(A_49)) | ~m1_subset_1(B_50, A_49) | v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.87/2.37  tff(c_150, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_138, c_144])).
% 6.87/2.37  tff(c_156, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_150])).
% 6.87/2.37  tff(c_157, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_133, c_156])).
% 6.87/2.37  tff(c_2101, plain, (![A_3592, B_3593]: (k1_orders_2(A_3592, B_3593)=a_2_0_orders_2(A_3592, B_3593) | ~m1_subset_1(B_3593, k1_zfmisc_1(u1_struct_0(A_3592))) | ~l1_orders_2(A_3592) | ~v5_orders_2(A_3592) | ~v4_orders_2(A_3592) | ~v3_orders_2(A_3592) | v2_struct_0(A_3592))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.87/2.37  tff(c_2113, plain, (k1_orders_2('#skF_5', k1_tarski('#skF_6'))=a_2_0_orders_2('#skF_5', k1_tarski('#skF_6')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_157, c_2101])).
% 6.87/2.37  tff(c_2124, plain, (k1_orders_2('#skF_5', k1_tarski('#skF_6'))=a_2_0_orders_2('#skF_5', k1_tarski('#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_2113])).
% 6.87/2.37  tff(c_2125, plain, (k1_orders_2('#skF_5', k1_tarski('#skF_6'))=a_2_0_orders_2('#skF_5', k1_tarski('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_56, c_2124])).
% 6.87/2.37  tff(c_2180, plain, (r2_hidden('#skF_7', a_2_0_orders_2('#skF_5', k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_2125, c_139])).
% 6.87/2.37  tff(c_2495, plain, (![A_4029, B_4030, C_4031]: ('#skF_3'(A_4029, B_4030, C_4031)=A_4029 | ~r2_hidden(A_4029, a_2_0_orders_2(B_4030, C_4031)) | ~m1_subset_1(C_4031, k1_zfmisc_1(u1_struct_0(B_4030))) | ~l1_orders_2(B_4030) | ~v5_orders_2(B_4030) | ~v4_orders_2(B_4030) | ~v3_orders_2(B_4030) | v2_struct_0(B_4030))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.87/2.37  tff(c_2497, plain, ('#skF_3'('#skF_7', '#skF_5', k1_tarski('#skF_6'))='#skF_7' | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_2180, c_2495])).
% 6.87/2.37  tff(c_2506, plain, ('#skF_3'('#skF_7', '#skF_5', k1_tarski('#skF_6'))='#skF_7' | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_157, c_2497])).
% 6.87/2.37  tff(c_2507, plain, ('#skF_3'('#skF_7', '#skF_5', k1_tarski('#skF_6'))='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_56, c_2506])).
% 6.87/2.37  tff(c_4457, plain, (![B_6082, E_6083, A_6084, C_6085]: (r2_orders_2(B_6082, E_6083, '#skF_3'(A_6084, B_6082, C_6085)) | ~r2_hidden(E_6083, C_6085) | ~m1_subset_1(E_6083, u1_struct_0(B_6082)) | ~r2_hidden(A_6084, a_2_0_orders_2(B_6082, C_6085)) | ~m1_subset_1(C_6085, k1_zfmisc_1(u1_struct_0(B_6082))) | ~l1_orders_2(B_6082) | ~v5_orders_2(B_6082) | ~v4_orders_2(B_6082) | ~v3_orders_2(B_6082) | v2_struct_0(B_6082))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.87/2.37  tff(c_4467, plain, (![E_6083, A_6084]: (r2_orders_2('#skF_5', E_6083, '#skF_3'(A_6084, '#skF_5', k1_tarski('#skF_6'))) | ~r2_hidden(E_6083, k1_tarski('#skF_6')) | ~m1_subset_1(E_6083, u1_struct_0('#skF_5')) | ~r2_hidden(A_6084, a_2_0_orders_2('#skF_5', k1_tarski('#skF_6'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_157, c_4457])).
% 6.87/2.37  tff(c_4477, plain, (![E_6083, A_6084]: (r2_orders_2('#skF_5', E_6083, '#skF_3'(A_6084, '#skF_5', k1_tarski('#skF_6'))) | ~r2_hidden(E_6083, k1_tarski('#skF_6')) | ~m1_subset_1(E_6083, u1_struct_0('#skF_5')) | ~r2_hidden(A_6084, a_2_0_orders_2('#skF_5', k1_tarski('#skF_6'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_4467])).
% 6.87/2.37  tff(c_5388, plain, (![E_6601, A_6602]: (r2_orders_2('#skF_5', E_6601, '#skF_3'(A_6602, '#skF_5', k1_tarski('#skF_6'))) | ~r2_hidden(E_6601, k1_tarski('#skF_6')) | ~m1_subset_1(E_6601, u1_struct_0('#skF_5')) | ~r2_hidden(A_6602, a_2_0_orders_2('#skF_5', k1_tarski('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_4477])).
% 6.87/2.37  tff(c_5394, plain, (![E_6601]: (r2_orders_2('#skF_5', E_6601, '#skF_7') | ~r2_hidden(E_6601, k1_tarski('#skF_6')) | ~m1_subset_1(E_6601, u1_struct_0('#skF_5')) | ~r2_hidden('#skF_7', a_2_0_orders_2('#skF_5', k1_tarski('#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_2507, c_5388])).
% 6.87/2.37  tff(c_5436, plain, (![E_6675]: (r2_orders_2('#skF_5', E_6675, '#skF_7') | ~r2_hidden(E_6675, k1_tarski('#skF_6')) | ~m1_subset_1(E_6675, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_2180, c_5394])).
% 6.87/2.37  tff(c_5451, plain, (r2_orders_2('#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_74, c_5436])).
% 6.87/2.37  tff(c_5456, plain, (r2_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_5451])).
% 6.87/2.37  tff(c_5458, plain, $false, inference(negUnitSimplification, [status(thm)], [c_170, c_5456])).
% 6.87/2.37  tff(c_5460, plain, (~r2_hidden('#skF_7', k1_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')))), inference(splitRight, [status(thm)], [c_64])).
% 6.87/2.37  tff(c_5547, plain, (~r2_hidden('#skF_7', k1_orders_2('#skF_5', k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_5546, c_5460])).
% 6.87/2.37  tff(c_6953, plain, (~r2_hidden('#skF_7', a_2_0_orders_2('#skF_5', k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_6947, c_5547])).
% 6.87/2.37  tff(c_5459, plain, (r2_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_64])).
% 6.87/2.37  tff(c_7763, plain, (![D_10916, B_10917, C_10918]: (r2_hidden('#skF_4'(D_10916, B_10917, C_10918, D_10916), C_10918) | r2_hidden(D_10916, a_2_0_orders_2(B_10917, C_10918)) | ~m1_subset_1(D_10916, u1_struct_0(B_10917)) | ~m1_subset_1(C_10918, k1_zfmisc_1(u1_struct_0(B_10917))) | ~l1_orders_2(B_10917) | ~v5_orders_2(B_10917) | ~v4_orders_2(B_10917) | ~v3_orders_2(B_10917) | v2_struct_0(B_10917))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.87/2.37  tff(c_7771, plain, (![D_10916]: (r2_hidden('#skF_4'(D_10916, '#skF_5', k1_tarski('#skF_6'), D_10916), k1_tarski('#skF_6')) | r2_hidden(D_10916, a_2_0_orders_2('#skF_5', k1_tarski('#skF_6'))) | ~m1_subset_1(D_10916, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_5556, c_7763])).
% 6.87/2.37  tff(c_7779, plain, (![D_10916]: (r2_hidden('#skF_4'(D_10916, '#skF_5', k1_tarski('#skF_6'), D_10916), k1_tarski('#skF_6')) | r2_hidden(D_10916, a_2_0_orders_2('#skF_5', k1_tarski('#skF_6'))) | ~m1_subset_1(D_10916, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_7771])).
% 6.87/2.37  tff(c_7943, plain, (![D_11065]: (r2_hidden('#skF_4'(D_11065, '#skF_5', k1_tarski('#skF_6'), D_11065), k1_tarski('#skF_6')) | r2_hidden(D_11065, a_2_0_orders_2('#skF_5', k1_tarski('#skF_6'))) | ~m1_subset_1(D_11065, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_56, c_7779])).
% 6.87/2.37  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.87/2.37  tff(c_5480, plain, (![D_6753, B_6754, A_6755]: (D_6753=B_6754 | D_6753=A_6755 | ~r2_hidden(D_6753, k2_tarski(A_6755, B_6754)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.87/2.37  tff(c_5486, plain, (![D_6753, A_7]: (D_6753=A_7 | D_6753=A_7 | ~r2_hidden(D_6753, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_5480])).
% 6.87/2.37  tff(c_8032, plain, (![D_11138]: ('#skF_4'(D_11138, '#skF_5', k1_tarski('#skF_6'), D_11138)='#skF_6' | r2_hidden(D_11138, a_2_0_orders_2('#skF_5', k1_tarski('#skF_6'))) | ~m1_subset_1(D_11138, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_7943, c_5486])).
% 6.87/2.37  tff(c_8049, plain, ('#skF_4'('#skF_7', '#skF_5', k1_tarski('#skF_6'), '#skF_7')='#skF_6' | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_8032, c_6953])).
% 6.87/2.37  tff(c_8141, plain, ('#skF_4'('#skF_7', '#skF_5', k1_tarski('#skF_6'), '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_8049])).
% 6.87/2.37  tff(c_8235, plain, (![B_11356, D_11357, C_11358]: (~r2_orders_2(B_11356, '#skF_4'(D_11357, B_11356, C_11358, D_11357), D_11357) | r2_hidden(D_11357, a_2_0_orders_2(B_11356, C_11358)) | ~m1_subset_1(D_11357, u1_struct_0(B_11356)) | ~m1_subset_1(C_11358, k1_zfmisc_1(u1_struct_0(B_11356))) | ~l1_orders_2(B_11356) | ~v5_orders_2(B_11356) | ~v4_orders_2(B_11356) | ~v3_orders_2(B_11356) | v2_struct_0(B_11356))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.87/2.37  tff(c_8237, plain, (~r2_orders_2('#skF_5', '#skF_6', '#skF_7') | r2_hidden('#skF_7', a_2_0_orders_2('#skF_5', k1_tarski('#skF_6'))) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_8141, c_8235])).
% 6.87/2.37  tff(c_8244, plain, (r2_hidden('#skF_7', a_2_0_orders_2('#skF_5', k1_tarski('#skF_6'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_5556, c_44, c_5459, c_8237])).
% 6.87/2.37  tff(c_8246, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_6953, c_8244])).
% 6.87/2.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.87/2.37  
% 6.87/2.37  Inference rules
% 6.87/2.37  ----------------------
% 6.87/2.37  #Ref     : 0
% 6.87/2.37  #Sup     : 1125
% 6.87/2.37  #Fact    : 38
% 6.87/2.37  #Define  : 0
% 6.87/2.37  #Split   : 24
% 6.87/2.37  #Chain   : 0
% 6.87/2.37  #Close   : 0
% 6.87/2.37  
% 6.87/2.37  Ordering : KBO
% 6.87/2.37  
% 6.87/2.37  Simplification rules
% 6.87/2.37  ----------------------
% 6.87/2.37  #Subsume      : 397
% 6.87/2.37  #Demod        : 332
% 6.87/2.37  #Tautology    : 355
% 6.87/2.37  #SimpNegUnit  : 53
% 6.87/2.37  #BackRed      : 4
% 6.87/2.37  
% 6.87/2.37  #Partial instantiations: 6510
% 6.87/2.37  #Strategies tried      : 1
% 6.87/2.37  
% 6.87/2.37  Timing (in seconds)
% 6.87/2.37  ----------------------
% 6.87/2.38  Preprocessing        : 0.36
% 6.87/2.38  Parsing              : 0.19
% 6.87/2.38  CNF conversion       : 0.03
% 6.87/2.38  Main loop            : 1.23
% 6.87/2.38  Inferencing          : 0.58
% 6.87/2.38  Reduction            : 0.29
% 6.87/2.38  Demodulation         : 0.20
% 6.87/2.38  BG Simplification    : 0.05
% 6.87/2.38  Subsumption          : 0.23
% 6.87/2.38  Abstraction          : 0.06
% 6.87/2.38  MUC search           : 0.00
% 6.87/2.38  Cooper               : 0.00
% 6.87/2.38  Total                : 1.63
% 6.87/2.38  Index Insertion      : 0.00
% 6.87/2.38  Index Deletion       : 0.00
% 6.87/2.38  Index Matching       : 0.00
% 6.87/2.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
