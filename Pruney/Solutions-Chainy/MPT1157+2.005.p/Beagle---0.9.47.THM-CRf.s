%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:41 EST 2020

% Result     : Theorem 6.62s
% Output     : CNFRefutation 6.62s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 534 expanded)
%              Number of leaves         :   37 ( 205 expanded)
%              Depth                    :   19
%              Number of atoms          :  281 (1982 expanded)
%              Number of equality atoms :   36 ( 156 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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
                <=> r2_hidden(C,k1_orders_2(A,k6_domain_1(u1_struct_0(A),B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_orders_2)).

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

tff(f_91,axiom,(
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

tff(c_48,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_26,plain,(
    ! [A_12] :
      ( l1_struct_0(A_12)
      | ~ l1_orders_2(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_46,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_4883,plain,(
    ! [A_6609,B_6610] :
      ( k6_domain_1(A_6609,B_6610) = k1_tarski(B_6610)
      | ~ m1_subset_1(B_6610,A_6609)
      | v1_xboole_0(A_6609) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4890,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_46,c_4883])).

tff(c_4892,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_4890])).

tff(c_22,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(u1_struct_0(A_8))
      | ~ l1_struct_0(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4896,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4892,c_22])).

tff(c_4899,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4896])).

tff(c_4902,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_4899])).

tff(c_4906,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_4902])).

tff(c_4908,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_4890])).

tff(c_4891,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_48,c_4883])).

tff(c_4909,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_4908,c_4891])).

tff(c_4935,plain,(
    ! [A_6625,B_6626] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_6625),B_6626),k1_zfmisc_1(u1_struct_0(A_6625)))
      | ~ m1_subset_1(B_6626,u1_struct_0(A_6625))
      | ~ l1_orders_2(A_6625)
      | ~ v3_orders_2(A_6625)
      | v2_struct_0(A_6625) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_4944,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4909,c_4935])).

tff(c_4950,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_50,c_48,c_4944])).

tff(c_4951,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4950])).

tff(c_6344,plain,(
    ! [A_9809,B_9810] :
      ( k1_orders_2(A_9809,B_9810) = a_2_0_orders_2(A_9809,B_9810)
      | ~ m1_subset_1(B_9810,k1_zfmisc_1(u1_struct_0(A_9809)))
      | ~ l1_orders_2(A_9809)
      | ~ v5_orders_2(A_9809)
      | ~ v4_orders_2(A_9809)
      | ~ v3_orders_2(A_9809)
      | v2_struct_0(A_9809) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6353,plain,
    ( k1_orders_2('#skF_5',k1_tarski('#skF_6')) = a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4951,c_6344])).

tff(c_6362,plain,
    ( k1_orders_2('#skF_5',k1_tarski('#skF_6')) = a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_6353])).

tff(c_6363,plain,(
    k1_orders_2('#skF_5',k1_tarski('#skF_6')) = a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_6362])).

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

tff(c_135,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_117,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_48,c_109])).

tff(c_140,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_117])).

tff(c_66,plain,
    ( r2_orders_2('#skF_5','#skF_6','#skF_7')
    | r2_hidden('#skF_7',k1_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_69,plain,(
    r2_hidden('#skF_7',k1_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_141,plain,(
    r2_hidden('#skF_7',k1_orders_2('#skF_5',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_69])).

tff(c_60,plain,
    ( ~ r2_hidden('#skF_7',k1_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_6')))
    | ~ r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_146,plain,
    ( ~ r2_hidden('#skF_7',k1_orders_2('#skF_5',k1_tarski('#skF_6')))
    | ~ r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_60])).

tff(c_147,plain,(
    ~ r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_146])).

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

tff(c_170,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_164])).

tff(c_176,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_50,c_48,c_170])).

tff(c_177,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_176])).

tff(c_1601,plain,(
    ! [A_3366,B_3367] :
      ( k1_orders_2(A_3366,B_3367) = a_2_0_orders_2(A_3366,B_3367)
      | ~ m1_subset_1(B_3367,k1_zfmisc_1(u1_struct_0(A_3366)))
      | ~ l1_orders_2(A_3366)
      | ~ v5_orders_2(A_3366)
      | ~ v4_orders_2(A_3366)
      | ~ v3_orders_2(A_3366)
      | v2_struct_0(A_3366) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1611,plain,
    ( k1_orders_2('#skF_5',k1_tarski('#skF_6')) = a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_177,c_1601])).

tff(c_1623,plain,
    ( k1_orders_2('#skF_5',k1_tarski('#skF_6')) = a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_1611])).

tff(c_1624,plain,(
    k1_orders_2('#skF_5',k1_tarski('#skF_6')) = a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1623])).

tff(c_1679,plain,(
    r2_hidden('#skF_7',a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1624,c_141])).

tff(c_1891,plain,(
    ! [A_3805,B_3806,C_3807] :
      ( '#skF_3'(A_3805,B_3806,C_3807) = A_3805
      | ~ r2_hidden(A_3805,a_2_0_orders_2(B_3806,C_3807))
      | ~ m1_subset_1(C_3807,k1_zfmisc_1(u1_struct_0(B_3806)))
      | ~ l1_orders_2(B_3806)
      | ~ v5_orders_2(B_3806)
      | ~ v4_orders_2(B_3806)
      | ~ v3_orders_2(B_3806)
      | v2_struct_0(B_3806) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1893,plain,
    ( '#skF_3'('#skF_7','#skF_5',k1_tarski('#skF_6')) = '#skF_7'
    | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1679,c_1891])).

tff(c_1902,plain,
    ( '#skF_3'('#skF_7','#skF_5',k1_tarski('#skF_6')) = '#skF_7'
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_177,c_1893])).

tff(c_1903,plain,(
    '#skF_3'('#skF_7','#skF_5',k1_tarski('#skF_6')) = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1902])).

tff(c_4362,plain,(
    ! [B_5941,E_5942,A_5943,C_5944] :
      ( r2_orders_2(B_5941,E_5942,'#skF_3'(A_5943,B_5941,C_5944))
      | ~ r2_hidden(E_5942,C_5944)
      | ~ m1_subset_1(E_5942,u1_struct_0(B_5941))
      | ~ r2_hidden(A_5943,a_2_0_orders_2(B_5941,C_5944))
      | ~ m1_subset_1(C_5944,k1_zfmisc_1(u1_struct_0(B_5941)))
      | ~ l1_orders_2(B_5941)
      | ~ v5_orders_2(B_5941)
      | ~ v4_orders_2(B_5941)
      | ~ v3_orders_2(B_5941)
      | v2_struct_0(B_5941) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4370,plain,(
    ! [E_5942,A_5943] :
      ( r2_orders_2('#skF_5',E_5942,'#skF_3'(A_5943,'#skF_5',k1_tarski('#skF_6')))
      | ~ r2_hidden(E_5942,k1_tarski('#skF_6'))
      | ~ m1_subset_1(E_5942,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_5943,a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_177,c_4362])).

tff(c_4381,plain,(
    ! [E_5942,A_5943] :
      ( r2_orders_2('#skF_5',E_5942,'#skF_3'(A_5943,'#skF_5',k1_tarski('#skF_6')))
      | ~ r2_hidden(E_5942,k1_tarski('#skF_6'))
      | ~ m1_subset_1(E_5942,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_5943,a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_4370])).

tff(c_4765,plain,(
    ! [E_6452,A_6453] :
      ( r2_orders_2('#skF_5',E_6452,'#skF_3'(A_6453,'#skF_5',k1_tarski('#skF_6')))
      | ~ r2_hidden(E_6452,k1_tarski('#skF_6'))
      | ~ m1_subset_1(E_6452,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_6453,a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4381])).

tff(c_4771,plain,(
    ! [E_6452] :
      ( r2_orders_2('#skF_5',E_6452,'#skF_7')
      | ~ r2_hidden(E_6452,k1_tarski('#skF_6'))
      | ~ m1_subset_1(E_6452,u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_7',a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1903,c_4765])).

tff(c_4813,plain,(
    ! [E_6526] :
      ( r2_orders_2('#skF_5',E_6526,'#skF_7')
      | ~ r2_hidden(E_6526,k1_tarski('#skF_6'))
      | ~ m1_subset_1(E_6526,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1679,c_4771])).

tff(c_4828,plain,
    ( r2_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_76,c_4813])).

tff(c_4833,plain,(
    r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4828])).

tff(c_4835,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_4833])).

tff(c_4836,plain,(
    ~ r2_hidden('#skF_7',k1_orders_2('#skF_5',k1_tarski('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_4839,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_4836])).

tff(c_4840,plain,(
    r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_4862,plain,(
    ~ r2_hidden('#skF_7',k1_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4840,c_60])).

tff(c_4910,plain,(
    ~ r2_hidden('#skF_7',k1_orders_2('#skF_5',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4909,c_4862])).

tff(c_6369,plain,(
    ~ r2_hidden('#skF_7',a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6363,c_4910])).

tff(c_7051,plain,(
    ! [D_10840,B_10841,C_10842] :
      ( r2_hidden('#skF_4'(D_10840,B_10841,C_10842,D_10840),C_10842)
      | r2_hidden(D_10840,a_2_0_orders_2(B_10841,C_10842))
      | ~ m1_subset_1(D_10840,u1_struct_0(B_10841))
      | ~ m1_subset_1(C_10842,k1_zfmisc_1(u1_struct_0(B_10841)))
      | ~ l1_orders_2(B_10841)
      | ~ v5_orders_2(B_10841)
      | ~ v4_orders_2(B_10841)
      | ~ v3_orders_2(B_10841)
      | v2_struct_0(B_10841) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_7059,plain,(
    ! [D_10840] :
      ( r2_hidden('#skF_4'(D_10840,'#skF_5',k1_tarski('#skF_6'),D_10840),k1_tarski('#skF_6'))
      | r2_hidden(D_10840,a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
      | ~ m1_subset_1(D_10840,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4951,c_7051])).

tff(c_7066,plain,(
    ! [D_10840] :
      ( r2_hidden('#skF_4'(D_10840,'#skF_5',k1_tarski('#skF_6'),D_10840),k1_tarski('#skF_6'))
      | r2_hidden(D_10840,a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
      | ~ m1_subset_1(D_10840,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_7059])).

tff(c_8162,plain,(
    ! [D_12090] :
      ( r2_hidden('#skF_4'(D_12090,'#skF_5',k1_tarski('#skF_6'),D_12090),k1_tarski('#skF_6'))
      | r2_hidden(D_12090,a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
      | ~ m1_subset_1(D_12090,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_7066])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4863,plain,(
    ! [D_6604,B_6605,A_6606] :
      ( D_6604 = B_6605
      | D_6604 = A_6606
      | ~ r2_hidden(D_6604,k2_tarski(A_6606,B_6605)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4869,plain,(
    ! [D_6604,A_7] :
      ( D_6604 = A_7
      | D_6604 = A_7
      | ~ r2_hidden(D_6604,k1_tarski(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_4863])).

tff(c_8251,plain,(
    ! [D_12163] :
      ( '#skF_4'(D_12163,'#skF_5',k1_tarski('#skF_6'),D_12163) = '#skF_6'
      | r2_hidden(D_12163,a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
      | ~ m1_subset_1(D_12163,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_8162,c_4869])).

tff(c_8273,plain,
    ( '#skF_4'('#skF_7','#skF_5',k1_tarski('#skF_6'),'#skF_7') = '#skF_6'
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_8251,c_6369])).

tff(c_8371,plain,(
    '#skF_4'('#skF_7','#skF_5',k1_tarski('#skF_6'),'#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8273])).

tff(c_28,plain,(
    ! [B_14,D_24,C_15] :
      ( ~ r2_orders_2(B_14,'#skF_4'(D_24,B_14,C_15,D_24),D_24)
      | r2_hidden(D_24,a_2_0_orders_2(B_14,C_15))
      | ~ m1_subset_1(D_24,u1_struct_0(B_14))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(u1_struct_0(B_14)))
      | ~ l1_orders_2(B_14)
      | ~ v5_orders_2(B_14)
      | ~ v4_orders_2(B_14)
      | ~ v3_orders_2(B_14)
      | v2_struct_0(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_8382,plain,
    ( ~ r2_orders_2('#skF_5','#skF_6','#skF_7')
    | r2_hidden('#skF_7',a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_8371,c_28])).

tff(c_8428,plain,
    ( r2_hidden('#skF_7',a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_4951,c_46,c_4840,c_8382])).

tff(c_8430,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_6369,c_8428])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:01:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.62/2.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.62/2.31  
% 6.62/2.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.62/2.32  %$ r2_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 6.62/2.32  
% 6.62/2.32  %Foreground sorts:
% 6.62/2.32  
% 6.62/2.32  
% 6.62/2.32  %Background operators:
% 6.62/2.32  
% 6.62/2.32  
% 6.62/2.32  %Foreground operators:
% 6.62/2.32  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.62/2.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.62/2.32  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 6.62/2.32  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 6.62/2.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.62/2.32  tff(a_2_0_orders_2, type, a_2_0_orders_2: ($i * $i) > $i).
% 6.62/2.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.62/2.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.62/2.32  tff('#skF_7', type, '#skF_7': $i).
% 6.62/2.32  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 6.62/2.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.62/2.32  tff('#skF_5', type, '#skF_5': $i).
% 6.62/2.32  tff('#skF_6', type, '#skF_6': $i).
% 6.62/2.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.62/2.32  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 6.62/2.32  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 6.62/2.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.62/2.32  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.62/2.32  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 6.62/2.32  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 6.62/2.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.62/2.32  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.62/2.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.62/2.32  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 6.62/2.32  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 6.62/2.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.62/2.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.62/2.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.62/2.32  
% 6.62/2.34  tff(f_134, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> r2_hidden(C, k1_orders_2(A, k6_domain_1(u1_struct_0(A), B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_orders_2)).
% 6.62/2.34  tff(f_64, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 6.62/2.34  tff(f_98, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 6.62/2.34  tff(f_44, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 6.62/2.34  tff(f_112, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v6_orders_2(k6_domain_1(u1_struct_0(A), B), A) & m1_subset_1(k6_domain_1(u1_struct_0(A), B), k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_orders_2)).
% 6.62/2.34  tff(f_60, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_orders_2(A, B) = a_2_0_orders_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_orders_2)).
% 6.62/2.34  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.62/2.34  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 6.62/2.34  tff(f_91, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_0_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, E, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 6.62/2.34  tff(c_58, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.62/2.34  tff(c_56, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.62/2.34  tff(c_54, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.62/2.34  tff(c_52, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.62/2.34  tff(c_50, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.62/2.34  tff(c_48, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.62/2.34  tff(c_26, plain, (![A_12]: (l1_struct_0(A_12) | ~l1_orders_2(A_12))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.62/2.34  tff(c_46, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.62/2.34  tff(c_4883, plain, (![A_6609, B_6610]: (k6_domain_1(A_6609, B_6610)=k1_tarski(B_6610) | ~m1_subset_1(B_6610, A_6609) | v1_xboole_0(A_6609))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.62/2.34  tff(c_4890, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')=k1_tarski('#skF_7') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_46, c_4883])).
% 6.62/2.34  tff(c_4892, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_4890])).
% 6.62/2.34  tff(c_22, plain, (![A_8]: (~v1_xboole_0(u1_struct_0(A_8)) | ~l1_struct_0(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.62/2.34  tff(c_4896, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_4892, c_22])).
% 6.62/2.34  tff(c_4899, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_58, c_4896])).
% 6.62/2.34  tff(c_4902, plain, (~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_26, c_4899])).
% 6.62/2.34  tff(c_4906, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_4902])).
% 6.62/2.34  tff(c_4908, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_4890])).
% 6.62/2.34  tff(c_4891, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_48, c_4883])).
% 6.62/2.34  tff(c_4909, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_4908, c_4891])).
% 6.62/2.34  tff(c_4935, plain, (![A_6625, B_6626]: (m1_subset_1(k6_domain_1(u1_struct_0(A_6625), B_6626), k1_zfmisc_1(u1_struct_0(A_6625))) | ~m1_subset_1(B_6626, u1_struct_0(A_6625)) | ~l1_orders_2(A_6625) | ~v3_orders_2(A_6625) | v2_struct_0(A_6625))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.62/2.34  tff(c_4944, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4909, c_4935])).
% 6.62/2.34  tff(c_4950, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_50, c_48, c_4944])).
% 6.62/2.34  tff(c_4951, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_4950])).
% 6.62/2.34  tff(c_6344, plain, (![A_9809, B_9810]: (k1_orders_2(A_9809, B_9810)=a_2_0_orders_2(A_9809, B_9810) | ~m1_subset_1(B_9810, k1_zfmisc_1(u1_struct_0(A_9809))) | ~l1_orders_2(A_9809) | ~v5_orders_2(A_9809) | ~v4_orders_2(A_9809) | ~v3_orders_2(A_9809) | v2_struct_0(A_9809))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.62/2.34  tff(c_6353, plain, (k1_orders_2('#skF_5', k1_tarski('#skF_6'))=a_2_0_orders_2('#skF_5', k1_tarski('#skF_6')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_4951, c_6344])).
% 6.62/2.34  tff(c_6362, plain, (k1_orders_2('#skF_5', k1_tarski('#skF_6'))=a_2_0_orders_2('#skF_5', k1_tarski('#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_6353])).
% 6.62/2.34  tff(c_6363, plain, (k1_orders_2('#skF_5', k1_tarski('#skF_6'))=a_2_0_orders_2('#skF_5', k1_tarski('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_58, c_6362])).
% 6.62/2.34  tff(c_109, plain, (![A_48, B_49]: (k6_domain_1(A_48, B_49)=k1_tarski(B_49) | ~m1_subset_1(B_49, A_48) | v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.62/2.34  tff(c_116, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')=k1_tarski('#skF_7') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_46, c_109])).
% 6.62/2.34  tff(c_118, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_116])).
% 6.62/2.34  tff(c_123, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_118, c_22])).
% 6.62/2.34  tff(c_126, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_58, c_123])).
% 6.62/2.34  tff(c_129, plain, (~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_26, c_126])).
% 6.62/2.34  tff(c_133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_129])).
% 6.62/2.34  tff(c_135, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_116])).
% 6.62/2.34  tff(c_117, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_48, c_109])).
% 6.62/2.34  tff(c_140, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_135, c_117])).
% 6.62/2.34  tff(c_66, plain, (r2_orders_2('#skF_5', '#skF_6', '#skF_7') | r2_hidden('#skF_7', k1_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.62/2.34  tff(c_69, plain, (r2_hidden('#skF_7', k1_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')))), inference(splitLeft, [status(thm)], [c_66])).
% 6.62/2.34  tff(c_141, plain, (r2_hidden('#skF_7', k1_orders_2('#skF_5', k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_69])).
% 6.62/2.34  tff(c_60, plain, (~r2_hidden('#skF_7', k1_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_6'))) | ~r2_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.62/2.34  tff(c_146, plain, (~r2_hidden('#skF_7', k1_orders_2('#skF_5', k1_tarski('#skF_6'))) | ~r2_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_60])).
% 6.62/2.34  tff(c_147, plain, (~r2_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_146])).
% 6.62/2.34  tff(c_70, plain, (![A_38]: (k2_tarski(A_38, A_38)=k1_tarski(A_38))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.62/2.34  tff(c_6, plain, (![D_6, B_2]: (r2_hidden(D_6, k2_tarski(D_6, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.62/2.34  tff(c_76, plain, (![A_38]: (r2_hidden(A_38, k1_tarski(A_38)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_6])).
% 6.62/2.34  tff(c_164, plain, (![A_61, B_62]: (m1_subset_1(k6_domain_1(u1_struct_0(A_61), B_62), k1_zfmisc_1(u1_struct_0(A_61))) | ~m1_subset_1(B_62, u1_struct_0(A_61)) | ~l1_orders_2(A_61) | ~v3_orders_2(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.62/2.34  tff(c_170, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_140, c_164])).
% 6.62/2.34  tff(c_176, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_50, c_48, c_170])).
% 6.62/2.34  tff(c_177, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_176])).
% 6.62/2.34  tff(c_1601, plain, (![A_3366, B_3367]: (k1_orders_2(A_3366, B_3367)=a_2_0_orders_2(A_3366, B_3367) | ~m1_subset_1(B_3367, k1_zfmisc_1(u1_struct_0(A_3366))) | ~l1_orders_2(A_3366) | ~v5_orders_2(A_3366) | ~v4_orders_2(A_3366) | ~v3_orders_2(A_3366) | v2_struct_0(A_3366))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.62/2.34  tff(c_1611, plain, (k1_orders_2('#skF_5', k1_tarski('#skF_6'))=a_2_0_orders_2('#skF_5', k1_tarski('#skF_6')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_177, c_1601])).
% 6.62/2.34  tff(c_1623, plain, (k1_orders_2('#skF_5', k1_tarski('#skF_6'))=a_2_0_orders_2('#skF_5', k1_tarski('#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_1611])).
% 6.62/2.34  tff(c_1624, plain, (k1_orders_2('#skF_5', k1_tarski('#skF_6'))=a_2_0_orders_2('#skF_5', k1_tarski('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_58, c_1623])).
% 6.62/2.34  tff(c_1679, plain, (r2_hidden('#skF_7', a_2_0_orders_2('#skF_5', k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_1624, c_141])).
% 6.62/2.34  tff(c_1891, plain, (![A_3805, B_3806, C_3807]: ('#skF_3'(A_3805, B_3806, C_3807)=A_3805 | ~r2_hidden(A_3805, a_2_0_orders_2(B_3806, C_3807)) | ~m1_subset_1(C_3807, k1_zfmisc_1(u1_struct_0(B_3806))) | ~l1_orders_2(B_3806) | ~v5_orders_2(B_3806) | ~v4_orders_2(B_3806) | ~v3_orders_2(B_3806) | v2_struct_0(B_3806))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.62/2.34  tff(c_1893, plain, ('#skF_3'('#skF_7', '#skF_5', k1_tarski('#skF_6'))='#skF_7' | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1679, c_1891])).
% 6.62/2.34  tff(c_1902, plain, ('#skF_3'('#skF_7', '#skF_5', k1_tarski('#skF_6'))='#skF_7' | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_177, c_1893])).
% 6.62/2.34  tff(c_1903, plain, ('#skF_3'('#skF_7', '#skF_5', k1_tarski('#skF_6'))='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_58, c_1902])).
% 6.62/2.34  tff(c_4362, plain, (![B_5941, E_5942, A_5943, C_5944]: (r2_orders_2(B_5941, E_5942, '#skF_3'(A_5943, B_5941, C_5944)) | ~r2_hidden(E_5942, C_5944) | ~m1_subset_1(E_5942, u1_struct_0(B_5941)) | ~r2_hidden(A_5943, a_2_0_orders_2(B_5941, C_5944)) | ~m1_subset_1(C_5944, k1_zfmisc_1(u1_struct_0(B_5941))) | ~l1_orders_2(B_5941) | ~v5_orders_2(B_5941) | ~v4_orders_2(B_5941) | ~v3_orders_2(B_5941) | v2_struct_0(B_5941))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.62/2.34  tff(c_4370, plain, (![E_5942, A_5943]: (r2_orders_2('#skF_5', E_5942, '#skF_3'(A_5943, '#skF_5', k1_tarski('#skF_6'))) | ~r2_hidden(E_5942, k1_tarski('#skF_6')) | ~m1_subset_1(E_5942, u1_struct_0('#skF_5')) | ~r2_hidden(A_5943, a_2_0_orders_2('#skF_5', k1_tarski('#skF_6'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_177, c_4362])).
% 6.62/2.34  tff(c_4381, plain, (![E_5942, A_5943]: (r2_orders_2('#skF_5', E_5942, '#skF_3'(A_5943, '#skF_5', k1_tarski('#skF_6'))) | ~r2_hidden(E_5942, k1_tarski('#skF_6')) | ~m1_subset_1(E_5942, u1_struct_0('#skF_5')) | ~r2_hidden(A_5943, a_2_0_orders_2('#skF_5', k1_tarski('#skF_6'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_4370])).
% 6.62/2.34  tff(c_4765, plain, (![E_6452, A_6453]: (r2_orders_2('#skF_5', E_6452, '#skF_3'(A_6453, '#skF_5', k1_tarski('#skF_6'))) | ~r2_hidden(E_6452, k1_tarski('#skF_6')) | ~m1_subset_1(E_6452, u1_struct_0('#skF_5')) | ~r2_hidden(A_6453, a_2_0_orders_2('#skF_5', k1_tarski('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_4381])).
% 6.62/2.34  tff(c_4771, plain, (![E_6452]: (r2_orders_2('#skF_5', E_6452, '#skF_7') | ~r2_hidden(E_6452, k1_tarski('#skF_6')) | ~m1_subset_1(E_6452, u1_struct_0('#skF_5')) | ~r2_hidden('#skF_7', a_2_0_orders_2('#skF_5', k1_tarski('#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_1903, c_4765])).
% 6.62/2.34  tff(c_4813, plain, (![E_6526]: (r2_orders_2('#skF_5', E_6526, '#skF_7') | ~r2_hidden(E_6526, k1_tarski('#skF_6')) | ~m1_subset_1(E_6526, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_1679, c_4771])).
% 6.62/2.34  tff(c_4828, plain, (r2_orders_2('#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_76, c_4813])).
% 6.62/2.34  tff(c_4833, plain, (r2_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4828])).
% 6.62/2.34  tff(c_4835, plain, $false, inference(negUnitSimplification, [status(thm)], [c_147, c_4833])).
% 6.62/2.34  tff(c_4836, plain, (~r2_hidden('#skF_7', k1_orders_2('#skF_5', k1_tarski('#skF_6')))), inference(splitRight, [status(thm)], [c_146])).
% 6.62/2.34  tff(c_4839, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141, c_4836])).
% 6.62/2.34  tff(c_4840, plain, (r2_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_66])).
% 6.62/2.34  tff(c_4862, plain, (~r2_hidden('#skF_7', k1_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_4840, c_60])).
% 6.62/2.34  tff(c_4910, plain, (~r2_hidden('#skF_7', k1_orders_2('#skF_5', k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_4909, c_4862])).
% 6.62/2.34  tff(c_6369, plain, (~r2_hidden('#skF_7', a_2_0_orders_2('#skF_5', k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_6363, c_4910])).
% 6.62/2.34  tff(c_7051, plain, (![D_10840, B_10841, C_10842]: (r2_hidden('#skF_4'(D_10840, B_10841, C_10842, D_10840), C_10842) | r2_hidden(D_10840, a_2_0_orders_2(B_10841, C_10842)) | ~m1_subset_1(D_10840, u1_struct_0(B_10841)) | ~m1_subset_1(C_10842, k1_zfmisc_1(u1_struct_0(B_10841))) | ~l1_orders_2(B_10841) | ~v5_orders_2(B_10841) | ~v4_orders_2(B_10841) | ~v3_orders_2(B_10841) | v2_struct_0(B_10841))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.62/2.34  tff(c_7059, plain, (![D_10840]: (r2_hidden('#skF_4'(D_10840, '#skF_5', k1_tarski('#skF_6'), D_10840), k1_tarski('#skF_6')) | r2_hidden(D_10840, a_2_0_orders_2('#skF_5', k1_tarski('#skF_6'))) | ~m1_subset_1(D_10840, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_4951, c_7051])).
% 6.62/2.34  tff(c_7066, plain, (![D_10840]: (r2_hidden('#skF_4'(D_10840, '#skF_5', k1_tarski('#skF_6'), D_10840), k1_tarski('#skF_6')) | r2_hidden(D_10840, a_2_0_orders_2('#skF_5', k1_tarski('#skF_6'))) | ~m1_subset_1(D_10840, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_7059])).
% 6.62/2.34  tff(c_8162, plain, (![D_12090]: (r2_hidden('#skF_4'(D_12090, '#skF_5', k1_tarski('#skF_6'), D_12090), k1_tarski('#skF_6')) | r2_hidden(D_12090, a_2_0_orders_2('#skF_5', k1_tarski('#skF_6'))) | ~m1_subset_1(D_12090, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_7066])).
% 6.62/2.34  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.62/2.34  tff(c_4863, plain, (![D_6604, B_6605, A_6606]: (D_6604=B_6605 | D_6604=A_6606 | ~r2_hidden(D_6604, k2_tarski(A_6606, B_6605)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.62/2.34  tff(c_4869, plain, (![D_6604, A_7]: (D_6604=A_7 | D_6604=A_7 | ~r2_hidden(D_6604, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_4863])).
% 6.62/2.34  tff(c_8251, plain, (![D_12163]: ('#skF_4'(D_12163, '#skF_5', k1_tarski('#skF_6'), D_12163)='#skF_6' | r2_hidden(D_12163, a_2_0_orders_2('#skF_5', k1_tarski('#skF_6'))) | ~m1_subset_1(D_12163, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_8162, c_4869])).
% 6.62/2.34  tff(c_8273, plain, ('#skF_4'('#skF_7', '#skF_5', k1_tarski('#skF_6'), '#skF_7')='#skF_6' | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_8251, c_6369])).
% 6.62/2.34  tff(c_8371, plain, ('#skF_4'('#skF_7', '#skF_5', k1_tarski('#skF_6'), '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8273])).
% 6.62/2.34  tff(c_28, plain, (![B_14, D_24, C_15]: (~r2_orders_2(B_14, '#skF_4'(D_24, B_14, C_15, D_24), D_24) | r2_hidden(D_24, a_2_0_orders_2(B_14, C_15)) | ~m1_subset_1(D_24, u1_struct_0(B_14)) | ~m1_subset_1(C_15, k1_zfmisc_1(u1_struct_0(B_14))) | ~l1_orders_2(B_14) | ~v5_orders_2(B_14) | ~v4_orders_2(B_14) | ~v3_orders_2(B_14) | v2_struct_0(B_14))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.62/2.34  tff(c_8382, plain, (~r2_orders_2('#skF_5', '#skF_6', '#skF_7') | r2_hidden('#skF_7', a_2_0_orders_2('#skF_5', k1_tarski('#skF_6'))) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_8371, c_28])).
% 6.62/2.34  tff(c_8428, plain, (r2_hidden('#skF_7', a_2_0_orders_2('#skF_5', k1_tarski('#skF_6'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_4951, c_46, c_4840, c_8382])).
% 6.62/2.34  tff(c_8430, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_6369, c_8428])).
% 6.62/2.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.62/2.34  
% 6.62/2.34  Inference rules
% 6.62/2.34  ----------------------
% 6.62/2.34  #Ref     : 0
% 6.62/2.34  #Sup     : 1102
% 6.62/2.34  #Fact    : 36
% 6.62/2.34  #Define  : 0
% 6.62/2.34  #Split   : 28
% 6.62/2.34  #Chain   : 0
% 6.62/2.34  #Close   : 0
% 6.62/2.34  
% 6.62/2.34  Ordering : KBO
% 6.62/2.34  
% 6.62/2.34  Simplification rules
% 6.62/2.34  ----------------------
% 6.62/2.34  #Subsume      : 389
% 6.62/2.34  #Demod        : 425
% 6.62/2.34  #Tautology    : 324
% 6.62/2.34  #SimpNegUnit  : 68
% 6.62/2.34  #BackRed      : 4
% 6.62/2.34  
% 6.62/2.34  #Partial instantiations: 7014
% 6.62/2.34  #Strategies tried      : 1
% 6.62/2.34  
% 6.62/2.34  Timing (in seconds)
% 6.62/2.34  ----------------------
% 6.62/2.34  Preprocessing        : 0.33
% 6.62/2.34  Parsing              : 0.17
% 6.62/2.34  CNF conversion       : 0.02
% 6.62/2.34  Main loop            : 1.23
% 6.62/2.34  Inferencing          : 0.61
% 6.62/2.34  Reduction            : 0.28
% 6.62/2.34  Demodulation         : 0.20
% 6.62/2.34  BG Simplification    : 0.05
% 6.62/2.34  Subsumption          : 0.21
% 6.62/2.34  Abstraction          : 0.06
% 6.62/2.34  MUC search           : 0.00
% 6.62/2.34  Cooper               : 0.00
% 6.62/2.34  Total                : 1.60
% 6.62/2.34  Index Insertion      : 0.00
% 6.62/2.34  Index Deletion       : 0.00
% 6.62/2.34  Index Matching       : 0.00
% 6.62/2.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
