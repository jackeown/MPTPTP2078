%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:41 EST 2020

% Result     : Theorem 4.83s
% Output     : CNFRefutation 5.16s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 458 expanded)
%              Number of leaves         :   35 ( 172 expanded)
%              Depth                    :   19
%              Number of atoms          :  259 (1608 expanded)
%              Number of equality atoms :   29 ( 138 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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
                <=> r2_hidden(C,k1_orders_2(A,k6_domain_1(u1_struct_0(A),B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_orders_2)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_110,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_49,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_orders_2(A,B) = a_2_0_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_orders_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_103,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

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

tff(c_24,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_orders_2(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_40,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_792,plain,(
    ! [A_120,B_121] :
      ( k6_domain_1(A_120,B_121) = k1_tarski(B_121)
      | ~ m1_subset_1(B_121,A_120)
      | v1_xboole_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_799,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_40,c_792])).

tff(c_809,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_799])).

tff(c_18,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(u1_struct_0(A_10))
      | ~ l1_struct_0(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_812,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_809,c_18])).

tff(c_815,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_812])).

tff(c_818,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_815])).

tff(c_822,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_818])).

tff(c_824,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_799])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_800,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_42,c_792])).

tff(c_825,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_800])).

tff(c_826,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_824,c_825])).

tff(c_827,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_800])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k6_domain_1(A_14,B_15),k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,A_14)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_844,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_827,c_22])).

tff(c_848,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_844])).

tff(c_849,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_824,c_848])).

tff(c_879,plain,(
    ! [A_132,B_133] :
      ( k1_orders_2(A_132,B_133) = a_2_0_orders_2(A_132,B_133)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_orders_2(A_132)
      | ~ v5_orders_2(A_132)
      | ~ v4_orders_2(A_132)
      | ~ v3_orders_2(A_132)
      | v2_struct_0(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_882,plain,
    ( k1_orders_2('#skF_5',k1_tarski('#skF_6')) = a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_849,c_879])).

tff(c_892,plain,
    ( k1_orders_2('#skF_5',k1_tarski('#skF_6')) = a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_882])).

tff(c_893,plain,(
    k1_orders_2('#skF_5',k1_tarski('#skF_6')) = a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_892])).

tff(c_54,plain,
    ( ~ r2_hidden('#skF_7',k1_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_6')))
    | ~ r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_63,plain,(
    ~ r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_81,plain,(
    ! [A_45,B_46] :
      ( k6_domain_1(A_45,B_46) = k1_tarski(B_46)
      | ~ m1_subset_1(B_46,A_45)
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_88,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_40,c_81])).

tff(c_90,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_93,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_18])).

tff(c_96,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_93])).

tff(c_99,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_96])).

tff(c_103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_99])).

tff(c_105,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_89,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_42,c_81])).

tff(c_111,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_89])).

tff(c_117,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1(k6_domain_1(A_47,B_48),k1_zfmisc_1(A_47))
      | ~ m1_subset_1(B_48,A_47)
      | v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_125,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_117])).

tff(c_132,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_125])).

tff(c_133,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_132])).

tff(c_190,plain,(
    ! [A_59,B_60] :
      ( k1_orders_2(A_59,B_60) = a_2_0_orders_2(A_59,B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_orders_2(A_59)
      | ~ v5_orders_2(A_59)
      | ~ v4_orders_2(A_59)
      | ~ v3_orders_2(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_196,plain,
    ( k1_orders_2('#skF_5',k1_tarski('#skF_6')) = a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_133,c_190])).

tff(c_207,plain,
    ( k1_orders_2('#skF_5',k1_tarski('#skF_6')) = a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_196])).

tff(c_208,plain,(
    k1_orders_2('#skF_5',k1_tarski('#skF_6')) = a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_207])).

tff(c_60,plain,
    ( r2_orders_2('#skF_5','#skF_6','#skF_7')
    | r2_hidden('#skF_7',k1_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_106,plain,(
    r2_hidden('#skF_7',k1_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_60])).

tff(c_112,plain,(
    r2_hidden('#skF_7',k1_orders_2('#skF_5',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_106])).

tff(c_214,plain,(
    r2_hidden('#skF_7',a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_112])).

tff(c_219,plain,(
    ! [A_61,B_62,C_63] :
      ( '#skF_3'(A_61,B_62,C_63) = A_61
      | ~ r2_hidden(A_61,a_2_0_orders_2(B_62,C_63))
      | ~ m1_subset_1(C_63,k1_zfmisc_1(u1_struct_0(B_62)))
      | ~ l1_orders_2(B_62)
      | ~ v5_orders_2(B_62)
      | ~ v4_orders_2(B_62)
      | ~ v3_orders_2(B_62)
      | v2_struct_0(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_221,plain,
    ( '#skF_3'('#skF_7','#skF_5',k1_tarski('#skF_6')) = '#skF_7'
    | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_214,c_219])).

tff(c_230,plain,
    ( '#skF_3'('#skF_7','#skF_5',k1_tarski('#skF_6')) = '#skF_7'
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_133,c_221])).

tff(c_231,plain,(
    '#skF_3'('#skF_7','#skF_5',k1_tarski('#skF_6')) = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_230])).

tff(c_684,plain,(
    ! [B_100,E_101,A_102,C_103] :
      ( r2_orders_2(B_100,E_101,'#skF_3'(A_102,B_100,C_103))
      | ~ r2_hidden(E_101,C_103)
      | ~ m1_subset_1(E_101,u1_struct_0(B_100))
      | ~ r2_hidden(A_102,a_2_0_orders_2(B_100,C_103))
      | ~ m1_subset_1(C_103,k1_zfmisc_1(u1_struct_0(B_100)))
      | ~ l1_orders_2(B_100)
      | ~ v5_orders_2(B_100)
      | ~ v4_orders_2(B_100)
      | ~ v3_orders_2(B_100)
      | v2_struct_0(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_688,plain,(
    ! [E_101,A_102] :
      ( r2_orders_2('#skF_5',E_101,'#skF_3'(A_102,'#skF_5',k1_tarski('#skF_6')))
      | ~ r2_hidden(E_101,k1_tarski('#skF_6'))
      | ~ m1_subset_1(E_101,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_102,a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_133,c_684])).

tff(c_698,plain,(
    ! [E_101,A_102] :
      ( r2_orders_2('#skF_5',E_101,'#skF_3'(A_102,'#skF_5',k1_tarski('#skF_6')))
      | ~ r2_hidden(E_101,k1_tarski('#skF_6'))
      | ~ m1_subset_1(E_101,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_102,a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_688])).

tff(c_709,plain,(
    ! [E_106,A_107] :
      ( r2_orders_2('#skF_5',E_106,'#skF_3'(A_107,'#skF_5',k1_tarski('#skF_6')))
      | ~ r2_hidden(E_106,k1_tarski('#skF_6'))
      | ~ m1_subset_1(E_106,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_107,a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_698])).

tff(c_721,plain,(
    ! [E_106] :
      ( r2_orders_2('#skF_5',E_106,'#skF_7')
      | ~ r2_hidden(E_106,k1_tarski('#skF_6'))
      | ~ m1_subset_1(E_106,u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_7',a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_709])).

tff(c_728,plain,(
    ! [E_108] :
      ( r2_orders_2('#skF_5',E_108,'#skF_7')
      | ~ r2_hidden(E_108,k1_tarski('#skF_6'))
      | ~ m1_subset_1(E_108,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_721])).

tff(c_743,plain,
    ( r2_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_4,c_728])).

tff(c_749,plain,(
    r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_743])).

tff(c_751,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_749])).

tff(c_752,plain,(
    ~ r2_hidden('#skF_7',k1_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_840,plain,(
    ~ r2_hidden('#skF_7',k1_orders_2('#skF_5',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_827,c_752])).

tff(c_899,plain,(
    ~ r2_hidden('#skF_7',a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_893,c_840])).

tff(c_753,plain,(
    r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1021,plain,(
    ! [D_150,B_151,C_152] :
      ( r2_hidden('#skF_4'(D_150,B_151,C_152,D_150),C_152)
      | r2_hidden(D_150,a_2_0_orders_2(B_151,C_152))
      | ~ m1_subset_1(D_150,u1_struct_0(B_151))
      | ~ m1_subset_1(C_152,k1_zfmisc_1(u1_struct_0(B_151)))
      | ~ l1_orders_2(B_151)
      | ~ v5_orders_2(B_151)
      | ~ v4_orders_2(B_151)
      | ~ v3_orders_2(B_151)
      | v2_struct_0(B_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1023,plain,(
    ! [D_150] :
      ( r2_hidden('#skF_4'(D_150,'#skF_5',k1_tarski('#skF_6'),D_150),k1_tarski('#skF_6'))
      | r2_hidden(D_150,a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
      | ~ m1_subset_1(D_150,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_849,c_1021])).

tff(c_1031,plain,(
    ! [D_150] :
      ( r2_hidden('#skF_4'(D_150,'#skF_5',k1_tarski('#skF_6'),D_150),k1_tarski('#skF_6'))
      | r2_hidden(D_150,a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
      | ~ m1_subset_1(D_150,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_1023])).

tff(c_1038,plain,(
    ! [D_153] :
      ( r2_hidden('#skF_4'(D_153,'#skF_5',k1_tarski('#skF_6'),D_153),k1_tarski('#skF_6'))
      | r2_hidden(D_153,a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
      | ~ m1_subset_1(D_153,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1031])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1048,plain,(
    ! [D_155] :
      ( '#skF_4'(D_155,'#skF_5',k1_tarski('#skF_6'),D_155) = '#skF_6'
      | r2_hidden(D_155,a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
      | ~ m1_subset_1(D_155,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1038,c_2])).

tff(c_1059,plain,
    ( '#skF_4'('#skF_7','#skF_5',k1_tarski('#skF_6'),'#skF_7') = '#skF_6'
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1048,c_899])).

tff(c_1073,plain,(
    '#skF_4'('#skF_7','#skF_5',k1_tarski('#skF_6'),'#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1059])).

tff(c_1267,plain,(
    ! [B_164,D_165,C_166] :
      ( ~ r2_orders_2(B_164,'#skF_4'(D_165,B_164,C_166,D_165),D_165)
      | r2_hidden(D_165,a_2_0_orders_2(B_164,C_166))
      | ~ m1_subset_1(D_165,u1_struct_0(B_164))
      | ~ m1_subset_1(C_166,k1_zfmisc_1(u1_struct_0(B_164)))
      | ~ l1_orders_2(B_164)
      | ~ v5_orders_2(B_164)
      | ~ v4_orders_2(B_164)
      | ~ v3_orders_2(B_164)
      | v2_struct_0(B_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1277,plain,
    ( ~ r2_orders_2('#skF_5','#skF_6','#skF_7')
    | r2_hidden('#skF_7',a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1073,c_1267])).

tff(c_1293,plain,
    ( r2_hidden('#skF_7',a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_849,c_40,c_753,c_1277])).

tff(c_1295,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_899,c_1293])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:32:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.83/2.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.83/2.27  
% 4.83/2.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.83/2.28  %$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 4.83/2.28  
% 4.83/2.28  %Foreground sorts:
% 4.83/2.28  
% 4.83/2.28  
% 4.83/2.28  %Background operators:
% 4.83/2.28  
% 4.83/2.28  
% 4.83/2.28  %Foreground operators:
% 4.83/2.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.83/2.28  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.83/2.28  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 4.83/2.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.83/2.28  tff(a_2_0_orders_2, type, a_2_0_orders_2: ($i * $i) > $i).
% 4.83/2.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.83/2.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.83/2.28  tff('#skF_7', type, '#skF_7': $i).
% 4.83/2.28  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.83/2.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.83/2.28  tff('#skF_5', type, '#skF_5': $i).
% 4.83/2.28  tff('#skF_6', type, '#skF_6': $i).
% 4.83/2.28  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.83/2.28  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.83/2.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.83/2.28  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.83/2.28  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 4.83/2.28  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.83/2.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.83/2.28  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.83/2.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.83/2.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.83/2.28  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 4.83/2.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.83/2.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.83/2.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.83/2.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.83/2.28  
% 5.16/2.31  tff(f_132, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> r2_hidden(C, k1_orders_2(A, k6_domain_1(u1_struct_0(A), B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_orders_2)).
% 5.16/2.31  tff(f_76, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 5.16/2.31  tff(f_110, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 5.16/2.31  tff(f_49, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 5.16/2.31  tff(f_72, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 5.16/2.31  tff(f_65, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_orders_2(A, B) = a_2_0_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_orders_2)).
% 5.16/2.31  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 5.16/2.31  tff(f_103, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_0_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, E, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 5.16/2.31  tff(c_52, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.16/2.31  tff(c_50, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.16/2.31  tff(c_48, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.16/2.31  tff(c_46, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.16/2.31  tff(c_44, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.16/2.31  tff(c_24, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_orders_2(A_16))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.16/2.31  tff(c_40, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.16/2.31  tff(c_792, plain, (![A_120, B_121]: (k6_domain_1(A_120, B_121)=k1_tarski(B_121) | ~m1_subset_1(B_121, A_120) | v1_xboole_0(A_120))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.16/2.31  tff(c_799, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')=k1_tarski('#skF_7') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_792])).
% 5.16/2.31  tff(c_809, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_799])).
% 5.16/2.31  tff(c_18, plain, (![A_10]: (~v1_xboole_0(u1_struct_0(A_10)) | ~l1_struct_0(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.16/2.31  tff(c_812, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_809, c_18])).
% 5.16/2.31  tff(c_815, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_52, c_812])).
% 5.16/2.31  tff(c_818, plain, (~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_24, c_815])).
% 5.16/2.31  tff(c_822, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_818])).
% 5.16/2.31  tff(c_824, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_799])).
% 5.16/2.31  tff(c_42, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.16/2.31  tff(c_800, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_42, c_792])).
% 5.16/2.31  tff(c_825, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_800])).
% 5.16/2.31  tff(c_826, plain, $false, inference(negUnitSimplification, [status(thm)], [c_824, c_825])).
% 5.16/2.31  tff(c_827, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_800])).
% 5.16/2.31  tff(c_22, plain, (![A_14, B_15]: (m1_subset_1(k6_domain_1(A_14, B_15), k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, A_14) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.16/2.31  tff(c_844, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_827, c_22])).
% 5.16/2.31  tff(c_848, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_844])).
% 5.16/2.31  tff(c_849, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_824, c_848])).
% 5.16/2.31  tff(c_879, plain, (![A_132, B_133]: (k1_orders_2(A_132, B_133)=a_2_0_orders_2(A_132, B_133) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_orders_2(A_132) | ~v5_orders_2(A_132) | ~v4_orders_2(A_132) | ~v3_orders_2(A_132) | v2_struct_0(A_132))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.16/2.31  tff(c_882, plain, (k1_orders_2('#skF_5', k1_tarski('#skF_6'))=a_2_0_orders_2('#skF_5', k1_tarski('#skF_6')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_849, c_879])).
% 5.16/2.31  tff(c_892, plain, (k1_orders_2('#skF_5', k1_tarski('#skF_6'))=a_2_0_orders_2('#skF_5', k1_tarski('#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_882])).
% 5.16/2.31  tff(c_893, plain, (k1_orders_2('#skF_5', k1_tarski('#skF_6'))=a_2_0_orders_2('#skF_5', k1_tarski('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_52, c_892])).
% 5.16/2.31  tff(c_54, plain, (~r2_hidden('#skF_7', k1_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_6'))) | ~r2_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.16/2.31  tff(c_63, plain, (~r2_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_54])).
% 5.16/2.31  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.16/2.31  tff(c_81, plain, (![A_45, B_46]: (k6_domain_1(A_45, B_46)=k1_tarski(B_46) | ~m1_subset_1(B_46, A_45) | v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.16/2.31  tff(c_88, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')=k1_tarski('#skF_7') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_81])).
% 5.16/2.31  tff(c_90, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_88])).
% 5.16/2.31  tff(c_93, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_90, c_18])).
% 5.16/2.31  tff(c_96, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_52, c_93])).
% 5.16/2.31  tff(c_99, plain, (~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_24, c_96])).
% 5.16/2.31  tff(c_103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_99])).
% 5.16/2.31  tff(c_105, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_88])).
% 5.16/2.31  tff(c_89, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_42, c_81])).
% 5.16/2.31  tff(c_111, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_105, c_89])).
% 5.16/2.31  tff(c_117, plain, (![A_47, B_48]: (m1_subset_1(k6_domain_1(A_47, B_48), k1_zfmisc_1(A_47)) | ~m1_subset_1(B_48, A_47) | v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.16/2.31  tff(c_125, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_111, c_117])).
% 5.16/2.31  tff(c_132, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_125])).
% 5.16/2.31  tff(c_133, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_105, c_132])).
% 5.16/2.31  tff(c_190, plain, (![A_59, B_60]: (k1_orders_2(A_59, B_60)=a_2_0_orders_2(A_59, B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_orders_2(A_59) | ~v5_orders_2(A_59) | ~v4_orders_2(A_59) | ~v3_orders_2(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.16/2.31  tff(c_196, plain, (k1_orders_2('#skF_5', k1_tarski('#skF_6'))=a_2_0_orders_2('#skF_5', k1_tarski('#skF_6')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_133, c_190])).
% 5.16/2.31  tff(c_207, plain, (k1_orders_2('#skF_5', k1_tarski('#skF_6'))=a_2_0_orders_2('#skF_5', k1_tarski('#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_196])).
% 5.16/2.31  tff(c_208, plain, (k1_orders_2('#skF_5', k1_tarski('#skF_6'))=a_2_0_orders_2('#skF_5', k1_tarski('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_52, c_207])).
% 5.16/2.31  tff(c_60, plain, (r2_orders_2('#skF_5', '#skF_6', '#skF_7') | r2_hidden('#skF_7', k1_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.16/2.31  tff(c_106, plain, (r2_hidden('#skF_7', k1_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_63, c_60])).
% 5.16/2.31  tff(c_112, plain, (r2_hidden('#skF_7', k1_orders_2('#skF_5', k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_106])).
% 5.16/2.31  tff(c_214, plain, (r2_hidden('#skF_7', a_2_0_orders_2('#skF_5', k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_208, c_112])).
% 5.16/2.31  tff(c_219, plain, (![A_61, B_62, C_63]: ('#skF_3'(A_61, B_62, C_63)=A_61 | ~r2_hidden(A_61, a_2_0_orders_2(B_62, C_63)) | ~m1_subset_1(C_63, k1_zfmisc_1(u1_struct_0(B_62))) | ~l1_orders_2(B_62) | ~v5_orders_2(B_62) | ~v4_orders_2(B_62) | ~v3_orders_2(B_62) | v2_struct_0(B_62))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.16/2.31  tff(c_221, plain, ('#skF_3'('#skF_7', '#skF_5', k1_tarski('#skF_6'))='#skF_7' | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_214, c_219])).
% 5.16/2.31  tff(c_230, plain, ('#skF_3'('#skF_7', '#skF_5', k1_tarski('#skF_6'))='#skF_7' | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_133, c_221])).
% 5.16/2.31  tff(c_231, plain, ('#skF_3'('#skF_7', '#skF_5', k1_tarski('#skF_6'))='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_52, c_230])).
% 5.16/2.31  tff(c_684, plain, (![B_100, E_101, A_102, C_103]: (r2_orders_2(B_100, E_101, '#skF_3'(A_102, B_100, C_103)) | ~r2_hidden(E_101, C_103) | ~m1_subset_1(E_101, u1_struct_0(B_100)) | ~r2_hidden(A_102, a_2_0_orders_2(B_100, C_103)) | ~m1_subset_1(C_103, k1_zfmisc_1(u1_struct_0(B_100))) | ~l1_orders_2(B_100) | ~v5_orders_2(B_100) | ~v4_orders_2(B_100) | ~v3_orders_2(B_100) | v2_struct_0(B_100))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.16/2.31  tff(c_688, plain, (![E_101, A_102]: (r2_orders_2('#skF_5', E_101, '#skF_3'(A_102, '#skF_5', k1_tarski('#skF_6'))) | ~r2_hidden(E_101, k1_tarski('#skF_6')) | ~m1_subset_1(E_101, u1_struct_0('#skF_5')) | ~r2_hidden(A_102, a_2_0_orders_2('#skF_5', k1_tarski('#skF_6'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_133, c_684])).
% 5.16/2.31  tff(c_698, plain, (![E_101, A_102]: (r2_orders_2('#skF_5', E_101, '#skF_3'(A_102, '#skF_5', k1_tarski('#skF_6'))) | ~r2_hidden(E_101, k1_tarski('#skF_6')) | ~m1_subset_1(E_101, u1_struct_0('#skF_5')) | ~r2_hidden(A_102, a_2_0_orders_2('#skF_5', k1_tarski('#skF_6'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_688])).
% 5.16/2.31  tff(c_709, plain, (![E_106, A_107]: (r2_orders_2('#skF_5', E_106, '#skF_3'(A_107, '#skF_5', k1_tarski('#skF_6'))) | ~r2_hidden(E_106, k1_tarski('#skF_6')) | ~m1_subset_1(E_106, u1_struct_0('#skF_5')) | ~r2_hidden(A_107, a_2_0_orders_2('#skF_5', k1_tarski('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_698])).
% 5.16/2.31  tff(c_721, plain, (![E_106]: (r2_orders_2('#skF_5', E_106, '#skF_7') | ~r2_hidden(E_106, k1_tarski('#skF_6')) | ~m1_subset_1(E_106, u1_struct_0('#skF_5')) | ~r2_hidden('#skF_7', a_2_0_orders_2('#skF_5', k1_tarski('#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_231, c_709])).
% 5.16/2.31  tff(c_728, plain, (![E_108]: (r2_orders_2('#skF_5', E_108, '#skF_7') | ~r2_hidden(E_108, k1_tarski('#skF_6')) | ~m1_subset_1(E_108, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_721])).
% 5.16/2.31  tff(c_743, plain, (r2_orders_2('#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_4, c_728])).
% 5.16/2.31  tff(c_749, plain, (r2_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_743])).
% 5.16/2.31  tff(c_751, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_749])).
% 5.16/2.31  tff(c_752, plain, (~r2_hidden('#skF_7', k1_orders_2('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')))), inference(splitRight, [status(thm)], [c_54])).
% 5.16/2.31  tff(c_840, plain, (~r2_hidden('#skF_7', k1_orders_2('#skF_5', k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_827, c_752])).
% 5.16/2.31  tff(c_899, plain, (~r2_hidden('#skF_7', a_2_0_orders_2('#skF_5', k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_893, c_840])).
% 5.16/2.31  tff(c_753, plain, (r2_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_54])).
% 5.16/2.31  tff(c_1021, plain, (![D_150, B_151, C_152]: (r2_hidden('#skF_4'(D_150, B_151, C_152, D_150), C_152) | r2_hidden(D_150, a_2_0_orders_2(B_151, C_152)) | ~m1_subset_1(D_150, u1_struct_0(B_151)) | ~m1_subset_1(C_152, k1_zfmisc_1(u1_struct_0(B_151))) | ~l1_orders_2(B_151) | ~v5_orders_2(B_151) | ~v4_orders_2(B_151) | ~v3_orders_2(B_151) | v2_struct_0(B_151))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.16/2.31  tff(c_1023, plain, (![D_150]: (r2_hidden('#skF_4'(D_150, '#skF_5', k1_tarski('#skF_6'), D_150), k1_tarski('#skF_6')) | r2_hidden(D_150, a_2_0_orders_2('#skF_5', k1_tarski('#skF_6'))) | ~m1_subset_1(D_150, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_849, c_1021])).
% 5.16/2.31  tff(c_1031, plain, (![D_150]: (r2_hidden('#skF_4'(D_150, '#skF_5', k1_tarski('#skF_6'), D_150), k1_tarski('#skF_6')) | r2_hidden(D_150, a_2_0_orders_2('#skF_5', k1_tarski('#skF_6'))) | ~m1_subset_1(D_150, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_1023])).
% 5.16/2.31  tff(c_1038, plain, (![D_153]: (r2_hidden('#skF_4'(D_153, '#skF_5', k1_tarski('#skF_6'), D_153), k1_tarski('#skF_6')) | r2_hidden(D_153, a_2_0_orders_2('#skF_5', k1_tarski('#skF_6'))) | ~m1_subset_1(D_153, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_52, c_1031])).
% 5.16/2.31  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.16/2.31  tff(c_1048, plain, (![D_155]: ('#skF_4'(D_155, '#skF_5', k1_tarski('#skF_6'), D_155)='#skF_6' | r2_hidden(D_155, a_2_0_orders_2('#skF_5', k1_tarski('#skF_6'))) | ~m1_subset_1(D_155, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_1038, c_2])).
% 5.16/2.31  tff(c_1059, plain, ('#skF_4'('#skF_7', '#skF_5', k1_tarski('#skF_6'), '#skF_7')='#skF_6' | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_1048, c_899])).
% 5.16/2.31  tff(c_1073, plain, ('#skF_4'('#skF_7', '#skF_5', k1_tarski('#skF_6'), '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1059])).
% 5.16/2.31  tff(c_1267, plain, (![B_164, D_165, C_166]: (~r2_orders_2(B_164, '#skF_4'(D_165, B_164, C_166, D_165), D_165) | r2_hidden(D_165, a_2_0_orders_2(B_164, C_166)) | ~m1_subset_1(D_165, u1_struct_0(B_164)) | ~m1_subset_1(C_166, k1_zfmisc_1(u1_struct_0(B_164))) | ~l1_orders_2(B_164) | ~v5_orders_2(B_164) | ~v4_orders_2(B_164) | ~v3_orders_2(B_164) | v2_struct_0(B_164))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.16/2.31  tff(c_1277, plain, (~r2_orders_2('#skF_5', '#skF_6', '#skF_7') | r2_hidden('#skF_7', a_2_0_orders_2('#skF_5', k1_tarski('#skF_6'))) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1073, c_1267])).
% 5.16/2.31  tff(c_1293, plain, (r2_hidden('#skF_7', a_2_0_orders_2('#skF_5', k1_tarski('#skF_6'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_849, c_40, c_753, c_1277])).
% 5.16/2.31  tff(c_1295, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_899, c_1293])).
% 5.16/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.16/2.31  
% 5.16/2.31  Inference rules
% 5.16/2.31  ----------------------
% 5.16/2.31  #Ref     : 0
% 5.16/2.31  #Sup     : 249
% 5.16/2.31  #Fact    : 0
% 5.16/2.31  #Define  : 0
% 5.16/2.31  #Split   : 16
% 5.16/2.31  #Chain   : 0
% 5.16/2.31  #Close   : 0
% 5.16/2.31  
% 5.16/2.31  Ordering : KBO
% 5.16/2.31  
% 5.16/2.31  Simplification rules
% 5.16/2.31  ----------------------
% 5.16/2.31  #Subsume      : 12
% 5.16/2.31  #Demod        : 394
% 5.16/2.31  #Tautology    : 124
% 5.16/2.31  #SimpNegUnit  : 83
% 5.16/2.31  #BackRed      : 4
% 5.16/2.31  
% 5.16/2.31  #Partial instantiations: 0
% 5.16/2.31  #Strategies tried      : 1
% 5.16/2.31  
% 5.16/2.31  Timing (in seconds)
% 5.16/2.31  ----------------------
% 5.16/2.31  Preprocessing        : 0.55
% 5.16/2.31  Parsing              : 0.27
% 5.16/2.31  CNF conversion       : 0.04
% 5.16/2.31  Main loop            : 0.82
% 5.16/2.31  Inferencing          : 0.30
% 5.16/2.31  Reduction            : 0.27
% 5.16/2.31  Demodulation         : 0.18
% 5.16/2.31  BG Simplification    : 0.05
% 5.16/2.31  Subsumption          : 0.14
% 5.16/2.31  Abstraction          : 0.05
% 5.16/2.31  MUC search           : 0.00
% 5.16/2.31  Cooper               : 0.00
% 5.16/2.31  Total                : 1.44
% 5.16/2.31  Index Insertion      : 0.00
% 5.16/2.32  Index Deletion       : 0.00
% 5.16/2.32  Index Matching       : 0.00
% 5.16/2.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
