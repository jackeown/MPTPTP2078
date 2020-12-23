%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1638+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:10 EST 2020

% Result     : Theorem 4.04s
% Output     : CNFRefutation 4.04s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 425 expanded)
%              Number of leaves         :   36 ( 157 expanded)
%              Depth                    :   18
%              Number of atoms          :  228 (1164 expanded)
%              Number of equality atoms :   38 ( 149 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > r2_hidden > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_waybel_0 > k6_domain_1 > k4_waybel_0 > a_2_6_waybel_0 > a_2_1_waybel_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_6 > #skF_4 > #skF_7 > #skF_5 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(a_2_1_waybel_0,type,(
    a_2_1_waybel_0: ( $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(a_2_6_waybel_0,type,(
    a_2_6_waybel_0: ( $i * $i ) > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k6_waybel_0,type,(
    k6_waybel_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k4_waybel_0,type,(
    k4_waybel_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_135,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r2_hidden(C,k6_waybel_0(A,B))
                <=> r1_orders_2(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_waybel_0)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_109,axiom,(
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

tff(f_119,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k4_waybel_0(A,B) = a_2_1_waybel_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_waybel_0)).

tff(f_34,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k6_waybel_0(A,B) = k4_waybel_0(A,k6_domain_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_waybel_0)).

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
     => ( r2_hidden(A,a_2_1_waybel_0(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & ? [E] :
                ( m1_subset_1(E,u1_struct_0(B))
                & r1_orders_2(B,E,D)
                & r2_hidden(E,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_waybel_0)).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_64,plain,
    ( r2_hidden('#skF_9',k6_waybel_0('#skF_7','#skF_8'))
    | r1_orders_2('#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_74,plain,(
    r1_orders_2('#skF_7','#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_50,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_54,plain,(
    l1_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_52,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_18,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_orders_2(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_76,plain,(
    ! [A_53,B_54] :
      ( k6_domain_1(A_53,B_54) = k1_tarski(B_54)
      | ~ m1_subset_1(B_54,A_53)
      | v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_83,plain,
    ( k6_domain_1(u1_struct_0('#skF_7'),'#skF_9') = k1_tarski('#skF_9')
    | v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_50,c_76])).

tff(c_85,plain,(
    v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_20,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(u1_struct_0(A_12))
      | ~ l1_struct_0(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_88,plain,
    ( ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_85,c_20])).

tff(c_91,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_88])).

tff(c_95,plain,(
    ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_18,c_91])).

tff(c_99,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_95])).

tff(c_101,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_84,plain,
    ( k6_domain_1(u1_struct_0('#skF_7'),'#skF_8') = k1_tarski('#skF_8')
    | v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_52,c_76])).

tff(c_106,plain,(
    k6_domain_1(u1_struct_0('#skF_7'),'#skF_8') = k1_tarski('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_84])).

tff(c_112,plain,(
    ! [A_59,B_60] :
      ( m1_subset_1(k6_domain_1(A_59,B_60),k1_zfmisc_1(A_59))
      | ~ m1_subset_1(B_60,A_59)
      | v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_118,plain,
    ( m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_7')))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_112])).

tff(c_124,plain,
    ( m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_7')))
    | v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_118])).

tff(c_125,plain,(
    m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_124])).

tff(c_175,plain,(
    ! [A_69,B_70] :
      ( k4_waybel_0(A_69,B_70) = a_2_1_waybel_0(A_69,B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_orders_2(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_181,plain,
    ( k4_waybel_0('#skF_7',k1_tarski('#skF_8')) = a_2_1_waybel_0('#skF_7',k1_tarski('#skF_8'))
    | ~ l1_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_125,c_175])).

tff(c_192,plain,
    ( k4_waybel_0('#skF_7',k1_tarski('#skF_8')) = a_2_1_waybel_0('#skF_7',k1_tarski('#skF_8'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_181])).

tff(c_193,plain,(
    k4_waybel_0('#skF_7',k1_tarski('#skF_8')) = a_2_1_waybel_0('#skF_7',k1_tarski('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_192])).

tff(c_204,plain,(
    ! [A_73,B_74] :
      ( k4_waybel_0(A_73,k6_domain_1(u1_struct_0(A_73),B_74)) = k6_waybel_0(A_73,B_74)
      | ~ m1_subset_1(B_74,u1_struct_0(A_73))
      | ~ l1_orders_2(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_213,plain,
    ( k4_waybel_0('#skF_7',k1_tarski('#skF_8')) = k6_waybel_0('#skF_7','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l1_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_204])).

tff(c_220,plain,
    ( a_2_1_waybel_0('#skF_7',k1_tarski('#skF_8')) = k6_waybel_0('#skF_7','#skF_8')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_193,c_213])).

tff(c_221,plain,(
    a_2_1_waybel_0('#skF_7',k1_tarski('#skF_8')) = k6_waybel_0('#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_220])).

tff(c_6,plain,(
    ! [C_8] : r2_hidden(C_8,k1_tarski(C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_690,plain,(
    ! [D_135,B_136,C_137,E_138] :
      ( r2_hidden(D_135,a_2_1_waybel_0(B_136,C_137))
      | ~ r2_hidden(E_138,C_137)
      | ~ r1_orders_2(B_136,E_138,D_135)
      | ~ m1_subset_1(E_138,u1_struct_0(B_136))
      | ~ m1_subset_1(D_135,u1_struct_0(B_136))
      | ~ m1_subset_1(C_137,k1_zfmisc_1(u1_struct_0(B_136)))
      | ~ l1_orders_2(B_136)
      | v2_struct_0(B_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_742,plain,(
    ! [D_142,B_143,C_144] :
      ( r2_hidden(D_142,a_2_1_waybel_0(B_143,k1_tarski(C_144)))
      | ~ r1_orders_2(B_143,C_144,D_142)
      | ~ m1_subset_1(C_144,u1_struct_0(B_143))
      | ~ m1_subset_1(D_142,u1_struct_0(B_143))
      | ~ m1_subset_1(k1_tarski(C_144),k1_zfmisc_1(u1_struct_0(B_143)))
      | ~ l1_orders_2(B_143)
      | v2_struct_0(B_143) ) ),
    inference(resolution,[status(thm)],[c_6,c_690])).

tff(c_746,plain,(
    ! [D_142] :
      ( r2_hidden(D_142,a_2_1_waybel_0('#skF_7',k1_tarski('#skF_8')))
      | ~ r1_orders_2('#skF_7','#skF_8',D_142)
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
      | ~ m1_subset_1(D_142,u1_struct_0('#skF_7'))
      | ~ l1_orders_2('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_125,c_742])).

tff(c_753,plain,(
    ! [D_142] :
      ( r2_hidden(D_142,k6_waybel_0('#skF_7','#skF_8'))
      | ~ r1_orders_2('#skF_7','#skF_8',D_142)
      | ~ m1_subset_1(D_142,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_221,c_746])).

tff(c_776,plain,(
    ! [D_146] :
      ( r2_hidden(D_146,k6_waybel_0('#skF_7','#skF_8'))
      | ~ r1_orders_2('#skF_7','#skF_8',D_146)
      | ~ m1_subset_1(D_146,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_753])).

tff(c_58,plain,
    ( ~ r1_orders_2('#skF_7','#skF_8','#skF_9')
    | ~ r2_hidden('#skF_9',k6_waybel_0('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_75,plain,(
    ~ r2_hidden('#skF_9',k6_waybel_0('#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_794,plain,
    ( ~ r1_orders_2('#skF_7','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_776,c_75])).

tff(c_803,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_74,c_794])).

tff(c_804,plain,(
    ~ r1_orders_2('#skF_7','#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_807,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_804])).

tff(c_809,plain,(
    ~ r1_orders_2('#skF_7','#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_812,plain,(
    ! [A_147,B_148] :
      ( k6_domain_1(A_147,B_148) = k1_tarski(B_148)
      | ~ m1_subset_1(B_148,A_147)
      | v1_xboole_0(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_819,plain,
    ( k6_domain_1(u1_struct_0('#skF_7'),'#skF_9') = k1_tarski('#skF_9')
    | v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_50,c_812])).

tff(c_821,plain,(
    v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_819])).

tff(c_824,plain,
    ( ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_821,c_20])).

tff(c_827,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_824])).

tff(c_830,plain,(
    ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_18,c_827])).

tff(c_834,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_830])).

tff(c_836,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_819])).

tff(c_820,plain,
    ( k6_domain_1(u1_struct_0('#skF_7'),'#skF_8') = k1_tarski('#skF_8')
    | v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_52,c_812])).

tff(c_837,plain,(
    v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_820])).

tff(c_838,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_836,c_837])).

tff(c_839,plain,(
    k6_domain_1(u1_struct_0('#skF_7'),'#skF_8') = k1_tarski('#skF_8') ),
    inference(splitRight,[status(thm)],[c_820])).

tff(c_850,plain,(
    ! [A_151,B_152] :
      ( m1_subset_1(k6_domain_1(A_151,B_152),k1_zfmisc_1(A_151))
      | ~ m1_subset_1(B_152,A_151)
      | v1_xboole_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_856,plain,
    ( m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_7')))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_839,c_850])).

tff(c_862,plain,
    ( m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_7')))
    | v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_856])).

tff(c_863,plain,(
    m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_836,c_862])).

tff(c_808,plain,(
    r2_hidden('#skF_9',k6_waybel_0('#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_889,plain,(
    ! [A_159,B_160] :
      ( k4_waybel_0(A_159,B_160) = a_2_1_waybel_0(A_159,B_160)
      | ~ m1_subset_1(B_160,k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ l1_orders_2(A_159)
      | v2_struct_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_895,plain,
    ( k4_waybel_0('#skF_7',k1_tarski('#skF_8')) = a_2_1_waybel_0('#skF_7',k1_tarski('#skF_8'))
    | ~ l1_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_863,c_889])).

tff(c_906,plain,
    ( k4_waybel_0('#skF_7',k1_tarski('#skF_8')) = a_2_1_waybel_0('#skF_7',k1_tarski('#skF_8'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_895])).

tff(c_907,plain,(
    k4_waybel_0('#skF_7',k1_tarski('#skF_8')) = a_2_1_waybel_0('#skF_7',k1_tarski('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_906])).

tff(c_918,plain,(
    ! [A_161,B_162] :
      ( k4_waybel_0(A_161,k6_domain_1(u1_struct_0(A_161),B_162)) = k6_waybel_0(A_161,B_162)
      | ~ m1_subset_1(B_162,u1_struct_0(A_161))
      | ~ l1_orders_2(A_161)
      | v2_struct_0(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_927,plain,
    ( k4_waybel_0('#skF_7',k1_tarski('#skF_8')) = k6_waybel_0('#skF_7','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l1_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_839,c_918])).

tff(c_934,plain,
    ( a_2_1_waybel_0('#skF_7',k1_tarski('#skF_8')) = k6_waybel_0('#skF_7','#skF_8')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_907,c_927])).

tff(c_935,plain,(
    a_2_1_waybel_0('#skF_7',k1_tarski('#skF_8')) = k6_waybel_0('#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_934])).

tff(c_1022,plain,(
    ! [A_172,B_173,C_174] :
      ( '#skF_3'(A_172,B_173,C_174) = A_172
      | ~ r2_hidden(A_172,a_2_1_waybel_0(B_173,C_174))
      | ~ m1_subset_1(C_174,k1_zfmisc_1(u1_struct_0(B_173)))
      | ~ l1_orders_2(B_173)
      | v2_struct_0(B_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1026,plain,(
    ! [A_172] :
      ( '#skF_3'(A_172,'#skF_7',k1_tarski('#skF_8')) = A_172
      | ~ r2_hidden(A_172,k6_waybel_0('#skF_7','#skF_8'))
      | ~ m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ l1_orders_2('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_935,c_1022])).

tff(c_1037,plain,(
    ! [A_172] :
      ( '#skF_3'(A_172,'#skF_7',k1_tarski('#skF_8')) = A_172
      | ~ r2_hidden(A_172,k6_waybel_0('#skF_7','#skF_8'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_863,c_1026])).

tff(c_1052,plain,(
    ! [A_176] :
      ( '#skF_3'(A_176,'#skF_7',k1_tarski('#skF_8')) = A_176
      | ~ r2_hidden(A_176,k6_waybel_0('#skF_7','#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1037])).

tff(c_1066,plain,(
    '#skF_3'('#skF_9','#skF_7',k1_tarski('#skF_8')) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_808,c_1052])).

tff(c_1076,plain,(
    ! [A_180,B_181,C_182] :
      ( r2_hidden('#skF_4'(A_180,B_181,C_182),C_182)
      | ~ r2_hidden(A_180,a_2_1_waybel_0(B_181,C_182))
      | ~ m1_subset_1(C_182,k1_zfmisc_1(u1_struct_0(B_181)))
      | ~ l1_orders_2(B_181)
      | v2_struct_0(B_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1080,plain,(
    ! [A_180] :
      ( r2_hidden('#skF_4'(A_180,'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8'))
      | ~ r2_hidden(A_180,a_2_1_waybel_0('#skF_7',k1_tarski('#skF_8')))
      | ~ l1_orders_2('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_863,c_1076])).

tff(c_1090,plain,(
    ! [A_180] :
      ( r2_hidden('#skF_4'(A_180,'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8'))
      | ~ r2_hidden(A_180,k6_waybel_0('#skF_7','#skF_8'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_935,c_1080])).

tff(c_1114,plain,(
    ! [A_188] :
      ( r2_hidden('#skF_4'(A_188,'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8'))
      | ~ r2_hidden(A_188,k6_waybel_0('#skF_7','#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1090])).

tff(c_4,plain,(
    ! [C_8,A_4] :
      ( C_8 = A_4
      | ~ r2_hidden(C_8,k1_tarski(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1119,plain,(
    ! [A_189] :
      ( '#skF_4'(A_189,'#skF_7',k1_tarski('#skF_8')) = '#skF_8'
      | ~ r2_hidden(A_189,k6_waybel_0('#skF_7','#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_1114,c_4])).

tff(c_1133,plain,(
    '#skF_4'('#skF_9','#skF_7',k1_tarski('#skF_8')) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_808,c_1119])).

tff(c_1344,plain,(
    ! [B_214,A_215,C_216] :
      ( r1_orders_2(B_214,'#skF_4'(A_215,B_214,C_216),'#skF_3'(A_215,B_214,C_216))
      | ~ r2_hidden(A_215,a_2_1_waybel_0(B_214,C_216))
      | ~ m1_subset_1(C_216,k1_zfmisc_1(u1_struct_0(B_214)))
      | ~ l1_orders_2(B_214)
      | v2_struct_0(B_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1353,plain,
    ( r1_orders_2('#skF_7','#skF_8','#skF_3'('#skF_9','#skF_7',k1_tarski('#skF_8')))
    | ~ r2_hidden('#skF_9',a_2_1_waybel_0('#skF_7',k1_tarski('#skF_8')))
    | ~ m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_7')))
    | ~ l1_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1133,c_1344])).

tff(c_1364,plain,
    ( r1_orders_2('#skF_7','#skF_8','#skF_9')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_863,c_808,c_935,c_1066,c_1353])).

tff(c_1366,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_809,c_1364])).

%------------------------------------------------------------------------------
