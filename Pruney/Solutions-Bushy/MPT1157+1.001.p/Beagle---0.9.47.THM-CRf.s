%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1157+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:31 EST 2020

% Result     : Theorem 6.06s
% Output     : CNFRefutation 6.06s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 516 expanded)
%              Number of leaves         :   36 ( 191 expanded)
%              Depth                    :   19
%              Number of atoms          :  235 (1793 expanded)
%              Number of equality atoms :   25 ( 175 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

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

tff(f_133,negated_conjecture,(
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

tff(f_58,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_40,axiom,(
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

tff(f_47,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_94,axiom,(
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

tff(c_54,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_52,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_50,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_48,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_46,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_18,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_orders_2(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_42,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_88,plain,(
    ! [A_45,B_46] :
      ( k6_domain_1(A_45,B_46) = k1_tarski(B_46)
      | ~ m1_subset_1(B_46,A_45)
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_95,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_42,c_88])).

tff(c_97,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_22,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(u1_struct_0(A_12))
      | ~ l1_struct_0(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_100,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_97,c_22])).

tff(c_106,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_100])).

tff(c_111,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_106])).

tff(c_115,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_111])).

tff(c_117,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_96,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_44,c_88])).

tff(c_122,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_96])).

tff(c_128,plain,(
    ! [A_49,B_50] :
      ( m1_subset_1(k6_domain_1(A_49,B_50),k1_zfmisc_1(A_49))
      | ~ m1_subset_1(B_50,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_136,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_128])).

tff(c_143,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_136])).

tff(c_144,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_143])).

tff(c_4103,plain,(
    ! [A_323,B_324] :
      ( k1_orders_2(A_323,B_324) = a_2_0_orders_2(A_323,B_324)
      | ~ m1_subset_1(B_324,k1_zfmisc_1(u1_struct_0(A_323)))
      | ~ l1_orders_2(A_323)
      | ~ v5_orders_2(A_323)
      | ~ v4_orders_2(A_323)
      | ~ v3_orders_2(A_323)
      | v2_struct_0(A_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4109,plain,
    ( k1_orders_2('#skF_5',k1_tarski('#skF_6')) = a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_144,c_4103])).

tff(c_4120,plain,
    ( k1_orders_2('#skF_5',k1_tarski('#skF_6')) = a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_4109])).

tff(c_4121,plain,(
    k1_orders_2('#skF_5',k1_tarski('#skF_6')) = a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_4120])).

tff(c_56,plain,
    ( ~ r2_hidden('#skF_7',k1_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_6')))
    | ~ r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_169,plain,
    ( ~ r2_hidden('#skF_7',k1_orders_2('#skF_5',k1_tarski('#skF_6')))
    | ~ r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_56])).

tff(c_170,plain,(
    ~ r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_169])).

tff(c_6,plain,(
    ! [C_8] : r2_hidden(C_8,k1_tarski(C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1363,plain,(
    ! [A_145,B_146] :
      ( k1_orders_2(A_145,B_146) = a_2_0_orders_2(A_145,B_146)
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_orders_2(A_145)
      | ~ v5_orders_2(A_145)
      | ~ v4_orders_2(A_145)
      | ~ v3_orders_2(A_145)
      | v2_struct_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1369,plain,
    ( k1_orders_2('#skF_5',k1_tarski('#skF_6')) = a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_144,c_1363])).

tff(c_1380,plain,
    ( k1_orders_2('#skF_5',k1_tarski('#skF_6')) = a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_1369])).

tff(c_1381,plain,(
    k1_orders_2('#skF_5',k1_tarski('#skF_6')) = a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1380])).

tff(c_62,plain,
    ( r2_orders_2('#skF_5','#skF_6','#skF_7')
    | r2_hidden('#skF_7',k1_orders_2('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_194,plain,
    ( r2_orders_2('#skF_5','#skF_6','#skF_7')
    | r2_hidden('#skF_7',k1_orders_2('#skF_5',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_62])).

tff(c_195,plain,(
    r2_hidden('#skF_7',k1_orders_2('#skF_5',k1_tarski('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_194])).

tff(c_1387,plain,(
    r2_hidden('#skF_7',a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1381,c_195])).

tff(c_1456,plain,(
    ! [A_149,B_150,C_151] :
      ( '#skF_3'(A_149,B_150,C_151) = A_149
      | ~ r2_hidden(A_149,a_2_0_orders_2(B_150,C_151))
      | ~ m1_subset_1(C_151,k1_zfmisc_1(u1_struct_0(B_150)))
      | ~ l1_orders_2(B_150)
      | ~ v5_orders_2(B_150)
      | ~ v4_orders_2(B_150)
      | ~ v3_orders_2(B_150)
      | v2_struct_0(B_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1458,plain,
    ( '#skF_3'('#skF_7','#skF_5',k1_tarski('#skF_6')) = '#skF_7'
    | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1387,c_1456])).

tff(c_1467,plain,
    ( '#skF_3'('#skF_7','#skF_5',k1_tarski('#skF_6')) = '#skF_7'
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_144,c_1458])).

tff(c_1468,plain,(
    '#skF_3'('#skF_7','#skF_5',k1_tarski('#skF_6')) = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1467])).

tff(c_2156,plain,(
    ! [B_196,E_197,A_198,C_199] :
      ( r2_orders_2(B_196,E_197,'#skF_3'(A_198,B_196,C_199))
      | ~ r2_hidden(E_197,C_199)
      | ~ m1_subset_1(E_197,u1_struct_0(B_196))
      | ~ r2_hidden(A_198,a_2_0_orders_2(B_196,C_199))
      | ~ m1_subset_1(C_199,k1_zfmisc_1(u1_struct_0(B_196)))
      | ~ l1_orders_2(B_196)
      | ~ v5_orders_2(B_196)
      | ~ v4_orders_2(B_196)
      | ~ v3_orders_2(B_196)
      | v2_struct_0(B_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2164,plain,(
    ! [E_197,A_198] :
      ( r2_orders_2('#skF_5',E_197,'#skF_3'(A_198,'#skF_5',k1_tarski('#skF_6')))
      | ~ r2_hidden(E_197,k1_tarski('#skF_6'))
      | ~ m1_subset_1(E_197,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_198,a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_144,c_2156])).

tff(c_2182,plain,(
    ! [E_197,A_198] :
      ( r2_orders_2('#skF_5',E_197,'#skF_3'(A_198,'#skF_5',k1_tarski('#skF_6')))
      | ~ r2_hidden(E_197,k1_tarski('#skF_6'))
      | ~ m1_subset_1(E_197,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_198,a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_2164])).

tff(c_3009,plain,(
    ! [E_239,A_240] :
      ( r2_orders_2('#skF_5',E_239,'#skF_3'(A_240,'#skF_5',k1_tarski('#skF_6')))
      | ~ r2_hidden(E_239,k1_tarski('#skF_6'))
      | ~ m1_subset_1(E_239,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_240,a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2182])).

tff(c_3015,plain,(
    ! [E_239] :
      ( r2_orders_2('#skF_5',E_239,'#skF_7')
      | ~ r2_hidden(E_239,k1_tarski('#skF_6'))
      | ~ m1_subset_1(E_239,u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_7',a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1468,c_3009])).

tff(c_3030,plain,(
    ! [E_243] :
      ( r2_orders_2('#skF_5',E_243,'#skF_7')
      | ~ r2_hidden(E_243,k1_tarski('#skF_6'))
      | ~ m1_subset_1(E_243,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1387,c_3015])).

tff(c_3049,plain,
    ( r2_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_6,c_3030])).

tff(c_3058,plain,(
    r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3049])).

tff(c_3060,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_3058])).

tff(c_3061,plain,(
    ~ r2_hidden('#skF_7',k1_orders_2('#skF_5',k1_tarski('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_4127,plain,(
    ~ r2_hidden('#skF_7',a_2_0_orders_2('#skF_5',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4121,c_3061])).

tff(c_3062,plain,(
    r2_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_4500,plain,(
    ! [D_356,B_357,C_358] :
      ( r2_hidden('#skF_4'(D_356,B_357,C_358,D_356),C_358)
      | r2_hidden(D_356,a_2_0_orders_2(B_357,C_358))
      | ~ m1_subset_1(D_356,u1_struct_0(B_357))
      | ~ m1_subset_1(C_358,k1_zfmisc_1(u1_struct_0(B_357)))
      | ~ l1_orders_2(B_357)
      | ~ v5_orders_2(B_357)
      | ~ v4_orders_2(B_357)
      | ~ v3_orders_2(B_357)
      | v2_struct_0(B_357) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_4508,plain,(
    ! [D_356] :
      ( r2_hidden('#skF_4'(D_356,'#skF_5',k1_tarski('#skF_6'),D_356),k1_tarski('#skF_6'))
      | r2_hidden(D_356,a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
      | ~ m1_subset_1(D_356,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_144,c_4500])).

tff(c_4526,plain,(
    ! [D_356] :
      ( r2_hidden('#skF_4'(D_356,'#skF_5',k1_tarski('#skF_6'),D_356),k1_tarski('#skF_6'))
      | r2_hidden(D_356,a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
      | ~ m1_subset_1(D_356,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_4508])).

tff(c_4548,plain,(
    ! [D_364] :
      ( r2_hidden('#skF_4'(D_364,'#skF_5',k1_tarski('#skF_6'),D_364),k1_tarski('#skF_6'))
      | r2_hidden(D_364,a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
      | ~ m1_subset_1(D_364,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_4526])).

tff(c_4,plain,(
    ! [C_8,A_4] :
      ( C_8 = A_4
      | ~ r2_hidden(C_8,k1_tarski(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4594,plain,(
    ! [D_366] :
      ( '#skF_4'(D_366,'#skF_5',k1_tarski('#skF_6'),D_366) = '#skF_6'
      | r2_hidden(D_366,a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
      | ~ m1_subset_1(D_366,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_4548,c_4])).

tff(c_4611,plain,
    ( '#skF_4'('#skF_7','#skF_5',k1_tarski('#skF_6'),'#skF_7') = '#skF_6'
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_4594,c_4127])).

tff(c_4627,plain,(
    '#skF_4'('#skF_7','#skF_5',k1_tarski('#skF_6'),'#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_4611])).

tff(c_4665,plain,(
    ! [B_368,D_369,C_370] :
      ( ~ r2_orders_2(B_368,'#skF_4'(D_369,B_368,C_370,D_369),D_369)
      | r2_hidden(D_369,a_2_0_orders_2(B_368,C_370))
      | ~ m1_subset_1(D_369,u1_struct_0(B_368))
      | ~ m1_subset_1(C_370,k1_zfmisc_1(u1_struct_0(B_368)))
      | ~ l1_orders_2(B_368)
      | ~ v5_orders_2(B_368)
      | ~ v4_orders_2(B_368)
      | ~ v3_orders_2(B_368)
      | v2_struct_0(B_368) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_4667,plain,
    ( ~ r2_orders_2('#skF_5','#skF_6','#skF_7')
    | r2_hidden('#skF_7',a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4627,c_4665])).

tff(c_4673,plain,
    ( r2_hidden('#skF_7',a_2_0_orders_2('#skF_5',k1_tarski('#skF_6')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_144,c_42,c_3062,c_4667])).

tff(c_4675,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_4127,c_4673])).

%------------------------------------------------------------------------------
