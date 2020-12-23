%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1638+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:10 EST 2020

% Result     : Theorem 5.11s
% Output     : CNFRefutation 5.11s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 459 expanded)
%              Number of leaves         :   33 ( 167 expanded)
%              Depth                    :   19
%              Number of atoms          :  224 (1265 expanded)
%              Number of equality atoms :   38 ( 170 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > r2_hidden > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_waybel_0 > k6_domain_1 > k4_waybel_0 > a_2_1_waybel_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_131,negated_conjecture,(
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

tff(c_50,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_44,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_58,plain,
    ( r2_hidden('#skF_7',k6_waybel_0('#skF_5','#skF_6'))
    | r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_73,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_48,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_18,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_orders_2(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_96,plain,(
    ! [A_57,B_58] :
      ( k6_domain_1(A_57,B_58) = k1_tarski(B_58)
      | ~ m1_subset_1(B_58,A_57)
      | v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_103,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_44,c_96])).

tff(c_105,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_20,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(u1_struct_0(A_12))
      | ~ l1_struct_0(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_108,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_105,c_20])).

tff(c_111,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_108])).

tff(c_114,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_111])).

tff(c_118,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_114])).

tff(c_120,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_104,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_46,c_96])).

tff(c_125,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_104])).

tff(c_130,plain,(
    ! [A_59,B_60] :
      ( m1_subset_1(k6_domain_1(A_59,B_60),k1_zfmisc_1(A_59))
      | ~ m1_subset_1(B_60,A_59)
      | v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_138,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_130])).

tff(c_145,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_138])).

tff(c_146,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_145])).

tff(c_321,plain,(
    ! [A_83,B_84] :
      ( k4_waybel_0(A_83,B_84) = a_2_1_waybel_0(A_83,B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_orders_2(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_327,plain,
    ( k4_waybel_0('#skF_5',k1_tarski('#skF_6')) = a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_146,c_321])).

tff(c_338,plain,
    ( k4_waybel_0('#skF_5',k1_tarski('#skF_6')) = a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_327])).

tff(c_339,plain,(
    k4_waybel_0('#skF_5',k1_tarski('#skF_6')) = a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_338])).

tff(c_406,plain,(
    ! [A_95,B_96] :
      ( k4_waybel_0(A_95,k6_domain_1(u1_struct_0(A_95),B_96)) = k6_waybel_0(A_95,B_96)
      | ~ m1_subset_1(B_96,u1_struct_0(A_95))
      | ~ l1_orders_2(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_415,plain,
    ( k4_waybel_0('#skF_5',k1_tarski('#skF_6')) = k6_waybel_0('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_406])).

tff(c_422,plain,
    ( a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6')) = k6_waybel_0('#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_339,c_415])).

tff(c_423,plain,(
    a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6')) = k6_waybel_0('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_422])).

tff(c_6,plain,(
    ! [C_8] : r2_hidden(C_8,k1_tarski(C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1185,plain,(
    ! [D_154,B_155,C_156,E_157] :
      ( r2_hidden(D_154,a_2_1_waybel_0(B_155,C_156))
      | ~ r2_hidden(E_157,C_156)
      | ~ r1_orders_2(B_155,E_157,D_154)
      | ~ m1_subset_1(E_157,u1_struct_0(B_155))
      | ~ m1_subset_1(D_154,u1_struct_0(B_155))
      | ~ m1_subset_1(C_156,k1_zfmisc_1(u1_struct_0(B_155)))
      | ~ l1_orders_2(B_155)
      | v2_struct_0(B_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1388,plain,(
    ! [D_172,B_173,C_174] :
      ( r2_hidden(D_172,a_2_1_waybel_0(B_173,k1_tarski(C_174)))
      | ~ r1_orders_2(B_173,C_174,D_172)
      | ~ m1_subset_1(C_174,u1_struct_0(B_173))
      | ~ m1_subset_1(D_172,u1_struct_0(B_173))
      | ~ m1_subset_1(k1_tarski(C_174),k1_zfmisc_1(u1_struct_0(B_173)))
      | ~ l1_orders_2(B_173)
      | v2_struct_0(B_173) ) ),
    inference(resolution,[status(thm)],[c_6,c_1185])).

tff(c_1396,plain,(
    ! [D_172] :
      ( r2_hidden(D_172,a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6')))
      | ~ r1_orders_2('#skF_5','#skF_6',D_172)
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(D_172,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_146,c_1388])).

tff(c_1411,plain,(
    ! [D_172] :
      ( r2_hidden(D_172,k6_waybel_0('#skF_5','#skF_6'))
      | ~ r1_orders_2('#skF_5','#skF_6',D_172)
      | ~ m1_subset_1(D_172,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_423,c_1396])).

tff(c_1524,plain,(
    ! [D_179] :
      ( r2_hidden(D_179,k6_waybel_0('#skF_5','#skF_6'))
      | ~ r1_orders_2('#skF_5','#skF_6',D_179)
      | ~ m1_subset_1(D_179,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1411])).

tff(c_52,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ r2_hidden('#skF_7',k6_waybel_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_89,plain,(
    ~ r2_hidden('#skF_7',k6_waybel_0('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_52])).

tff(c_1545,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1524,c_89])).

tff(c_1558,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_73,c_1545])).

tff(c_1560,plain,(
    ~ r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1582,plain,(
    ! [A_188,B_189] :
      ( k6_domain_1(A_188,B_189) = k1_tarski(B_189)
      | ~ m1_subset_1(B_189,A_188)
      | v1_xboole_0(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1589,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_44,c_1582])).

tff(c_1591,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1589])).

tff(c_1594,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1591,c_20])).

tff(c_1597,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1594])).

tff(c_1600,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_1597])).

tff(c_1604,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1600])).

tff(c_1606,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1589])).

tff(c_1590,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_46,c_1582])).

tff(c_1632,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_1606,c_1590])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k6_domain_1(A_9,B_10),k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1636,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1632,c_16])).

tff(c_1640,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1636])).

tff(c_1641,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1606,c_1640])).

tff(c_1559,plain,(
    r2_hidden('#skF_7',k6_waybel_0('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1759,plain,(
    ! [A_209,B_210] :
      ( k4_waybel_0(A_209,B_210) = a_2_1_waybel_0(A_209,B_210)
      | ~ m1_subset_1(B_210,k1_zfmisc_1(u1_struct_0(A_209)))
      | ~ l1_orders_2(A_209)
      | v2_struct_0(A_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1762,plain,
    ( k4_waybel_0('#skF_5',k1_tarski('#skF_6')) = a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1641,c_1759])).

tff(c_1772,plain,
    ( k4_waybel_0('#skF_5',k1_tarski('#skF_6')) = a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1762])).

tff(c_1773,plain,(
    k4_waybel_0('#skF_5',k1_tarski('#skF_6')) = a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1772])).

tff(c_1878,plain,(
    ! [A_223,B_224] :
      ( k4_waybel_0(A_223,k6_domain_1(u1_struct_0(A_223),B_224)) = k6_waybel_0(A_223,B_224)
      | ~ m1_subset_1(B_224,u1_struct_0(A_223))
      | ~ l1_orders_2(A_223)
      | v2_struct_0(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1887,plain,
    ( k4_waybel_0('#skF_5',k1_tarski('#skF_6')) = k6_waybel_0('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1632,c_1878])).

tff(c_1894,plain,
    ( a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6')) = k6_waybel_0('#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1773,c_1887])).

tff(c_1895,plain,(
    a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6')) = k6_waybel_0('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1894])).

tff(c_1980,plain,(
    ! [A_233,B_234,C_235] :
      ( '#skF_3'(A_233,B_234,C_235) = A_233
      | ~ r2_hidden(A_233,a_2_1_waybel_0(B_234,C_235))
      | ~ m1_subset_1(C_235,k1_zfmisc_1(u1_struct_0(B_234)))
      | ~ l1_orders_2(B_234)
      | v2_struct_0(B_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1984,plain,(
    ! [A_233] :
      ( '#skF_3'(A_233,'#skF_5',k1_tarski('#skF_6')) = A_233
      | ~ r2_hidden(A_233,k6_waybel_0('#skF_5','#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1895,c_1980])).

tff(c_1998,plain,(
    ! [A_233] :
      ( '#skF_3'(A_233,'#skF_5',k1_tarski('#skF_6')) = A_233
      | ~ r2_hidden(A_233,k6_waybel_0('#skF_5','#skF_6'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1641,c_1984])).

tff(c_2019,plain,(
    ! [A_237] :
      ( '#skF_3'(A_237,'#skF_5',k1_tarski('#skF_6')) = A_237
      | ~ r2_hidden(A_237,k6_waybel_0('#skF_5','#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1998])).

tff(c_2040,plain,(
    '#skF_3'('#skF_7','#skF_5',k1_tarski('#skF_6')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1559,c_2019])).

tff(c_2081,plain,(
    ! [A_242,B_243,C_244] :
      ( r2_hidden('#skF_4'(A_242,B_243,C_244),C_244)
      | ~ r2_hidden(A_242,a_2_1_waybel_0(B_243,C_244))
      | ~ m1_subset_1(C_244,k1_zfmisc_1(u1_struct_0(B_243)))
      | ~ l1_orders_2(B_243)
      | v2_struct_0(B_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2083,plain,(
    ! [A_242] :
      ( r2_hidden('#skF_4'(A_242,'#skF_5',k1_tarski('#skF_6')),k1_tarski('#skF_6'))
      | ~ r2_hidden(A_242,a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6')))
      | ~ l1_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1641,c_2081])).

tff(c_2091,plain,(
    ! [A_242] :
      ( r2_hidden('#skF_4'(A_242,'#skF_5',k1_tarski('#skF_6')),k1_tarski('#skF_6'))
      | ~ r2_hidden(A_242,k6_waybel_0('#skF_5','#skF_6'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1895,c_2083])).

tff(c_2098,plain,(
    ! [A_245] :
      ( r2_hidden('#skF_4'(A_245,'#skF_5',k1_tarski('#skF_6')),k1_tarski('#skF_6'))
      | ~ r2_hidden(A_245,k6_waybel_0('#skF_5','#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2091])).

tff(c_4,plain,(
    ! [C_8,A_4] :
      ( C_8 = A_4
      | ~ r2_hidden(C_8,k1_tarski(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2111,plain,(
    ! [A_246] :
      ( '#skF_4'(A_246,'#skF_5',k1_tarski('#skF_6')) = '#skF_6'
      | ~ r2_hidden(A_246,k6_waybel_0('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_2098,c_4])).

tff(c_2132,plain,(
    '#skF_4'('#skF_7','#skF_5',k1_tarski('#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1559,c_2111])).

tff(c_2431,plain,(
    ! [B_267,A_268,C_269] :
      ( r1_orders_2(B_267,'#skF_4'(A_268,B_267,C_269),'#skF_3'(A_268,B_267,C_269))
      | ~ r2_hidden(A_268,a_2_1_waybel_0(B_267,C_269))
      | ~ m1_subset_1(C_269,k1_zfmisc_1(u1_struct_0(B_267)))
      | ~ l1_orders_2(B_267)
      | v2_struct_0(B_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2437,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_3'('#skF_7','#skF_5',k1_tarski('#skF_6')))
    | ~ r2_hidden('#skF_7',a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6')))
    | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2132,c_2431])).

tff(c_2445,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_7')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1641,c_1559,c_1895,c_2040,c_2437])).

tff(c_2447,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1560,c_2445])).

%------------------------------------------------------------------------------
