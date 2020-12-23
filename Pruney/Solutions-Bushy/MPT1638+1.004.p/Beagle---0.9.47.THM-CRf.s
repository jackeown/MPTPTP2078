%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1638+1.004 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:10 EST 2020

% Result     : Theorem 5.25s
% Output     : CNFRefutation 5.60s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 413 expanded)
%              Number of leaves         :   33 ( 151 expanded)
%              Depth                    :   18
%              Number of atoms          :  228 (1139 expanded)
%              Number of equality atoms :   38 ( 146 expanded)
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

tff(f_130,negated_conjecture,(
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
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_44,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_58,plain,
    ( r2_hidden('#skF_7',k6_waybel_0('#skF_5','#skF_6'))
    | r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_73,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_48,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_18,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_orders_2(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_97,plain,(
    ! [A_54,B_55] :
      ( k6_domain_1(A_54,B_55) = k1_tarski(B_55)
      | ~ m1_subset_1(B_55,A_54)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_108,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_44,c_97])).

tff(c_110,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_20,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(u1_struct_0(A_12))
      | ~ l1_struct_0(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_113,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_110,c_20])).

tff(c_116,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_113])).

tff(c_119,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_116])).

tff(c_123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_119])).

tff(c_125,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_109,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_46,c_97])).

tff(c_126,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_109])).

tff(c_127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_126])).

tff(c_128,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_150,plain,(
    ! [A_62,B_63] :
      ( m1_subset_1(k6_domain_1(A_62,B_63),k1_zfmisc_1(A_62))
      | ~ m1_subset_1(B_63,A_62)
      | v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_164,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_150])).

tff(c_173,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_164])).

tff(c_174,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_173])).

tff(c_352,plain,(
    ! [A_84,B_85] :
      ( k4_waybel_0(A_84,B_85) = a_2_1_waybel_0(A_84,B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_orders_2(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_359,plain,
    ( k4_waybel_0('#skF_5',k1_tarski('#skF_6')) = a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_174,c_352])).

tff(c_370,plain,
    ( k4_waybel_0('#skF_5',k1_tarski('#skF_6')) = a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_359])).

tff(c_371,plain,(
    k4_waybel_0('#skF_5',k1_tarski('#skF_6')) = a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_370])).

tff(c_385,plain,(
    ! [A_86,B_87] :
      ( k4_waybel_0(A_86,k6_domain_1(u1_struct_0(A_86),B_87)) = k6_waybel_0(A_86,B_87)
      | ~ m1_subset_1(B_87,u1_struct_0(A_86))
      | ~ l1_orders_2(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_397,plain,
    ( k4_waybel_0('#skF_5',k1_tarski('#skF_6')) = k6_waybel_0('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_385])).

tff(c_404,plain,
    ( a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6')) = k6_waybel_0('#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_371,c_397])).

tff(c_405,plain,(
    a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6')) = k6_waybel_0('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_404])).

tff(c_6,plain,(
    ! [C_8] : r2_hidden(C_8,k1_tarski(C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1361,plain,(
    ! [D_156,B_157,C_158,E_159] :
      ( r2_hidden(D_156,a_2_1_waybel_0(B_157,C_158))
      | ~ r2_hidden(E_159,C_158)
      | ~ r1_orders_2(B_157,E_159,D_156)
      | ~ m1_subset_1(E_159,u1_struct_0(B_157))
      | ~ m1_subset_1(D_156,u1_struct_0(B_157))
      | ~ m1_subset_1(C_158,k1_zfmisc_1(u1_struct_0(B_157)))
      | ~ l1_orders_2(B_157)
      | v2_struct_0(B_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1588,plain,(
    ! [D_173,B_174,C_175] :
      ( r2_hidden(D_173,a_2_1_waybel_0(B_174,k1_tarski(C_175)))
      | ~ r1_orders_2(B_174,C_175,D_173)
      | ~ m1_subset_1(C_175,u1_struct_0(B_174))
      | ~ m1_subset_1(D_173,u1_struct_0(B_174))
      | ~ m1_subset_1(k1_tarski(C_175),k1_zfmisc_1(u1_struct_0(B_174)))
      | ~ l1_orders_2(B_174)
      | v2_struct_0(B_174) ) ),
    inference(resolution,[status(thm)],[c_6,c_1361])).

tff(c_1592,plain,(
    ! [D_173] :
      ( r2_hidden(D_173,a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6')))
      | ~ r1_orders_2('#skF_5','#skF_6',D_173)
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(D_173,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_174,c_1588])).

tff(c_1597,plain,(
    ! [D_173] :
      ( r2_hidden(D_173,k6_waybel_0('#skF_5','#skF_6'))
      | ~ r1_orders_2('#skF_5','#skF_6',D_173)
      | ~ m1_subset_1(D_173,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_405,c_1592])).

tff(c_1603,plain,(
    ! [D_176] :
      ( r2_hidden(D_176,k6_waybel_0('#skF_5','#skF_6'))
      | ~ r1_orders_2('#skF_5','#skF_6',D_176)
      | ~ m1_subset_1(D_176,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1597])).

tff(c_52,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ r2_hidden('#skF_7',k6_waybel_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_86,plain,(
    ~ r2_hidden('#skF_7',k6_waybel_0('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_52])).

tff(c_1622,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1603,c_86])).

tff(c_1634,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_73,c_1622])).

tff(c_1636,plain,(
    ~ r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1661,plain,(
    ! [A_185,B_186] :
      ( k6_domain_1(A_185,B_186) = k1_tarski(B_186)
      | ~ m1_subset_1(B_186,A_185)
      | v1_xboole_0(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1676,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_44,c_1661])).

tff(c_1678,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1676])).

tff(c_1681,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1678,c_20])).

tff(c_1684,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1681])).

tff(c_1687,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_1684])).

tff(c_1691,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1687])).

tff(c_1693,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1676])).

tff(c_1677,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_46,c_1661])).

tff(c_1694,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1677])).

tff(c_1695,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1693,c_1694])).

tff(c_1696,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_1677])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k6_domain_1(A_9,B_10),k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1719,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1696,c_16])).

tff(c_1723,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1719])).

tff(c_1724,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1693,c_1723])).

tff(c_1635,plain,(
    r2_hidden('#skF_7',k6_waybel_0('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1931,plain,(
    ! [A_213,B_214] :
      ( k4_waybel_0(A_213,B_214) = a_2_1_waybel_0(A_213,B_214)
      | ~ m1_subset_1(B_214,k1_zfmisc_1(u1_struct_0(A_213)))
      | ~ l1_orders_2(A_213)
      | v2_struct_0(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1938,plain,
    ( k4_waybel_0('#skF_5',k1_tarski('#skF_6')) = a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1724,c_1931])).

tff(c_1949,plain,
    ( k4_waybel_0('#skF_5',k1_tarski('#skF_6')) = a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1938])).

tff(c_1950,plain,(
    k4_waybel_0('#skF_5',k1_tarski('#skF_6')) = a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1949])).

tff(c_1964,plain,(
    ! [A_215,B_216] :
      ( k4_waybel_0(A_215,k6_domain_1(u1_struct_0(A_215),B_216)) = k6_waybel_0(A_215,B_216)
      | ~ m1_subset_1(B_216,u1_struct_0(A_215))
      | ~ l1_orders_2(A_215)
      | v2_struct_0(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1973,plain,
    ( k4_waybel_0('#skF_5',k1_tarski('#skF_6')) = k6_waybel_0('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1696,c_1964])).

tff(c_1980,plain,
    ( a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6')) = k6_waybel_0('#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1950,c_1973])).

tff(c_1981,plain,(
    a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6')) = k6_waybel_0('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1980])).

tff(c_2089,plain,(
    ! [A_226,B_227,C_228] :
      ( '#skF_3'(A_226,B_227,C_228) = A_226
      | ~ r2_hidden(A_226,a_2_1_waybel_0(B_227,C_228))
      | ~ m1_subset_1(C_228,k1_zfmisc_1(u1_struct_0(B_227)))
      | ~ l1_orders_2(B_227)
      | v2_struct_0(B_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2093,plain,(
    ! [A_226] :
      ( '#skF_3'(A_226,'#skF_5',k1_tarski('#skF_6')) = A_226
      | ~ r2_hidden(A_226,k6_waybel_0('#skF_5','#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1981,c_2089])).

tff(c_2107,plain,(
    ! [A_226] :
      ( '#skF_3'(A_226,'#skF_5',k1_tarski('#skF_6')) = A_226
      | ~ r2_hidden(A_226,k6_waybel_0('#skF_5','#skF_6'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1724,c_2093])).

tff(c_2128,plain,(
    ! [A_230] :
      ( '#skF_3'(A_230,'#skF_5',k1_tarski('#skF_6')) = A_230
      | ~ r2_hidden(A_230,k6_waybel_0('#skF_5','#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2107])).

tff(c_2148,plain,(
    '#skF_3'('#skF_7','#skF_5',k1_tarski('#skF_6')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1635,c_2128])).

tff(c_2242,plain,(
    ! [A_238,B_239,C_240] :
      ( r2_hidden('#skF_4'(A_238,B_239,C_240),C_240)
      | ~ r2_hidden(A_238,a_2_1_waybel_0(B_239,C_240))
      | ~ m1_subset_1(C_240,k1_zfmisc_1(u1_struct_0(B_239)))
      | ~ l1_orders_2(B_239)
      | v2_struct_0(B_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2250,plain,(
    ! [A_238] :
      ( r2_hidden('#skF_4'(A_238,'#skF_5',k1_tarski('#skF_6')),k1_tarski('#skF_6'))
      | ~ r2_hidden(A_238,a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6')))
      | ~ l1_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1724,c_2242])).

tff(c_2260,plain,(
    ! [A_238] :
      ( r2_hidden('#skF_4'(A_238,'#skF_5',k1_tarski('#skF_6')),k1_tarski('#skF_6'))
      | ~ r2_hidden(A_238,k6_waybel_0('#skF_5','#skF_6'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1981,c_2250])).

tff(c_2267,plain,(
    ! [A_241] :
      ( r2_hidden('#skF_4'(A_241,'#skF_5',k1_tarski('#skF_6')),k1_tarski('#skF_6'))
      | ~ r2_hidden(A_241,k6_waybel_0('#skF_5','#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2260])).

tff(c_4,plain,(
    ! [C_8,A_4] :
      ( C_8 = A_4
      | ~ r2_hidden(C_8,k1_tarski(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2280,plain,(
    ! [A_242] :
      ( '#skF_4'(A_242,'#skF_5',k1_tarski('#skF_6')) = '#skF_6'
      | ~ r2_hidden(A_242,k6_waybel_0('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_2267,c_4])).

tff(c_2300,plain,(
    '#skF_4'('#skF_7','#skF_5',k1_tarski('#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1635,c_2280])).

tff(c_2854,plain,(
    ! [B_273,A_274,C_275] :
      ( r1_orders_2(B_273,'#skF_4'(A_274,B_273,C_275),'#skF_3'(A_274,B_273,C_275))
      | ~ r2_hidden(A_274,a_2_1_waybel_0(B_273,C_275))
      | ~ m1_subset_1(C_275,k1_zfmisc_1(u1_struct_0(B_273)))
      | ~ l1_orders_2(B_273)
      | v2_struct_0(B_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2866,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_3'('#skF_7','#skF_5',k1_tarski('#skF_6')))
    | ~ r2_hidden('#skF_7',a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6')))
    | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2300,c_2854])).

tff(c_2880,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_7')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1724,c_1635,c_1981,c_2148,c_2866])).

tff(c_2882,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1636,c_2880])).

%------------------------------------------------------------------------------
