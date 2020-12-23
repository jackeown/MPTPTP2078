%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1638+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:10 EST 2020

% Result     : Theorem 4.23s
% Output     : CNFRefutation 4.23s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 417 expanded)
%              Number of leaves         :   33 ( 152 expanded)
%              Depth                    :   18
%              Number of atoms          :  230 (1149 expanded)
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

tff(f_136,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r2_hidden(C,k6_waybel_0(A,B))
                <=> r1_orders_2(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_waybel_0)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_107,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k4_waybel_0(A,B) = a_2_1_waybel_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_waybel_0)).

tff(f_34,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k6_waybel_0(A,B) = k4_waybel_0(A,k6_domain_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_waybel_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_90,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_waybel_0)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_52,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ r2_hidden('#skF_7',k6_waybel_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_68,plain,(
    ~ r2_hidden('#skF_7',k6_waybel_0('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_44,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_58,plain,
    ( r2_hidden('#skF_7',k6_waybel_0('#skF_5','#skF_6'))
    | r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_69,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_48,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_20,plain,(
    ! [A_13] :
      ( l1_struct_0(A_13)
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_72,plain,(
    ! [A_54,B_55] :
      ( k6_domain_1(A_54,B_55) = k1_tarski(B_55)
      | ~ m1_subset_1(B_55,A_54)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_79,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_44,c_72])).

tff(c_92,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_22,plain,(
    ! [A_14] :
      ( ~ v1_xboole_0(u1_struct_0(A_14))
      | ~ l1_struct_0(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_95,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_92,c_22])).

tff(c_98,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_95])).

tff(c_101,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_98])).

tff(c_105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_101])).

tff(c_107,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_80,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_46,c_72])).

tff(c_108,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_108])).

tff(c_110,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k6_domain_1(A_9,B_10),k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_126,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_16])).

tff(c_130,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_126])).

tff(c_131,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_130])).

tff(c_223,plain,(
    ! [A_71,B_72] :
      ( k4_waybel_0(A_71,B_72) = a_2_1_waybel_0(A_71,B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_orders_2(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_226,plain,
    ( k4_waybel_0('#skF_5',k1_tarski('#skF_6')) = a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_131,c_223])).

tff(c_236,plain,
    ( k4_waybel_0('#skF_5',k1_tarski('#skF_6')) = a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_226])).

tff(c_237,plain,(
    k4_waybel_0('#skF_5',k1_tarski('#skF_6')) = a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_236])).

tff(c_293,plain,(
    ! [A_79,B_80] :
      ( k4_waybel_0(A_79,k6_domain_1(u1_struct_0(A_79),B_80)) = k6_waybel_0(A_79,B_80)
      | ~ m1_subset_1(B_80,u1_struct_0(A_79))
      | ~ l1_orders_2(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_302,plain,
    ( k4_waybel_0('#skF_5',k1_tarski('#skF_6')) = k6_waybel_0('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_293])).

tff(c_309,plain,
    ( a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6')) = k6_waybel_0('#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_237,c_302])).

tff(c_310,plain,(
    a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6')) = k6_waybel_0('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_309])).

tff(c_6,plain,(
    ! [C_8] : r2_hidden(C_8,k1_tarski(C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_983,plain,(
    ! [D_136,B_137,C_138,E_139] :
      ( r2_hidden(D_136,a_2_1_waybel_0(B_137,C_138))
      | ~ r2_hidden(E_139,C_138)
      | ~ r1_orders_2(B_137,E_139,D_136)
      | ~ m1_subset_1(E_139,u1_struct_0(B_137))
      | ~ m1_subset_1(D_136,u1_struct_0(B_137))
      | ~ m1_subset_1(C_138,k1_zfmisc_1(u1_struct_0(B_137)))
      | ~ l1_orders_2(B_137)
      | v2_struct_0(B_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1182,plain,(
    ! [D_153,B_154,C_155] :
      ( r2_hidden(D_153,a_2_1_waybel_0(B_154,k1_tarski(C_155)))
      | ~ r1_orders_2(B_154,C_155,D_153)
      | ~ m1_subset_1(C_155,u1_struct_0(B_154))
      | ~ m1_subset_1(D_153,u1_struct_0(B_154))
      | ~ m1_subset_1(k1_tarski(C_155),k1_zfmisc_1(u1_struct_0(B_154)))
      | ~ l1_orders_2(B_154)
      | v2_struct_0(B_154) ) ),
    inference(resolution,[status(thm)],[c_6,c_983])).

tff(c_1188,plain,(
    ! [D_153] :
      ( r2_hidden(D_153,a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6')))
      | ~ r1_orders_2('#skF_5','#skF_6',D_153)
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(D_153,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_131,c_1182])).

tff(c_1201,plain,(
    ! [D_153] :
      ( r2_hidden(D_153,k6_waybel_0('#skF_5','#skF_6'))
      | ~ r1_orders_2('#skF_5','#skF_6',D_153)
      | ~ m1_subset_1(D_153,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_310,c_1188])).

tff(c_1207,plain,(
    ! [D_156] :
      ( r2_hidden(D_156,k6_waybel_0('#skF_5','#skF_6'))
      | ~ r1_orders_2('#skF_5','#skF_6',D_156)
      | ~ m1_subset_1(D_156,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1201])).

tff(c_1231,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1207,c_68])).

tff(c_1248,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_69,c_1231])).

tff(c_1249,plain,(
    r2_hidden('#skF_7',k6_waybel_0('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1249])).

tff(c_1252,plain,(
    ~ r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1257,plain,(
    ! [A_160,B_161] :
      ( k6_domain_1(A_160,B_161) = k1_tarski(B_161)
      | ~ m1_subset_1(B_161,A_160)
      | v1_xboole_0(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1264,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_44,c_1257])).

tff(c_1267,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1264])).

tff(c_1270,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1267,c_22])).

tff(c_1273,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1270])).

tff(c_1276,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_1273])).

tff(c_1280,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1276])).

tff(c_1282,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1264])).

tff(c_1265,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_46,c_1257])).

tff(c_1283,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1265])).

tff(c_1284,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1282,c_1283])).

tff(c_1285,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_1265])).

tff(c_1296,plain,(
    ! [A_167,B_168] :
      ( m1_subset_1(k6_domain_1(A_167,B_168),k1_zfmisc_1(A_167))
      | ~ m1_subset_1(B_168,A_167)
      | v1_xboole_0(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1306,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1285,c_1296])).

tff(c_1314,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1306])).

tff(c_1315,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1282,c_1314])).

tff(c_1253,plain,(
    r2_hidden('#skF_7',k6_waybel_0('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1386,plain,(
    ! [A_177,B_178] :
      ( k4_waybel_0(A_177,B_178) = a_2_1_waybel_0(A_177,B_178)
      | ~ m1_subset_1(B_178,k1_zfmisc_1(u1_struct_0(A_177)))
      | ~ l1_orders_2(A_177)
      | v2_struct_0(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1392,plain,
    ( k4_waybel_0('#skF_5',k1_tarski('#skF_6')) = a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1315,c_1386])).

tff(c_1403,plain,
    ( k4_waybel_0('#skF_5',k1_tarski('#skF_6')) = a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1392])).

tff(c_1404,plain,(
    k4_waybel_0('#skF_5',k1_tarski('#skF_6')) = a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1403])).

tff(c_1478,plain,(
    ! [A_188,B_189] :
      ( k4_waybel_0(A_188,k6_domain_1(u1_struct_0(A_188),B_189)) = k6_waybel_0(A_188,B_189)
      | ~ m1_subset_1(B_189,u1_struct_0(A_188))
      | ~ l1_orders_2(A_188)
      | v2_struct_0(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1487,plain,
    ( k4_waybel_0('#skF_5',k1_tarski('#skF_6')) = k6_waybel_0('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1285,c_1478])).

tff(c_1494,plain,
    ( a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6')) = k6_waybel_0('#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1404,c_1487])).

tff(c_1495,plain,(
    a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6')) = k6_waybel_0('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1494])).

tff(c_1602,plain,(
    ! [A_200,B_201,C_202] :
      ( '#skF_3'(A_200,B_201,C_202) = A_200
      | ~ r2_hidden(A_200,a_2_1_waybel_0(B_201,C_202))
      | ~ m1_subset_1(C_202,k1_zfmisc_1(u1_struct_0(B_201)))
      | ~ l1_orders_2(B_201)
      | v2_struct_0(B_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1606,plain,(
    ! [A_200] :
      ( '#skF_3'(A_200,'#skF_5',k1_tarski('#skF_6')) = A_200
      | ~ r2_hidden(A_200,k6_waybel_0('#skF_5','#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1495,c_1602])).

tff(c_1617,plain,(
    ! [A_200] :
      ( '#skF_3'(A_200,'#skF_5',k1_tarski('#skF_6')) = A_200
      | ~ r2_hidden(A_200,k6_waybel_0('#skF_5','#skF_6'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1315,c_1606])).

tff(c_1640,plain,(
    ! [A_204] :
      ( '#skF_3'(A_204,'#skF_5',k1_tarski('#skF_6')) = A_204
      | ~ r2_hidden(A_204,k6_waybel_0('#skF_5','#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1617])).

tff(c_1654,plain,(
    '#skF_3'('#skF_7','#skF_5',k1_tarski('#skF_6')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1253,c_1640])).

tff(c_1694,plain,(
    ! [A_209,B_210,C_211] :
      ( r2_hidden('#skF_4'(A_209,B_210,C_211),C_211)
      | ~ r2_hidden(A_209,a_2_1_waybel_0(B_210,C_211))
      | ~ m1_subset_1(C_211,k1_zfmisc_1(u1_struct_0(B_210)))
      | ~ l1_orders_2(B_210)
      | v2_struct_0(B_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1700,plain,(
    ! [A_209] :
      ( r2_hidden('#skF_4'(A_209,'#skF_5',k1_tarski('#skF_6')),k1_tarski('#skF_6'))
      | ~ r2_hidden(A_209,a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6')))
      | ~ l1_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1315,c_1694])).

tff(c_1711,plain,(
    ! [A_209] :
      ( r2_hidden('#skF_4'(A_209,'#skF_5',k1_tarski('#skF_6')),k1_tarski('#skF_6'))
      | ~ r2_hidden(A_209,k6_waybel_0('#skF_5','#skF_6'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1495,c_1700])).

tff(c_1748,plain,(
    ! [A_217] :
      ( r2_hidden('#skF_4'(A_217,'#skF_5',k1_tarski('#skF_6')),k1_tarski('#skF_6'))
      | ~ r2_hidden(A_217,k6_waybel_0('#skF_5','#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1711])).

tff(c_4,plain,(
    ! [C_8,A_4] :
      ( C_8 = A_4
      | ~ r2_hidden(C_8,k1_tarski(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1771,plain,(
    ! [A_219] :
      ( '#skF_4'(A_219,'#skF_5',k1_tarski('#skF_6')) = '#skF_6'
      | ~ r2_hidden(A_219,k6_waybel_0('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_1748,c_4])).

tff(c_1785,plain,(
    '#skF_4'('#skF_7','#skF_5',k1_tarski('#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1253,c_1771])).

tff(c_2153,plain,(
    ! [B_239,A_240,C_241] :
      ( r1_orders_2(B_239,'#skF_4'(A_240,B_239,C_241),'#skF_3'(A_240,B_239,C_241))
      | ~ r2_hidden(A_240,a_2_1_waybel_0(B_239,C_241))
      | ~ m1_subset_1(C_241,k1_zfmisc_1(u1_struct_0(B_239)))
      | ~ l1_orders_2(B_239)
      | v2_struct_0(B_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2162,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_3'('#skF_7','#skF_5',k1_tarski('#skF_6')))
    | ~ r2_hidden('#skF_7',a_2_1_waybel_0('#skF_5',k1_tarski('#skF_6')))
    | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1785,c_2153])).

tff(c_2173,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_7')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1315,c_1253,c_1495,c_1654,c_2162])).

tff(c_2175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1252,c_2173])).

%------------------------------------------------------------------------------
