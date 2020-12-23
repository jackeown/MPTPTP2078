%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1143+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:29 EST 2020

% Result     : Theorem 4.14s
% Output     : CNFRefutation 4.22s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 424 expanded)
%              Number of leaves         :   41 ( 150 expanded)
%              Depth                    :   17
%              Number of atoms          :  180 (1082 expanded)
%              Number of equality atoms :   16 ( 129 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_orders_2 > r7_relat_2 > r2_hidden > r1_relat_2 > m1_subset_1 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > k1_tarski > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_relat_2,type,(
    r1_relat_2: ( $i * $i ) > $o )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(r7_relat_2,type,(
    r7_relat_2: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_128,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v6_orders_2(k6_domain_1(u1_struct_0(A),B),A)
              & m1_subset_1(k6_domain_1(u1_struct_0(A),B),k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_107,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_100,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r7_relat_2(A,B)
        <=> ! [C,D] :
              ~ ( r2_hidden(C,B)
                & r2_hidden(D,B)
                & ~ r2_hidden(k4_tarski(C,D),A)
                & ~ r2_hidden(k4_tarski(D,C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_relat_2)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_orders_2(B,A)
          <=> r7_relat_2(u1_orders_2(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_orders_2)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v3_orders_2(A)
      <=> r1_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_orders_2)).

tff(f_113,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_relat_2(A,B)
        <=> ! [C] :
              ( r2_hidden(C,B)
             => r2_hidden(k4_tarski(C,C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_2)).

tff(c_56,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_42,plain,(
    ! [A_42] :
      ( l1_struct_0(A_42)
      | ~ l1_orders_2(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_54,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_2089,plain,(
    ! [A_1884,B_1885] :
      ( k6_domain_1(A_1884,B_1885) = k1_tarski(B_1885)
      | ~ m1_subset_1(B_1885,A_1884)
      | v1_xboole_0(A_1884) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2093,plain,
    ( k6_domain_1(u1_struct_0('#skF_6'),'#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_54,c_2089])).

tff(c_2094,plain,(
    v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_2093])).

tff(c_46,plain,(
    ! [A_44] :
      ( ~ v1_xboole_0(u1_struct_0(A_44))
      | ~ l1_struct_0(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2097,plain,
    ( ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_2094,c_46])).

tff(c_2100,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2097])).

tff(c_2103,plain,(
    ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_2100])).

tff(c_2107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2103])).

tff(c_2109,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_2093])).

tff(c_2108,plain,(
    k6_domain_1(u1_struct_0('#skF_6'),'#skF_7') = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_2093])).

tff(c_91,plain,(
    ! [A_66,B_67] :
      ( k6_domain_1(A_66,B_67) = k1_tarski(B_67)
      | ~ m1_subset_1(B_67,A_66)
      | v1_xboole_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_95,plain,
    ( k6_domain_1(u1_struct_0('#skF_6'),'#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_54,c_91])).

tff(c_96,plain,(
    v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_99,plain,
    ( ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_96,c_46])).

tff(c_102,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_99])).

tff(c_105,plain,(
    ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_102])).

tff(c_109,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_105])).

tff(c_111,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_58,plain,(
    v3_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_129,plain,(
    ! [A_72] :
      ( m1_subset_1(u1_orders_2(A_72),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_72),u1_struct_0(A_72))))
      | ~ l1_orders_2(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2,plain,(
    ! [C_3,A_1,B_2] :
      ( v1_relat_1(C_3)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_137,plain,(
    ! [A_72] :
      ( v1_relat_1(u1_orders_2(A_72))
      | ~ l1_orders_2(A_72) ) ),
    inference(resolution,[status(thm)],[c_129,c_2])).

tff(c_85,plain,(
    ! [A_64,B_65] :
      ( r2_hidden('#skF_5'(A_64,B_65),B_65)
      | r7_relat_2(A_64,B_65)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_14,plain,(
    ! [C_21,A_17] :
      ( C_21 = A_17
      | ~ r2_hidden(C_21,k1_tarski(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_90,plain,(
    ! [A_64,A_17] :
      ( '#skF_5'(A_64,k1_tarski(A_17)) = A_17
      | r7_relat_2(A_64,k1_tarski(A_17))
      | ~ v1_relat_1(A_64) ) ),
    inference(resolution,[status(thm)],[c_85,c_14])).

tff(c_110,plain,(
    k6_domain_1(u1_struct_0('#skF_6'),'#skF_7') = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_52,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_6'),'#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ v6_orders_2(k6_domain_1(u1_struct_0('#skF_6'),'#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_71,plain,(
    ~ v6_orders_2(k6_domain_1(u1_struct_0('#skF_6'),'#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_112,plain,(
    ~ v6_orders_2(k1_tarski('#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_71])).

tff(c_139,plain,(
    ! [A_74,B_75] :
      ( m1_subset_1(k6_domain_1(A_74,B_75),k1_zfmisc_1(A_74))
      | ~ m1_subset_1(B_75,A_74)
      | v1_xboole_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_149,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_139])).

tff(c_153,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_149])).

tff(c_154,plain,(
    m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_153])).

tff(c_613,plain,(
    ! [B_906,A_907] :
      ( v6_orders_2(B_906,A_907)
      | ~ r7_relat_2(u1_orders_2(A_907),B_906)
      | ~ m1_subset_1(B_906,k1_zfmisc_1(u1_struct_0(A_907)))
      | ~ l1_orders_2(A_907) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_622,plain,
    ( v6_orders_2(k1_tarski('#skF_7'),'#skF_6')
    | ~ r7_relat_2(u1_orders_2('#skF_6'),k1_tarski('#skF_7'))
    | ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_154,c_613])).

tff(c_629,plain,
    ( v6_orders_2(k1_tarski('#skF_7'),'#skF_6')
    | ~ r7_relat_2(u1_orders_2('#skF_6'),k1_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_622])).

tff(c_630,plain,(
    ~ r7_relat_2(u1_orders_2('#skF_6'),k1_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_629])).

tff(c_638,plain,
    ( '#skF_5'(u1_orders_2('#skF_6'),k1_tarski('#skF_7')) = '#skF_7'
    | ~ v1_relat_1(u1_orders_2('#skF_6')) ),
    inference(resolution,[status(thm)],[c_90,c_630])).

tff(c_655,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_638])).

tff(c_658,plain,(
    ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_137,c_655])).

tff(c_662,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_658])).

tff(c_664,plain,(
    v1_relat_1(u1_orders_2('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_638])).

tff(c_28,plain,(
    ! [A_22] :
      ( r1_relat_2(u1_orders_2(A_22),u1_struct_0(A_22))
      | ~ v3_orders_2(A_22)
      | ~ l1_orders_2(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_50,plain,(
    ! [A_47,B_48] :
      ( r2_hidden(A_47,B_48)
      | v1_xboole_0(B_48)
      | ~ m1_subset_1(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_176,plain,(
    ! [C_88,A_89,B_90] :
      ( r2_hidden(k4_tarski(C_88,C_88),A_89)
      | ~ r2_hidden(C_88,B_90)
      | ~ r1_relat_2(A_89,B_90)
      | ~ v1_relat_1(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_979,plain,(
    ! [A_1286,A_1287,B_1288] :
      ( r2_hidden(k4_tarski(A_1286,A_1286),A_1287)
      | ~ r1_relat_2(A_1287,B_1288)
      | ~ v1_relat_1(A_1287)
      | v1_xboole_0(B_1288)
      | ~ m1_subset_1(A_1286,B_1288) ) ),
    inference(resolution,[status(thm)],[c_50,c_176])).

tff(c_1973,plain,(
    ! [A_1854,A_1855] :
      ( r2_hidden(k4_tarski(A_1854,A_1854),u1_orders_2(A_1855))
      | ~ v1_relat_1(u1_orders_2(A_1855))
      | v1_xboole_0(u1_struct_0(A_1855))
      | ~ m1_subset_1(A_1854,u1_struct_0(A_1855))
      | ~ v3_orders_2(A_1855)
      | ~ l1_orders_2(A_1855) ) ),
    inference(resolution,[status(thm)],[c_28,c_979])).

tff(c_123,plain,(
    ! [A_70,B_71] :
      ( r2_hidden('#skF_4'(A_70,B_71),B_71)
      | r7_relat_2(A_70,B_71)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_128,plain,(
    ! [A_70,A_17] :
      ( '#skF_4'(A_70,k1_tarski(A_17)) = A_17
      | r7_relat_2(A_70,k1_tarski(A_17))
      | ~ v1_relat_1(A_70) ) ),
    inference(resolution,[status(thm)],[c_123,c_14])).

tff(c_639,plain,
    ( '#skF_4'(u1_orders_2('#skF_6'),k1_tarski('#skF_7')) = '#skF_7'
    | ~ v1_relat_1(u1_orders_2('#skF_6')) ),
    inference(resolution,[status(thm)],[c_128,c_630])).

tff(c_666,plain,(
    '#skF_4'(u1_orders_2('#skF_6'),k1_tarski('#skF_7')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_664,c_639])).

tff(c_663,plain,(
    '#skF_5'(u1_orders_2('#skF_6'),k1_tarski('#skF_7')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_638])).

tff(c_34,plain,(
    ! [A_23,B_33] :
      ( ~ r2_hidden(k4_tarski('#skF_4'(A_23,B_33),'#skF_5'(A_23,B_33)),A_23)
      | r7_relat_2(A_23,B_33)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_696,plain,
    ( ~ r2_hidden(k4_tarski('#skF_4'(u1_orders_2('#skF_6'),k1_tarski('#skF_7')),'#skF_7'),u1_orders_2('#skF_6'))
    | r7_relat_2(u1_orders_2('#skF_6'),k1_tarski('#skF_7'))
    | ~ v1_relat_1(u1_orders_2('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_663,c_34])).

tff(c_709,plain,
    ( ~ r2_hidden(k4_tarski('#skF_7','#skF_7'),u1_orders_2('#skF_6'))
    | r7_relat_2(u1_orders_2('#skF_6'),k1_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_664,c_666,c_696])).

tff(c_710,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_7'),u1_orders_2('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_630,c_709])).

tff(c_1982,plain,
    ( ~ v1_relat_1(u1_orders_2('#skF_6'))
    | v1_xboole_0(u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ v3_orders_2('#skF_6')
    | ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_1973,c_710])).

tff(c_2065,plain,(
    v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_54,c_664,c_1982])).

tff(c_2067,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_2065])).

tff(c_2068,plain,(
    ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_6'),'#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_2110,plain,(
    ~ m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2108,c_2068])).

tff(c_2138,plain,(
    ! [A_1892,B_1893] :
      ( m1_subset_1(k6_domain_1(A_1892,B_1893),k1_zfmisc_1(A_1892))
      | ~ m1_subset_1(B_1893,A_1892)
      | v1_xboole_0(A_1892) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2148,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2108,c_2138])).

tff(c_2152,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2148])).

tff(c_2154,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2109,c_2110,c_2152])).

%------------------------------------------------------------------------------
