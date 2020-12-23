%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:21 EST 2020

% Result     : Theorem 7.73s
% Output     : CNFRefutation 7.73s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 145 expanded)
%              Number of leaves         :   33 (  62 expanded)
%              Depth                    :   14
%              Number of atoms          :  165 ( 289 expanded)
%              Number of equality atoms :   19 (  33 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(k6_relat_1(B),C)
         => ( r1_tarski(B,k1_relset_1(A,B,C))
            & B = k2_relset_1(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_56,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_5669,plain,(
    ! [A_515,B_516,C_517] :
      ( k2_relset_1(A_515,B_516,C_517) = k2_relat_1(C_517)
      | ~ m1_subset_1(C_517,k1_zfmisc_1(k2_zfmisc_1(A_515,B_516))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_5678,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_5669])).

tff(c_466,plain,(
    ! [A_113,B_114,C_115] :
      ( k1_relset_1(A_113,B_114,C_115) = k1_relat_1(C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_475,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_466])).

tff(c_44,plain,
    ( k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3'
    | ~ r1_tarski('#skF_3',k1_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_80,plain,(
    ~ r1_tarski('#skF_3',k1_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_476,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_475,c_80])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_81,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_90,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_81])).

tff(c_28,plain,(
    ! [A_15] :
      ( r1_tarski(A_15,k2_zfmisc_1(k1_relat_1(A_15),k2_relat_1(A_15)))
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_46,plain,(
    r1_tarski(k6_relat_1('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_354,plain,(
    ! [C_89,B_90,A_91] :
      ( r2_hidden(C_89,B_90)
      | ~ r2_hidden(C_89,A_91)
      | ~ r1_tarski(A_91,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_500,plain,(
    ! [A_117,B_118,B_119] :
      ( r2_hidden('#skF_1'(A_117,B_118),B_119)
      | ~ r1_tarski(A_117,B_119)
      | r1_tarski(A_117,B_118) ) ),
    inference(resolution,[status(thm)],[c_6,c_354])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1020,plain,(
    ! [A_178,B_179,B_180,B_181] :
      ( r2_hidden('#skF_1'(A_178,B_179),B_180)
      | ~ r1_tarski(B_181,B_180)
      | ~ r1_tarski(A_178,B_181)
      | r1_tarski(A_178,B_179) ) ),
    inference(resolution,[status(thm)],[c_500,c_2])).

tff(c_1177,plain,(
    ! [A_211,B_212] :
      ( r2_hidden('#skF_1'(A_211,B_212),'#skF_4')
      | ~ r1_tarski(A_211,k6_relat_1('#skF_3'))
      | r1_tarski(A_211,B_212) ) ),
    inference(resolution,[status(thm)],[c_46,c_1020])).

tff(c_1954,plain,(
    ! [A_260,B_261,B_262] :
      ( r2_hidden('#skF_1'(A_260,B_261),B_262)
      | ~ r1_tarski('#skF_4',B_262)
      | ~ r1_tarski(A_260,k6_relat_1('#skF_3'))
      | r1_tarski(A_260,B_261) ) ),
    inference(resolution,[status(thm)],[c_1177,c_2])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2118,plain,(
    ! [B_273,A_274] :
      ( ~ r1_tarski('#skF_4',B_273)
      | ~ r1_tarski(A_274,k6_relat_1('#skF_3'))
      | r1_tarski(A_274,B_273) ) ),
    inference(resolution,[status(thm)],[c_1954,c_4])).

tff(c_2127,plain,(
    ! [A_274] :
      ( ~ r1_tarski(A_274,k6_relat_1('#skF_3'))
      | r1_tarski(A_274,k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4')))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_2118])).

tff(c_4562,plain,(
    ! [A_435] :
      ( ~ r1_tarski(A_435,k6_relat_1('#skF_3'))
      | r1_tarski(A_435,k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_2127])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_282,plain,(
    ! [C_76,A_77,B_78] :
      ( v4_relat_1(C_76,A_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_290,plain,(
    ! [A_8,A_77,B_78] :
      ( v4_relat_1(A_8,A_77)
      | ~ r1_tarski(A_8,k2_zfmisc_1(A_77,B_78)) ) ),
    inference(resolution,[status(thm)],[c_16,c_282])).

tff(c_4625,plain,(
    ! [A_436] :
      ( v4_relat_1(A_436,k1_relat_1('#skF_4'))
      | ~ r1_tarski(A_436,k6_relat_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_4562,c_290])).

tff(c_26,plain,(
    ! [A_14] : v1_relat_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_30,plain,(
    ! [A_16] : k1_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_125,plain,(
    ! [B_51,A_52] :
      ( r1_tarski(k1_relat_1(B_51),A_52)
      | ~ v4_relat_1(B_51,A_52)
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_134,plain,(
    ! [A_16,A_52] :
      ( r1_tarski(A_16,A_52)
      | ~ v4_relat_1(k6_relat_1(A_16),A_52)
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_125])).

tff(c_138,plain,(
    ! [A_16,A_52] :
      ( r1_tarski(A_16,A_52)
      | ~ v4_relat_1(k6_relat_1(A_16),A_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_134])).

tff(c_5355,plain,(
    ! [A_453] :
      ( r1_tarski(A_453,k1_relat_1('#skF_4'))
      | ~ r1_tarski(k6_relat_1(A_453),k6_relat_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_4625,c_138])).

tff(c_5359,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_12,c_5355])).

tff(c_5363,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_476,c_5359])).

tff(c_5364,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_5679,plain,(
    k2_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5678,c_5364])).

tff(c_5366,plain,(
    ! [C_454,A_455,B_456] :
      ( v1_relat_1(C_454)
      | ~ m1_subset_1(C_454,k1_zfmisc_1(k2_zfmisc_1(A_455,B_456))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_5375,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_5366])).

tff(c_5413,plain,(
    ! [C_468,B_469,A_470] :
      ( v5_relat_1(C_468,B_469)
      | ~ m1_subset_1(C_468,k1_zfmisc_1(k2_zfmisc_1(A_470,B_469))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_5422,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_5413])).

tff(c_5579,plain,(
    ! [C_499,B_500,A_501] :
      ( r2_hidden(C_499,B_500)
      | ~ r2_hidden(C_499,A_501)
      | ~ r1_tarski(A_501,B_500) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5731,plain,(
    ! [A_524,B_525,B_526] :
      ( r2_hidden('#skF_1'(A_524,B_525),B_526)
      | ~ r1_tarski(A_524,B_526)
      | r1_tarski(A_524,B_525) ) ),
    inference(resolution,[status(thm)],[c_6,c_5579])).

tff(c_6459,plain,(
    ! [A_624,B_625,B_626,B_627] :
      ( r2_hidden('#skF_1'(A_624,B_625),B_626)
      | ~ r1_tarski(B_627,B_626)
      | ~ r1_tarski(A_624,B_627)
      | r1_tarski(A_624,B_625) ) ),
    inference(resolution,[status(thm)],[c_5731,c_2])).

tff(c_6686,plain,(
    ! [A_644,B_645] :
      ( r2_hidden('#skF_1'(A_644,B_645),'#skF_4')
      | ~ r1_tarski(A_644,k6_relat_1('#skF_3'))
      | r1_tarski(A_644,B_645) ) ),
    inference(resolution,[status(thm)],[c_46,c_6459])).

tff(c_7721,plain,(
    ! [A_708,B_709,B_710] :
      ( r2_hidden('#skF_1'(A_708,B_709),B_710)
      | ~ r1_tarski('#skF_4',B_710)
      | ~ r1_tarski(A_708,k6_relat_1('#skF_3'))
      | r1_tarski(A_708,B_709) ) ),
    inference(resolution,[status(thm)],[c_6686,c_2])).

tff(c_7787,plain,(
    ! [B_715,A_716] :
      ( ~ r1_tarski('#skF_4',B_715)
      | ~ r1_tarski(A_716,k6_relat_1('#skF_3'))
      | r1_tarski(A_716,B_715) ) ),
    inference(resolution,[status(thm)],[c_7721,c_4])).

tff(c_7799,plain,(
    ! [A_716] :
      ( ~ r1_tarski(A_716,k6_relat_1('#skF_3'))
      | r1_tarski(A_716,k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4')))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_7787])).

tff(c_10195,plain,(
    ! [A_860] :
      ( ~ r1_tarski(A_860,k6_relat_1('#skF_3'))
      | r1_tarski(A_860,k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5375,c_7799])).

tff(c_5421,plain,(
    ! [A_8,B_469,A_470] :
      ( v5_relat_1(A_8,B_469)
      | ~ r1_tarski(A_8,k2_zfmisc_1(A_470,B_469)) ) ),
    inference(resolution,[status(thm)],[c_16,c_5413])).

tff(c_10339,plain,(
    ! [A_864] :
      ( v5_relat_1(A_864,k2_relat_1('#skF_4'))
      | ~ r1_tarski(A_864,k6_relat_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_10195,c_5421])).

tff(c_32,plain,(
    ! [A_16] : k2_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_5423,plain,(
    ! [B_471,A_472] :
      ( r1_tarski(k2_relat_1(B_471),A_472)
      | ~ v5_relat_1(B_471,A_472)
      | ~ v1_relat_1(B_471) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_5432,plain,(
    ! [A_16,A_472] :
      ( r1_tarski(A_16,A_472)
      | ~ v5_relat_1(k6_relat_1(A_16),A_472)
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_5423])).

tff(c_5436,plain,(
    ! [A_16,A_472] :
      ( r1_tarski(A_16,A_472)
      | ~ v5_relat_1(k6_relat_1(A_16),A_472) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_5432])).

tff(c_10395,plain,(
    ! [A_866] :
      ( r1_tarski(A_866,k2_relat_1('#skF_4'))
      | ~ r1_tarski(k6_relat_1(A_866),k6_relat_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_10339,c_5436])).

tff(c_10400,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_12,c_10395])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_5433,plain,(
    ! [B_471,A_472] :
      ( k2_relat_1(B_471) = A_472
      | ~ r1_tarski(A_472,k2_relat_1(B_471))
      | ~ v5_relat_1(B_471,A_472)
      | ~ v1_relat_1(B_471) ) ),
    inference(resolution,[status(thm)],[c_5423,c_8])).

tff(c_10407,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10400,c_5433])).

tff(c_10414,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5375,c_5422,c_10407])).

tff(c_10416,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5679,c_10414])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:37:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.73/2.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.73/2.81  
% 7.73/2.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.73/2.81  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 7.73/2.81  
% 7.73/2.81  %Foreground sorts:
% 7.73/2.81  
% 7.73/2.81  
% 7.73/2.81  %Background operators:
% 7.73/2.81  
% 7.73/2.81  
% 7.73/2.81  %Foreground operators:
% 7.73/2.81  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.73/2.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.73/2.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.73/2.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.73/2.81  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.73/2.81  tff('#skF_2', type, '#skF_2': $i).
% 7.73/2.81  tff('#skF_3', type, '#skF_3': $i).
% 7.73/2.81  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.73/2.81  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.73/2.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.73/2.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.73/2.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.73/2.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.73/2.81  tff('#skF_4', type, '#skF_4': $i).
% 7.73/2.81  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.73/2.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.73/2.81  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.73/2.81  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.73/2.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.73/2.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.73/2.81  
% 7.73/2.83  tff(f_91, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(B), C) => (r1_tarski(B, k1_relset_1(A, B, C)) & (B = k2_relset_1(A, B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_relset_1)).
% 7.73/2.83  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.73/2.83  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.73/2.83  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.73/2.83  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.73/2.83  tff(f_60, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 7.73/2.83  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.73/2.83  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.73/2.83  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.73/2.83  tff(f_56, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 7.73/2.83  tff(f_64, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 7.73/2.83  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 7.73/2.83  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 7.73/2.83  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.73/2.83  tff(c_5669, plain, (![A_515, B_516, C_517]: (k2_relset_1(A_515, B_516, C_517)=k2_relat_1(C_517) | ~m1_subset_1(C_517, k1_zfmisc_1(k2_zfmisc_1(A_515, B_516))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.73/2.83  tff(c_5678, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_5669])).
% 7.73/2.83  tff(c_466, plain, (![A_113, B_114, C_115]: (k1_relset_1(A_113, B_114, C_115)=k1_relat_1(C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.73/2.83  tff(c_475, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_466])).
% 7.73/2.83  tff(c_44, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | ~r1_tarski('#skF_3', k1_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.73/2.83  tff(c_80, plain, (~r1_tarski('#skF_3', k1_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_44])).
% 7.73/2.83  tff(c_476, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_475, c_80])).
% 7.73/2.83  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.73/2.83  tff(c_81, plain, (![C_37, A_38, B_39]: (v1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.73/2.83  tff(c_90, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_81])).
% 7.73/2.83  tff(c_28, plain, (![A_15]: (r1_tarski(A_15, k2_zfmisc_1(k1_relat_1(A_15), k2_relat_1(A_15))) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.73/2.83  tff(c_46, plain, (r1_tarski(k6_relat_1('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.73/2.83  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.73/2.83  tff(c_354, plain, (![C_89, B_90, A_91]: (r2_hidden(C_89, B_90) | ~r2_hidden(C_89, A_91) | ~r1_tarski(A_91, B_90))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.73/2.83  tff(c_500, plain, (![A_117, B_118, B_119]: (r2_hidden('#skF_1'(A_117, B_118), B_119) | ~r1_tarski(A_117, B_119) | r1_tarski(A_117, B_118))), inference(resolution, [status(thm)], [c_6, c_354])).
% 7.73/2.83  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.73/2.83  tff(c_1020, plain, (![A_178, B_179, B_180, B_181]: (r2_hidden('#skF_1'(A_178, B_179), B_180) | ~r1_tarski(B_181, B_180) | ~r1_tarski(A_178, B_181) | r1_tarski(A_178, B_179))), inference(resolution, [status(thm)], [c_500, c_2])).
% 7.73/2.83  tff(c_1177, plain, (![A_211, B_212]: (r2_hidden('#skF_1'(A_211, B_212), '#skF_4') | ~r1_tarski(A_211, k6_relat_1('#skF_3')) | r1_tarski(A_211, B_212))), inference(resolution, [status(thm)], [c_46, c_1020])).
% 7.73/2.83  tff(c_1954, plain, (![A_260, B_261, B_262]: (r2_hidden('#skF_1'(A_260, B_261), B_262) | ~r1_tarski('#skF_4', B_262) | ~r1_tarski(A_260, k6_relat_1('#skF_3')) | r1_tarski(A_260, B_261))), inference(resolution, [status(thm)], [c_1177, c_2])).
% 7.73/2.83  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.73/2.83  tff(c_2118, plain, (![B_273, A_274]: (~r1_tarski('#skF_4', B_273) | ~r1_tarski(A_274, k6_relat_1('#skF_3')) | r1_tarski(A_274, B_273))), inference(resolution, [status(thm)], [c_1954, c_4])).
% 7.73/2.83  tff(c_2127, plain, (![A_274]: (~r1_tarski(A_274, k6_relat_1('#skF_3')) | r1_tarski(A_274, k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_2118])).
% 7.73/2.83  tff(c_4562, plain, (![A_435]: (~r1_tarski(A_435, k6_relat_1('#skF_3')) | r1_tarski(A_435, k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_2127])).
% 7.73/2.83  tff(c_16, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.73/2.83  tff(c_282, plain, (![C_76, A_77, B_78]: (v4_relat_1(C_76, A_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.73/2.83  tff(c_290, plain, (![A_8, A_77, B_78]: (v4_relat_1(A_8, A_77) | ~r1_tarski(A_8, k2_zfmisc_1(A_77, B_78)))), inference(resolution, [status(thm)], [c_16, c_282])).
% 7.73/2.83  tff(c_4625, plain, (![A_436]: (v4_relat_1(A_436, k1_relat_1('#skF_4')) | ~r1_tarski(A_436, k6_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_4562, c_290])).
% 7.73/2.83  tff(c_26, plain, (![A_14]: (v1_relat_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.73/2.83  tff(c_30, plain, (![A_16]: (k1_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.73/2.83  tff(c_125, plain, (![B_51, A_52]: (r1_tarski(k1_relat_1(B_51), A_52) | ~v4_relat_1(B_51, A_52) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.73/2.83  tff(c_134, plain, (![A_16, A_52]: (r1_tarski(A_16, A_52) | ~v4_relat_1(k6_relat_1(A_16), A_52) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_125])).
% 7.73/2.83  tff(c_138, plain, (![A_16, A_52]: (r1_tarski(A_16, A_52) | ~v4_relat_1(k6_relat_1(A_16), A_52))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_134])).
% 7.73/2.83  tff(c_5355, plain, (![A_453]: (r1_tarski(A_453, k1_relat_1('#skF_4')) | ~r1_tarski(k6_relat_1(A_453), k6_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_4625, c_138])).
% 7.73/2.83  tff(c_5359, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_12, c_5355])).
% 7.73/2.83  tff(c_5363, plain, $false, inference(negUnitSimplification, [status(thm)], [c_476, c_5359])).
% 7.73/2.83  tff(c_5364, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(splitRight, [status(thm)], [c_44])).
% 7.73/2.83  tff(c_5679, plain, (k2_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5678, c_5364])).
% 7.73/2.83  tff(c_5366, plain, (![C_454, A_455, B_456]: (v1_relat_1(C_454) | ~m1_subset_1(C_454, k1_zfmisc_1(k2_zfmisc_1(A_455, B_456))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.73/2.83  tff(c_5375, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_5366])).
% 7.73/2.83  tff(c_5413, plain, (![C_468, B_469, A_470]: (v5_relat_1(C_468, B_469) | ~m1_subset_1(C_468, k1_zfmisc_1(k2_zfmisc_1(A_470, B_469))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.73/2.83  tff(c_5422, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_5413])).
% 7.73/2.83  tff(c_5579, plain, (![C_499, B_500, A_501]: (r2_hidden(C_499, B_500) | ~r2_hidden(C_499, A_501) | ~r1_tarski(A_501, B_500))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.73/2.83  tff(c_5731, plain, (![A_524, B_525, B_526]: (r2_hidden('#skF_1'(A_524, B_525), B_526) | ~r1_tarski(A_524, B_526) | r1_tarski(A_524, B_525))), inference(resolution, [status(thm)], [c_6, c_5579])).
% 7.73/2.83  tff(c_6459, plain, (![A_624, B_625, B_626, B_627]: (r2_hidden('#skF_1'(A_624, B_625), B_626) | ~r1_tarski(B_627, B_626) | ~r1_tarski(A_624, B_627) | r1_tarski(A_624, B_625))), inference(resolution, [status(thm)], [c_5731, c_2])).
% 7.73/2.83  tff(c_6686, plain, (![A_644, B_645]: (r2_hidden('#skF_1'(A_644, B_645), '#skF_4') | ~r1_tarski(A_644, k6_relat_1('#skF_3')) | r1_tarski(A_644, B_645))), inference(resolution, [status(thm)], [c_46, c_6459])).
% 7.73/2.83  tff(c_7721, plain, (![A_708, B_709, B_710]: (r2_hidden('#skF_1'(A_708, B_709), B_710) | ~r1_tarski('#skF_4', B_710) | ~r1_tarski(A_708, k6_relat_1('#skF_3')) | r1_tarski(A_708, B_709))), inference(resolution, [status(thm)], [c_6686, c_2])).
% 7.73/2.83  tff(c_7787, plain, (![B_715, A_716]: (~r1_tarski('#skF_4', B_715) | ~r1_tarski(A_716, k6_relat_1('#skF_3')) | r1_tarski(A_716, B_715))), inference(resolution, [status(thm)], [c_7721, c_4])).
% 7.73/2.83  tff(c_7799, plain, (![A_716]: (~r1_tarski(A_716, k6_relat_1('#skF_3')) | r1_tarski(A_716, k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_7787])).
% 7.73/2.83  tff(c_10195, plain, (![A_860]: (~r1_tarski(A_860, k6_relat_1('#skF_3')) | r1_tarski(A_860, k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_5375, c_7799])).
% 7.73/2.83  tff(c_5421, plain, (![A_8, B_469, A_470]: (v5_relat_1(A_8, B_469) | ~r1_tarski(A_8, k2_zfmisc_1(A_470, B_469)))), inference(resolution, [status(thm)], [c_16, c_5413])).
% 7.73/2.83  tff(c_10339, plain, (![A_864]: (v5_relat_1(A_864, k2_relat_1('#skF_4')) | ~r1_tarski(A_864, k6_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_10195, c_5421])).
% 7.73/2.83  tff(c_32, plain, (![A_16]: (k2_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.73/2.83  tff(c_5423, plain, (![B_471, A_472]: (r1_tarski(k2_relat_1(B_471), A_472) | ~v5_relat_1(B_471, A_472) | ~v1_relat_1(B_471))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.73/2.83  tff(c_5432, plain, (![A_16, A_472]: (r1_tarski(A_16, A_472) | ~v5_relat_1(k6_relat_1(A_16), A_472) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_5423])).
% 7.73/2.83  tff(c_5436, plain, (![A_16, A_472]: (r1_tarski(A_16, A_472) | ~v5_relat_1(k6_relat_1(A_16), A_472))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_5432])).
% 7.73/2.83  tff(c_10395, plain, (![A_866]: (r1_tarski(A_866, k2_relat_1('#skF_4')) | ~r1_tarski(k6_relat_1(A_866), k6_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_10339, c_5436])).
% 7.73/2.83  tff(c_10400, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_12, c_10395])).
% 7.73/2.83  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.73/2.83  tff(c_5433, plain, (![B_471, A_472]: (k2_relat_1(B_471)=A_472 | ~r1_tarski(A_472, k2_relat_1(B_471)) | ~v5_relat_1(B_471, A_472) | ~v1_relat_1(B_471))), inference(resolution, [status(thm)], [c_5423, c_8])).
% 7.73/2.83  tff(c_10407, plain, (k2_relat_1('#skF_4')='#skF_3' | ~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10400, c_5433])).
% 7.73/2.83  tff(c_10414, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5375, c_5422, c_10407])).
% 7.73/2.83  tff(c_10416, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5679, c_10414])).
% 7.73/2.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.73/2.83  
% 7.73/2.83  Inference rules
% 7.73/2.83  ----------------------
% 7.73/2.83  #Ref     : 0
% 7.73/2.83  #Sup     : 1865
% 7.73/2.83  #Fact    : 0
% 7.73/2.83  #Define  : 0
% 7.73/2.83  #Split   : 20
% 7.73/2.83  #Chain   : 0
% 7.73/2.83  #Close   : 0
% 7.73/2.83  
% 7.73/2.83  Ordering : KBO
% 7.73/2.83  
% 7.73/2.83  Simplification rules
% 7.73/2.83  ----------------------
% 7.73/2.83  #Subsume      : 401
% 7.73/2.83  #Demod        : 1701
% 7.73/2.83  #Tautology    : 352
% 7.73/2.83  #SimpNegUnit  : 3
% 7.73/2.83  #BackRed      : 13
% 7.73/2.83  
% 7.73/2.83  #Partial instantiations: 0
% 7.73/2.83  #Strategies tried      : 1
% 7.73/2.83  
% 7.73/2.83  Timing (in seconds)
% 7.73/2.83  ----------------------
% 7.73/2.83  Preprocessing        : 0.31
% 7.73/2.83  Parsing              : 0.17
% 7.73/2.83  CNF conversion       : 0.02
% 7.73/2.83  Main loop            : 1.76
% 7.73/2.83  Inferencing          : 0.57
% 7.73/2.83  Reduction            : 0.65
% 7.73/2.83  Demodulation         : 0.47
% 7.73/2.83  BG Simplification    : 0.05
% 7.73/2.83  Subsumption          : 0.37
% 7.73/2.83  Abstraction          : 0.08
% 7.73/2.83  MUC search           : 0.00
% 7.73/2.83  Cooper               : 0.00
% 7.73/2.83  Total                : 2.10
% 7.73/2.83  Index Insertion      : 0.00
% 7.73/2.83  Index Deletion       : 0.00
% 7.73/2.83  Index Matching       : 0.00
% 7.73/2.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
