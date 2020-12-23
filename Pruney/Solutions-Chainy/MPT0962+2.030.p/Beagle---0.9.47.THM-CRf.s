%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:55 EST 2020

% Result     : Theorem 5.13s
% Output     : CNFRefutation 5.30s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 912 expanded)
%              Number of leaves         :   31 ( 298 expanded)
%              Depth                    :   13
%              Number of atoms          :  346 (2321 expanded)
%              Number of equality atoms :  102 ( 602 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ~ ( ~ ( A = k1_xboole_0
            & B != k1_xboole_0 )
        & ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ~ ( B = k1_relat_1(C)
                & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

tff(c_68,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_64,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_4415,plain,(
    ! [C_495,A_496,B_497] :
      ( m1_subset_1(C_495,k1_zfmisc_1(k2_zfmisc_1(A_496,B_497)))
      | ~ r1_tarski(k2_relat_1(C_495),B_497)
      | ~ r1_tarski(k1_relat_1(C_495),A_496)
      | ~ v1_relat_1(C_495) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_62,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_70,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62])).

tff(c_83,plain,(
    ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_357,plain,(
    ! [C_82,A_83,B_84] :
      ( m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84)))
      | ~ r1_tarski(k2_relat_1(C_82),B_84)
      | ~ r1_tarski(k1_relat_1(C_82),A_83)
      | ~ v1_relat_1(C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_46,plain,(
    ! [A_21,B_22,C_23] :
      ( k1_relset_1(A_21,B_22,C_23) = k1_relat_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1637,plain,(
    ! [A_204,B_205,C_206] :
      ( k1_relset_1(A_204,B_205,C_206) = k1_relat_1(C_206)
      | ~ r1_tarski(k2_relat_1(C_206),B_205)
      | ~ r1_tarski(k1_relat_1(C_206),A_204)
      | ~ v1_relat_1(C_206) ) ),
    inference(resolution,[status(thm)],[c_357,c_46])).

tff(c_1651,plain,(
    ! [A_204] :
      ( k1_relset_1(A_204,'#skF_3','#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_204)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_64,c_1637])).

tff(c_1665,plain,(
    ! [A_207] :
      ( k1_relset_1(A_207,'#skF_3','#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_207) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1651])).

tff(c_1680,plain,(
    k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_1665])).

tff(c_48,plain,(
    ! [C_26,A_24,B_25] :
      ( m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25)))
      | ~ r1_tarski(k2_relat_1(C_26),B_25)
      | ~ r1_tarski(k1_relat_1(C_26),A_24)
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_514,plain,(
    ! [B_109,C_110,A_111] :
      ( k1_xboole_0 = B_109
      | v1_funct_2(C_110,A_111,B_109)
      | k1_relset_1(A_111,B_109,C_110) != A_111
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_111,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2103,plain,(
    ! [B_248,C_249,A_250] :
      ( k1_xboole_0 = B_248
      | v1_funct_2(C_249,A_250,B_248)
      | k1_relset_1(A_250,B_248,C_249) != A_250
      | ~ r1_tarski(k2_relat_1(C_249),B_248)
      | ~ r1_tarski(k1_relat_1(C_249),A_250)
      | ~ v1_relat_1(C_249) ) ),
    inference(resolution,[status(thm)],[c_48,c_514])).

tff(c_2123,plain,(
    ! [A_250] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2('#skF_4',A_250,'#skF_3')
      | k1_relset_1(A_250,'#skF_3','#skF_4') != A_250
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_250)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_64,c_2103])).

tff(c_2137,plain,(
    ! [A_250] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2('#skF_4',A_250,'#skF_3')
      | k1_relset_1(A_250,'#skF_3','#skF_4') != A_250
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_250) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2123])).

tff(c_2139,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2137])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_292,plain,(
    ! [C_62,B_63,A_64] :
      ( r2_hidden(C_62,B_63)
      | ~ r2_hidden(C_62,A_64)
      | ~ r1_tarski(A_64,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_312,plain,(
    ! [A_70,B_71,B_72] :
      ( r2_hidden('#skF_1'(A_70,B_71),B_72)
      | ~ r1_tarski(A_70,B_72)
      | r1_tarski(A_70,B_71) ) ),
    inference(resolution,[status(thm)],[c_6,c_292])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_485,plain,(
    ! [A_102,B_103,B_104,B_105] :
      ( r2_hidden('#skF_1'(A_102,B_103),B_104)
      | ~ r1_tarski(B_105,B_104)
      | ~ r1_tarski(A_102,B_105)
      | r1_tarski(A_102,B_103) ) ),
    inference(resolution,[status(thm)],[c_312,c_2])).

tff(c_568,plain,(
    ! [A_116,B_117] :
      ( r2_hidden('#skF_1'(A_116,B_117),'#skF_3')
      | ~ r1_tarski(A_116,k2_relat_1('#skF_4'))
      | r1_tarski(A_116,B_117) ) ),
    inference(resolution,[status(thm)],[c_64,c_485])).

tff(c_882,plain,(
    ! [A_141,B_142,B_143] :
      ( r2_hidden('#skF_1'(A_141,B_142),B_143)
      | ~ r1_tarski('#skF_3',B_143)
      | ~ r1_tarski(A_141,k2_relat_1('#skF_4'))
      | r1_tarski(A_141,B_142) ) ),
    inference(resolution,[status(thm)],[c_568,c_2])).

tff(c_22,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_299,plain,(
    ! [A_65,C_66,B_67] :
      ( m1_subset_1(A_65,C_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(C_66))
      | ~ r2_hidden(A_65,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_302,plain,(
    ! [A_65,A_11] :
      ( m1_subset_1(A_65,A_11)
      | ~ r2_hidden(A_65,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_299])).

tff(c_892,plain,(
    ! [A_141,B_142,A_11] :
      ( m1_subset_1('#skF_1'(A_141,B_142),A_11)
      | ~ r1_tarski('#skF_3',k1_xboole_0)
      | ~ r1_tarski(A_141,k2_relat_1('#skF_4'))
      | r1_tarski(A_141,B_142) ) ),
    inference(resolution,[status(thm)],[c_882,c_302])).

tff(c_1596,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_892])).

tff(c_2145,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2139,c_1596])).

tff(c_2184,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2145])).

tff(c_2187,plain,(
    ! [A_251] :
      ( v1_funct_2('#skF_4',A_251,'#skF_3')
      | k1_relset_1(A_251,'#skF_3','#skF_4') != A_251
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_251) ) ),
    inference(splitRight,[status(thm)],[c_2137])).

tff(c_2207,plain,
    ( v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3')
    | k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') != k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_2187])).

tff(c_2214,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1680,c_2207])).

tff(c_2216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_2214])).

tff(c_2218,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_892])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_501,plain,(
    ! [A_106,B_107,A_108] :
      ( r2_hidden('#skF_1'(A_106,B_107),A_108)
      | ~ r1_tarski(A_106,k1_xboole_0)
      | r1_tarski(A_106,B_107) ) ),
    inference(resolution,[status(thm)],[c_14,c_485])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_513,plain,(
    ! [A_106,A_108] :
      ( ~ r1_tarski(A_106,k1_xboole_0)
      | r1_tarski(A_106,A_108) ) ),
    inference(resolution,[status(thm)],[c_501,c_4])).

tff(c_2231,plain,(
    ! [A_108] : r1_tarski('#skF_3',A_108) ),
    inference(resolution,[status(thm)],[c_2218,c_513])).

tff(c_155,plain,(
    ! [B_54,A_55] :
      ( B_54 = A_55
      | ~ r1_tarski(B_54,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_168,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_64,c_155])).

tff(c_218,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_168])).

tff(c_2296,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2231,c_218])).

tff(c_2297,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_2522,plain,(
    ! [C_289,A_290,B_291] :
      ( m1_subset_1(C_289,k1_zfmisc_1(k2_zfmisc_1(A_290,B_291)))
      | ~ r1_tarski(k2_relat_1(C_289),B_291)
      | ~ r1_tarski(k1_relat_1(C_289),A_290)
      | ~ v1_relat_1(C_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2817,plain,(
    ! [A_328,B_329,C_330] :
      ( k1_relset_1(A_328,B_329,C_330) = k1_relat_1(C_330)
      | ~ r1_tarski(k2_relat_1(C_330),B_329)
      | ~ r1_tarski(k1_relat_1(C_330),A_328)
      | ~ v1_relat_1(C_330) ) ),
    inference(resolution,[status(thm)],[c_2522,c_46])).

tff(c_2841,plain,(
    ! [A_331,C_332] :
      ( k1_relset_1(A_331,k2_relat_1(C_332),C_332) = k1_relat_1(C_332)
      | ~ r1_tarski(k1_relat_1(C_332),A_331)
      | ~ v1_relat_1(C_332) ) ),
    inference(resolution,[status(thm)],[c_12,c_2817])).

tff(c_2872,plain,(
    ! [C_337] :
      ( k1_relset_1(k1_relat_1(C_337),k2_relat_1(C_337),C_337) = k1_relat_1(C_337)
      | ~ v1_relat_1(C_337) ) ),
    inference(resolution,[status(thm)],[c_12,c_2841])).

tff(c_2895,plain,
    ( k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2297,c_2872])).

tff(c_2910,plain,(
    k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2895])).

tff(c_2673,plain,(
    ! [B_313,C_314,A_315] :
      ( k1_xboole_0 = B_313
      | v1_funct_2(C_314,A_315,B_313)
      | k1_relset_1(A_315,B_313,C_314) != A_315
      | ~ m1_subset_1(C_314,k1_zfmisc_1(k2_zfmisc_1(A_315,B_313))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_3035,plain,(
    ! [B_352,C_353,A_354] :
      ( k1_xboole_0 = B_352
      | v1_funct_2(C_353,A_354,B_352)
      | k1_relset_1(A_354,B_352,C_353) != A_354
      | ~ r1_tarski(k2_relat_1(C_353),B_352)
      | ~ r1_tarski(k1_relat_1(C_353),A_354)
      | ~ v1_relat_1(C_353) ) ),
    inference(resolution,[status(thm)],[c_48,c_2673])).

tff(c_3045,plain,(
    ! [B_352,A_354] :
      ( k1_xboole_0 = B_352
      | v1_funct_2('#skF_4',A_354,B_352)
      | k1_relset_1(A_354,B_352,'#skF_4') != A_354
      | ~ r1_tarski('#skF_3',B_352)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_354)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2297,c_3035])).

tff(c_3180,plain,(
    ! [B_361,A_362] :
      ( k1_xboole_0 = B_361
      | v1_funct_2('#skF_4',A_362,B_361)
      | k1_relset_1(A_362,B_361,'#skF_4') != A_362
      | ~ r1_tarski('#skF_3',B_361)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_362) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3045])).

tff(c_3197,plain,(
    ! [B_363] :
      ( k1_xboole_0 = B_363
      | v1_funct_2('#skF_4',k1_relat_1('#skF_4'),B_363)
      | k1_relset_1(k1_relat_1('#skF_4'),B_363,'#skF_4') != k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_3',B_363) ) ),
    inference(resolution,[status(thm)],[c_12,c_3180])).

tff(c_3205,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') != k1_relat_1('#skF_4')
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_3197,c_83])).

tff(c_3212,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2910,c_3205])).

tff(c_18,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2604,plain,(
    ! [C_300,A_301] :
      ( m1_subset_1(C_300,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_300),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_300),A_301)
      | ~ v1_relat_1(C_300) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2522])).

tff(c_2608,plain,(
    ! [A_301] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_3',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_301)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2297,c_2604])).

tff(c_2615,plain,(
    ! [A_301] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_3',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_301) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2608])).

tff(c_2618,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2615])).

tff(c_3224,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3212,c_2618])).

tff(c_3257,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3224])).

tff(c_3259,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_2615])).

tff(c_173,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_155])).

tff(c_3265,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3259,c_173])).

tff(c_3300,plain,(
    ! [A_8] : r1_tarski('#skF_3',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3265,c_14])).

tff(c_3298,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3265,c_3265,c_18])).

tff(c_2310,plain,(
    ! [A_257] :
      ( r1_tarski(A_257,k2_zfmisc_1(k1_relat_1(A_257),k2_relat_1(A_257)))
      | ~ v1_relat_1(A_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2315,plain,
    ( r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2297,c_2310])).

tff(c_2327,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2315])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2396,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_2327,c_8])).

tff(c_2439,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2396])).

tff(c_3394,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3298,c_2439])).

tff(c_3398,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3300,c_3394])).

tff(c_3399,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2396])).

tff(c_3563,plain,(
    ! [C_399,A_400,B_401] :
      ( m1_subset_1(C_399,k1_zfmisc_1(k2_zfmisc_1(A_400,B_401)))
      | ~ r1_tarski(k2_relat_1(C_399),B_401)
      | ~ r1_tarski(k1_relat_1(C_399),A_400)
      | ~ v1_relat_1(C_399) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3698,plain,(
    ! [C_415] :
      ( m1_subset_1(C_415,k1_zfmisc_1('#skF_4'))
      | ~ r1_tarski(k2_relat_1(C_415),'#skF_3')
      | ~ r1_tarski(k1_relat_1(C_415),k1_relat_1('#skF_4'))
      | ~ v1_relat_1(C_415) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3399,c_3563])).

tff(c_3708,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4'))
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_3698])).

tff(c_3713,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_12,c_2297,c_3708])).

tff(c_3406,plain,(
    ! [C_23] :
      ( k1_relset_1(k1_relat_1('#skF_4'),'#skF_3',C_23) = k1_relat_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3399,c_46])).

tff(c_3759,plain,(
    k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3713,c_3406])).

tff(c_3648,plain,(
    ! [B_408,A_409,C_410] :
      ( k1_xboole_0 = B_408
      | k1_relset_1(A_409,B_408,C_410) = A_409
      | ~ v1_funct_2(C_410,A_409,B_408)
      | ~ m1_subset_1(C_410,k1_zfmisc_1(k2_zfmisc_1(A_409,B_408))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_3654,plain,(
    ! [C_410] :
      ( k1_xboole_0 = '#skF_3'
      | k1_relset_1(k1_relat_1('#skF_4'),'#skF_3',C_410) = k1_relat_1('#skF_4')
      | ~ v1_funct_2(C_410,k1_relat_1('#skF_4'),'#skF_3')
      | ~ m1_subset_1(C_410,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3399,c_3648])).

tff(c_3714,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3654])).

tff(c_3614,plain,(
    ! [C_405,A_406] :
      ( m1_subset_1(C_405,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_405),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_405),A_406)
      | ~ v1_relat_1(C_405) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_3563])).

tff(c_3618,plain,(
    ! [A_406] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_3',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_406)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2297,c_3614])).

tff(c_3625,plain,(
    ! [A_406] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_3',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_406) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3618])).

tff(c_3628,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_3625])).

tff(c_3718,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3714,c_3628])).

tff(c_3751,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3718])).

tff(c_3753,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3654])).

tff(c_3776,plain,(
    ! [B_417,C_418,A_419] :
      ( k1_xboole_0 = B_417
      | v1_funct_2(C_418,A_419,B_417)
      | k1_relset_1(A_419,B_417,C_418) != A_419
      | ~ m1_subset_1(C_418,k1_zfmisc_1(k2_zfmisc_1(A_419,B_417))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_3782,plain,(
    ! [C_418] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2(C_418,k1_relat_1('#skF_4'),'#skF_3')
      | k1_relset_1(k1_relat_1('#skF_4'),'#skF_3',C_418) != k1_relat_1('#skF_4')
      | ~ m1_subset_1(C_418,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3399,c_3776])).

tff(c_3819,plain,(
    ! [C_425] :
      ( v1_funct_2(C_425,k1_relat_1('#skF_4'),'#skF_3')
      | k1_relset_1(k1_relat_1('#skF_4'),'#skF_3',C_425) != k1_relat_1('#skF_4')
      | ~ m1_subset_1(C_425,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3753,c_3782])).

tff(c_3826,plain,
    ( k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') != k1_relat_1('#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_3819,c_83])).

tff(c_3834,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3713,c_3759,c_3826])).

tff(c_3836,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_3625])).

tff(c_3848,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3836,c_173])).

tff(c_16,plain,(
    ! [B_10,A_9] :
      ( k1_xboole_0 = B_10
      | k1_xboole_0 = A_9
      | k2_zfmisc_1(A_9,B_10) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3409,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = k1_xboole_0
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3399,c_16])).

tff(c_3417,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3409])).

tff(c_3862,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3848,c_3417])).

tff(c_3935,plain,(
    ! [A_432] : k2_zfmisc_1(A_432,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3848,c_3848,c_18])).

tff(c_3945,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3935,c_3399])).

tff(c_3958,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3862,c_3945])).

tff(c_3960,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3409])).

tff(c_42,plain,(
    ! [A_18] : v1_relat_1('#skF_2'(A_18,k1_xboole_0)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_20,plain,(
    ! [B_10] : k2_zfmisc_1(k1_xboole_0,B_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_34,plain,(
    ! [A_18] : k1_relat_1('#skF_2'(A_18,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2324,plain,(
    ! [A_18] :
      ( r1_tarski('#skF_2'(A_18,k1_xboole_0),k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_2'(A_18,k1_xboole_0))))
      | ~ v1_relat_1('#skF_2'(A_18,k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2310])).

tff(c_2332,plain,(
    ! [A_258] : r1_tarski('#skF_2'(A_258,k1_xboole_0),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_20,c_2324])).

tff(c_2338,plain,(
    ! [A_258] : '#skF_2'(A_258,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2332,c_173])).

tff(c_2345,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2338,c_34])).

tff(c_2407,plain,(
    ! [A_265,B_266,C_267] :
      ( k1_relset_1(A_265,B_266,C_267) = k1_relat_1(C_267)
      | ~ m1_subset_1(C_267,k1_zfmisc_1(k2_zfmisc_1(A_265,B_266))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2417,plain,(
    ! [A_265,B_266] : k1_relset_1(A_265,B_266,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_2407])).

tff(c_2419,plain,(
    ! [A_265,B_266] : k1_relset_1(A_265,B_266,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2345,c_2417])).

tff(c_3971,plain,(
    ! [A_265,B_266] : k1_relset_1(A_265,B_266,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3960,c_3960,c_2419])).

tff(c_3987,plain,(
    ! [A_11] : m1_subset_1('#skF_4',k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3960,c_22])).

tff(c_54,plain,(
    ! [C_29,B_28] :
      ( v1_funct_2(C_29,k1_xboole_0,B_28)
      | k1_relset_1(k1_xboole_0,B_28,C_29) != k1_xboole_0
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_73,plain,(
    ! [C_29,B_28] :
      ( v1_funct_2(C_29,k1_xboole_0,B_28)
      | k1_relset_1(k1_xboole_0,B_28,C_29) != k1_xboole_0
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_54])).

tff(c_4122,plain,(
    ! [C_446,B_447] :
      ( v1_funct_2(C_446,'#skF_4',B_447)
      | k1_relset_1('#skF_4',B_447,C_446) != '#skF_4'
      | ~ m1_subset_1(C_446,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3960,c_3960,c_3960,c_3960,c_73])).

tff(c_4125,plain,(
    ! [B_447] :
      ( v1_funct_2('#skF_4','#skF_4',B_447)
      | k1_relset_1('#skF_4',B_447,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_3987,c_4122])).

tff(c_4128,plain,(
    ! [B_447] : v1_funct_2('#skF_4','#skF_4',B_447) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3971,c_4125])).

tff(c_30,plain,(
    ! [A_18] : r1_tarski(k2_relat_1('#skF_2'(A_18,k1_xboole_0)),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_174,plain,(
    ! [A_56] :
      ( k1_xboole_0 = A_56
      | ~ r1_tarski(A_56,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_155])).

tff(c_193,plain,(
    k2_relat_1('#skF_2'(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_174])).

tff(c_2343,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2338,c_193])).

tff(c_3974,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3960,c_3960,c_2343])).

tff(c_4006,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3974,c_2297])).

tff(c_3973,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3960,c_3960,c_2345])).

tff(c_3996,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3973,c_83])).

tff(c_4089,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4006,c_3996])).

tff(c_4131,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4128,c_4089])).

tff(c_4132,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_4423,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4415,c_4132])).

tff(c_4435,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_12,c_64,c_4423])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:16:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.13/2.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.30/2.13  
% 5.30/2.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.30/2.13  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 5.30/2.13  
% 5.30/2.13  %Foreground sorts:
% 5.30/2.13  
% 5.30/2.13  
% 5.30/2.13  %Background operators:
% 5.30/2.13  
% 5.30/2.13  
% 5.30/2.13  %Foreground operators:
% 5.30/2.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.30/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.30/2.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.30/2.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.30/2.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.30/2.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.30/2.13  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.30/2.13  tff('#skF_3', type, '#skF_3': $i).
% 5.30/2.13  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.30/2.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.30/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.30/2.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.30/2.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.30/2.13  tff('#skF_4', type, '#skF_4': $i).
% 5.30/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.30/2.13  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.30/2.13  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.30/2.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.30/2.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.30/2.13  
% 5.30/2.15  tff(f_120, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 5.30/2.15  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.30/2.15  tff(f_89, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 5.30/2.15  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.30/2.15  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.30/2.15  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.30/2.15  tff(f_48, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 5.30/2.15  tff(f_54, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 5.30/2.15  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.30/2.15  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.30/2.15  tff(f_60, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 5.30/2.15  tff(f_77, axiom, (![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_1)).
% 5.30/2.15  tff(c_68, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.30/2.15  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.30/2.15  tff(c_64, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.30/2.15  tff(c_4415, plain, (![C_495, A_496, B_497]: (m1_subset_1(C_495, k1_zfmisc_1(k2_zfmisc_1(A_496, B_497))) | ~r1_tarski(k2_relat_1(C_495), B_497) | ~r1_tarski(k1_relat_1(C_495), A_496) | ~v1_relat_1(C_495))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.30/2.15  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.30/2.15  tff(c_62, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.30/2.15  tff(c_70, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62])).
% 5.30/2.15  tff(c_83, plain, (~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_70])).
% 5.30/2.15  tff(c_357, plain, (![C_82, A_83, B_84]: (m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))) | ~r1_tarski(k2_relat_1(C_82), B_84) | ~r1_tarski(k1_relat_1(C_82), A_83) | ~v1_relat_1(C_82))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.30/2.15  tff(c_46, plain, (![A_21, B_22, C_23]: (k1_relset_1(A_21, B_22, C_23)=k1_relat_1(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.30/2.15  tff(c_1637, plain, (![A_204, B_205, C_206]: (k1_relset_1(A_204, B_205, C_206)=k1_relat_1(C_206) | ~r1_tarski(k2_relat_1(C_206), B_205) | ~r1_tarski(k1_relat_1(C_206), A_204) | ~v1_relat_1(C_206))), inference(resolution, [status(thm)], [c_357, c_46])).
% 5.30/2.15  tff(c_1651, plain, (![A_204]: (k1_relset_1(A_204, '#skF_3', '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), A_204) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_64, c_1637])).
% 5.30/2.15  tff(c_1665, plain, (![A_207]: (k1_relset_1(A_207, '#skF_3', '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), A_207))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1651])).
% 5.30/2.15  tff(c_1680, plain, (k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_1665])).
% 5.30/2.15  tff(c_48, plain, (![C_26, A_24, B_25]: (m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))) | ~r1_tarski(k2_relat_1(C_26), B_25) | ~r1_tarski(k1_relat_1(C_26), A_24) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.30/2.15  tff(c_514, plain, (![B_109, C_110, A_111]: (k1_xboole_0=B_109 | v1_funct_2(C_110, A_111, B_109) | k1_relset_1(A_111, B_109, C_110)!=A_111 | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_111, B_109))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.30/2.15  tff(c_2103, plain, (![B_248, C_249, A_250]: (k1_xboole_0=B_248 | v1_funct_2(C_249, A_250, B_248) | k1_relset_1(A_250, B_248, C_249)!=A_250 | ~r1_tarski(k2_relat_1(C_249), B_248) | ~r1_tarski(k1_relat_1(C_249), A_250) | ~v1_relat_1(C_249))), inference(resolution, [status(thm)], [c_48, c_514])).
% 5.30/2.15  tff(c_2123, plain, (![A_250]: (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', A_250, '#skF_3') | k1_relset_1(A_250, '#skF_3', '#skF_4')!=A_250 | ~r1_tarski(k1_relat_1('#skF_4'), A_250) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_64, c_2103])).
% 5.30/2.15  tff(c_2137, plain, (![A_250]: (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', A_250, '#skF_3') | k1_relset_1(A_250, '#skF_3', '#skF_4')!=A_250 | ~r1_tarski(k1_relat_1('#skF_4'), A_250))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2123])).
% 5.30/2.15  tff(c_2139, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2137])).
% 5.30/2.15  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.30/2.15  tff(c_292, plain, (![C_62, B_63, A_64]: (r2_hidden(C_62, B_63) | ~r2_hidden(C_62, A_64) | ~r1_tarski(A_64, B_63))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.30/2.15  tff(c_312, plain, (![A_70, B_71, B_72]: (r2_hidden('#skF_1'(A_70, B_71), B_72) | ~r1_tarski(A_70, B_72) | r1_tarski(A_70, B_71))), inference(resolution, [status(thm)], [c_6, c_292])).
% 5.30/2.15  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.30/2.15  tff(c_485, plain, (![A_102, B_103, B_104, B_105]: (r2_hidden('#skF_1'(A_102, B_103), B_104) | ~r1_tarski(B_105, B_104) | ~r1_tarski(A_102, B_105) | r1_tarski(A_102, B_103))), inference(resolution, [status(thm)], [c_312, c_2])).
% 5.30/2.15  tff(c_568, plain, (![A_116, B_117]: (r2_hidden('#skF_1'(A_116, B_117), '#skF_3') | ~r1_tarski(A_116, k2_relat_1('#skF_4')) | r1_tarski(A_116, B_117))), inference(resolution, [status(thm)], [c_64, c_485])).
% 5.30/2.15  tff(c_882, plain, (![A_141, B_142, B_143]: (r2_hidden('#skF_1'(A_141, B_142), B_143) | ~r1_tarski('#skF_3', B_143) | ~r1_tarski(A_141, k2_relat_1('#skF_4')) | r1_tarski(A_141, B_142))), inference(resolution, [status(thm)], [c_568, c_2])).
% 5.30/2.15  tff(c_22, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.30/2.15  tff(c_299, plain, (![A_65, C_66, B_67]: (m1_subset_1(A_65, C_66) | ~m1_subset_1(B_67, k1_zfmisc_1(C_66)) | ~r2_hidden(A_65, B_67))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.30/2.15  tff(c_302, plain, (![A_65, A_11]: (m1_subset_1(A_65, A_11) | ~r2_hidden(A_65, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_299])).
% 5.30/2.15  tff(c_892, plain, (![A_141, B_142, A_11]: (m1_subset_1('#skF_1'(A_141, B_142), A_11) | ~r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski(A_141, k2_relat_1('#skF_4')) | r1_tarski(A_141, B_142))), inference(resolution, [status(thm)], [c_882, c_302])).
% 5.30/2.15  tff(c_1596, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_892])).
% 5.30/2.15  tff(c_2145, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2139, c_1596])).
% 5.30/2.15  tff(c_2184, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_2145])).
% 5.30/2.15  tff(c_2187, plain, (![A_251]: (v1_funct_2('#skF_4', A_251, '#skF_3') | k1_relset_1(A_251, '#skF_3', '#skF_4')!=A_251 | ~r1_tarski(k1_relat_1('#skF_4'), A_251))), inference(splitRight, [status(thm)], [c_2137])).
% 5.30/2.15  tff(c_2207, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3') | k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')!=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_2187])).
% 5.30/2.15  tff(c_2214, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1680, c_2207])).
% 5.30/2.15  tff(c_2216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_2214])).
% 5.30/2.15  tff(c_2218, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_892])).
% 5.30/2.15  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.30/2.15  tff(c_501, plain, (![A_106, B_107, A_108]: (r2_hidden('#skF_1'(A_106, B_107), A_108) | ~r1_tarski(A_106, k1_xboole_0) | r1_tarski(A_106, B_107))), inference(resolution, [status(thm)], [c_14, c_485])).
% 5.30/2.15  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.30/2.15  tff(c_513, plain, (![A_106, A_108]: (~r1_tarski(A_106, k1_xboole_0) | r1_tarski(A_106, A_108))), inference(resolution, [status(thm)], [c_501, c_4])).
% 5.30/2.15  tff(c_2231, plain, (![A_108]: (r1_tarski('#skF_3', A_108))), inference(resolution, [status(thm)], [c_2218, c_513])).
% 5.30/2.15  tff(c_155, plain, (![B_54, A_55]: (B_54=A_55 | ~r1_tarski(B_54, A_55) | ~r1_tarski(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.30/2.15  tff(c_168, plain, (k2_relat_1('#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_64, c_155])).
% 5.30/2.15  tff(c_218, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_168])).
% 5.30/2.15  tff(c_2296, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2231, c_218])).
% 5.30/2.15  tff(c_2297, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_168])).
% 5.30/2.15  tff(c_2522, plain, (![C_289, A_290, B_291]: (m1_subset_1(C_289, k1_zfmisc_1(k2_zfmisc_1(A_290, B_291))) | ~r1_tarski(k2_relat_1(C_289), B_291) | ~r1_tarski(k1_relat_1(C_289), A_290) | ~v1_relat_1(C_289))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.30/2.15  tff(c_2817, plain, (![A_328, B_329, C_330]: (k1_relset_1(A_328, B_329, C_330)=k1_relat_1(C_330) | ~r1_tarski(k2_relat_1(C_330), B_329) | ~r1_tarski(k1_relat_1(C_330), A_328) | ~v1_relat_1(C_330))), inference(resolution, [status(thm)], [c_2522, c_46])).
% 5.30/2.15  tff(c_2841, plain, (![A_331, C_332]: (k1_relset_1(A_331, k2_relat_1(C_332), C_332)=k1_relat_1(C_332) | ~r1_tarski(k1_relat_1(C_332), A_331) | ~v1_relat_1(C_332))), inference(resolution, [status(thm)], [c_12, c_2817])).
% 5.30/2.15  tff(c_2872, plain, (![C_337]: (k1_relset_1(k1_relat_1(C_337), k2_relat_1(C_337), C_337)=k1_relat_1(C_337) | ~v1_relat_1(C_337))), inference(resolution, [status(thm)], [c_12, c_2841])).
% 5.30/2.15  tff(c_2895, plain, (k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2297, c_2872])).
% 5.30/2.15  tff(c_2910, plain, (k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2895])).
% 5.30/2.15  tff(c_2673, plain, (![B_313, C_314, A_315]: (k1_xboole_0=B_313 | v1_funct_2(C_314, A_315, B_313) | k1_relset_1(A_315, B_313, C_314)!=A_315 | ~m1_subset_1(C_314, k1_zfmisc_1(k2_zfmisc_1(A_315, B_313))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.30/2.15  tff(c_3035, plain, (![B_352, C_353, A_354]: (k1_xboole_0=B_352 | v1_funct_2(C_353, A_354, B_352) | k1_relset_1(A_354, B_352, C_353)!=A_354 | ~r1_tarski(k2_relat_1(C_353), B_352) | ~r1_tarski(k1_relat_1(C_353), A_354) | ~v1_relat_1(C_353))), inference(resolution, [status(thm)], [c_48, c_2673])).
% 5.30/2.15  tff(c_3045, plain, (![B_352, A_354]: (k1_xboole_0=B_352 | v1_funct_2('#skF_4', A_354, B_352) | k1_relset_1(A_354, B_352, '#skF_4')!=A_354 | ~r1_tarski('#skF_3', B_352) | ~r1_tarski(k1_relat_1('#skF_4'), A_354) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2297, c_3035])).
% 5.30/2.15  tff(c_3180, plain, (![B_361, A_362]: (k1_xboole_0=B_361 | v1_funct_2('#skF_4', A_362, B_361) | k1_relset_1(A_362, B_361, '#skF_4')!=A_362 | ~r1_tarski('#skF_3', B_361) | ~r1_tarski(k1_relat_1('#skF_4'), A_362))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_3045])).
% 5.30/2.15  tff(c_3197, plain, (![B_363]: (k1_xboole_0=B_363 | v1_funct_2('#skF_4', k1_relat_1('#skF_4'), B_363) | k1_relset_1(k1_relat_1('#skF_4'), B_363, '#skF_4')!=k1_relat_1('#skF_4') | ~r1_tarski('#skF_3', B_363))), inference(resolution, [status(thm)], [c_12, c_3180])).
% 5.30/2.15  tff(c_3205, plain, (k1_xboole_0='#skF_3' | k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')!=k1_relat_1('#skF_4') | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_3197, c_83])).
% 5.30/2.15  tff(c_3212, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2910, c_3205])).
% 5.30/2.15  tff(c_18, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.30/2.15  tff(c_2604, plain, (![C_300, A_301]: (m1_subset_1(C_300, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_300), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_300), A_301) | ~v1_relat_1(C_300))), inference(superposition, [status(thm), theory('equality')], [c_18, c_2522])).
% 5.30/2.15  tff(c_2608, plain, (![A_301]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_4'), A_301) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2297, c_2604])).
% 5.30/2.15  tff(c_2615, plain, (![A_301]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_4'), A_301))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2608])).
% 5.30/2.15  tff(c_2618, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2615])).
% 5.30/2.15  tff(c_3224, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3212, c_2618])).
% 5.30/2.15  tff(c_3257, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_3224])).
% 5.30/2.15  tff(c_3259, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_2615])).
% 5.30/2.15  tff(c_173, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_155])).
% 5.30/2.15  tff(c_3265, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3259, c_173])).
% 5.30/2.15  tff(c_3300, plain, (![A_8]: (r1_tarski('#skF_3', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_3265, c_14])).
% 5.30/2.15  tff(c_3298, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3265, c_3265, c_18])).
% 5.30/2.15  tff(c_2310, plain, (![A_257]: (r1_tarski(A_257, k2_zfmisc_1(k1_relat_1(A_257), k2_relat_1(A_257))) | ~v1_relat_1(A_257))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.30/2.15  tff(c_2315, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2297, c_2310])).
% 5.30/2.15  tff(c_2327, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2315])).
% 5.30/2.15  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.30/2.15  tff(c_2396, plain, (k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')='#skF_4' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_2327, c_8])).
% 5.30/2.15  tff(c_2439, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_2396])).
% 5.30/2.15  tff(c_3394, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3298, c_2439])).
% 5.30/2.15  tff(c_3398, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3300, c_3394])).
% 5.30/2.15  tff(c_3399, plain, (k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_2396])).
% 5.30/2.15  tff(c_3563, plain, (![C_399, A_400, B_401]: (m1_subset_1(C_399, k1_zfmisc_1(k2_zfmisc_1(A_400, B_401))) | ~r1_tarski(k2_relat_1(C_399), B_401) | ~r1_tarski(k1_relat_1(C_399), A_400) | ~v1_relat_1(C_399))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.30/2.15  tff(c_3698, plain, (![C_415]: (m1_subset_1(C_415, k1_zfmisc_1('#skF_4')) | ~r1_tarski(k2_relat_1(C_415), '#skF_3') | ~r1_tarski(k1_relat_1(C_415), k1_relat_1('#skF_4')) | ~v1_relat_1(C_415))), inference(superposition, [status(thm), theory('equality')], [c_3399, c_3563])).
% 5.30/2.15  tff(c_3708, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')) | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_3698])).
% 5.30/2.15  tff(c_3713, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_12, c_2297, c_3708])).
% 5.30/2.15  tff(c_3406, plain, (![C_23]: (k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', C_23)=k1_relat_1(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_3399, c_46])).
% 5.30/2.15  tff(c_3759, plain, (k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_3713, c_3406])).
% 5.30/2.15  tff(c_3648, plain, (![B_408, A_409, C_410]: (k1_xboole_0=B_408 | k1_relset_1(A_409, B_408, C_410)=A_409 | ~v1_funct_2(C_410, A_409, B_408) | ~m1_subset_1(C_410, k1_zfmisc_1(k2_zfmisc_1(A_409, B_408))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.30/2.15  tff(c_3654, plain, (![C_410]: (k1_xboole_0='#skF_3' | k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', C_410)=k1_relat_1('#skF_4') | ~v1_funct_2(C_410, k1_relat_1('#skF_4'), '#skF_3') | ~m1_subset_1(C_410, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_3399, c_3648])).
% 5.30/2.15  tff(c_3714, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_3654])).
% 5.30/2.15  tff(c_3614, plain, (![C_405, A_406]: (m1_subset_1(C_405, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_405), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_405), A_406) | ~v1_relat_1(C_405))), inference(superposition, [status(thm), theory('equality')], [c_18, c_3563])).
% 5.30/2.15  tff(c_3618, plain, (![A_406]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_4'), A_406) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2297, c_3614])).
% 5.30/2.15  tff(c_3625, plain, (![A_406]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_4'), A_406))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_3618])).
% 5.30/2.15  tff(c_3628, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_3625])).
% 5.30/2.15  tff(c_3718, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3714, c_3628])).
% 5.30/2.15  tff(c_3751, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_3718])).
% 5.30/2.15  tff(c_3753, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_3654])).
% 5.30/2.15  tff(c_3776, plain, (![B_417, C_418, A_419]: (k1_xboole_0=B_417 | v1_funct_2(C_418, A_419, B_417) | k1_relset_1(A_419, B_417, C_418)!=A_419 | ~m1_subset_1(C_418, k1_zfmisc_1(k2_zfmisc_1(A_419, B_417))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.30/2.15  tff(c_3782, plain, (![C_418]: (k1_xboole_0='#skF_3' | v1_funct_2(C_418, k1_relat_1('#skF_4'), '#skF_3') | k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', C_418)!=k1_relat_1('#skF_4') | ~m1_subset_1(C_418, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_3399, c_3776])).
% 5.30/2.15  tff(c_3819, plain, (![C_425]: (v1_funct_2(C_425, k1_relat_1('#skF_4'), '#skF_3') | k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', C_425)!=k1_relat_1('#skF_4') | ~m1_subset_1(C_425, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_3753, c_3782])).
% 5.30/2.15  tff(c_3826, plain, (k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')!=k1_relat_1('#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_3819, c_83])).
% 5.30/2.15  tff(c_3834, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3713, c_3759, c_3826])).
% 5.30/2.15  tff(c_3836, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_3625])).
% 5.30/2.15  tff(c_3848, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3836, c_173])).
% 5.30/2.15  tff(c_16, plain, (![B_10, A_9]: (k1_xboole_0=B_10 | k1_xboole_0=A_9 | k2_zfmisc_1(A_9, B_10)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.30/2.15  tff(c_3409, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')=k1_xboole_0 | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3399, c_16])).
% 5.30/2.15  tff(c_3417, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_3409])).
% 5.30/2.15  tff(c_3862, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3848, c_3417])).
% 5.30/2.15  tff(c_3935, plain, (![A_432]: (k2_zfmisc_1(A_432, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3848, c_3848, c_18])).
% 5.30/2.15  tff(c_3945, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3935, c_3399])).
% 5.30/2.15  tff(c_3958, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3862, c_3945])).
% 5.30/2.15  tff(c_3960, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_3409])).
% 5.30/2.15  tff(c_42, plain, (![A_18]: (v1_relat_1('#skF_2'(A_18, k1_xboole_0)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.30/2.15  tff(c_20, plain, (![B_10]: (k2_zfmisc_1(k1_xboole_0, B_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.30/2.15  tff(c_34, plain, (![A_18]: (k1_relat_1('#skF_2'(A_18, k1_xboole_0))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.30/2.15  tff(c_2324, plain, (![A_18]: (r1_tarski('#skF_2'(A_18, k1_xboole_0), k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_2'(A_18, k1_xboole_0)))) | ~v1_relat_1('#skF_2'(A_18, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_2310])).
% 5.30/2.15  tff(c_2332, plain, (![A_258]: (r1_tarski('#skF_2'(A_258, k1_xboole_0), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_20, c_2324])).
% 5.30/2.15  tff(c_2338, plain, (![A_258]: ('#skF_2'(A_258, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2332, c_173])).
% 5.30/2.15  tff(c_2345, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2338, c_34])).
% 5.30/2.15  tff(c_2407, plain, (![A_265, B_266, C_267]: (k1_relset_1(A_265, B_266, C_267)=k1_relat_1(C_267) | ~m1_subset_1(C_267, k1_zfmisc_1(k2_zfmisc_1(A_265, B_266))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.30/2.15  tff(c_2417, plain, (![A_265, B_266]: (k1_relset_1(A_265, B_266, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_2407])).
% 5.30/2.15  tff(c_2419, plain, (![A_265, B_266]: (k1_relset_1(A_265, B_266, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2345, c_2417])).
% 5.30/2.15  tff(c_3971, plain, (![A_265, B_266]: (k1_relset_1(A_265, B_266, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3960, c_3960, c_2419])).
% 5.30/2.15  tff(c_3987, plain, (![A_11]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_3960, c_22])).
% 5.30/2.15  tff(c_54, plain, (![C_29, B_28]: (v1_funct_2(C_29, k1_xboole_0, B_28) | k1_relset_1(k1_xboole_0, B_28, C_29)!=k1_xboole_0 | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_28))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.30/2.15  tff(c_73, plain, (![C_29, B_28]: (v1_funct_2(C_29, k1_xboole_0, B_28) | k1_relset_1(k1_xboole_0, B_28, C_29)!=k1_xboole_0 | ~m1_subset_1(C_29, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_54])).
% 5.30/2.15  tff(c_4122, plain, (![C_446, B_447]: (v1_funct_2(C_446, '#skF_4', B_447) | k1_relset_1('#skF_4', B_447, C_446)!='#skF_4' | ~m1_subset_1(C_446, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_3960, c_3960, c_3960, c_3960, c_73])).
% 5.30/2.15  tff(c_4125, plain, (![B_447]: (v1_funct_2('#skF_4', '#skF_4', B_447) | k1_relset_1('#skF_4', B_447, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_3987, c_4122])).
% 5.30/2.15  tff(c_4128, plain, (![B_447]: (v1_funct_2('#skF_4', '#skF_4', B_447))), inference(demodulation, [status(thm), theory('equality')], [c_3971, c_4125])).
% 5.30/2.15  tff(c_30, plain, (![A_18]: (r1_tarski(k2_relat_1('#skF_2'(A_18, k1_xboole_0)), A_18))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.30/2.15  tff(c_174, plain, (![A_56]: (k1_xboole_0=A_56 | ~r1_tarski(A_56, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_155])).
% 5.30/2.15  tff(c_193, plain, (k2_relat_1('#skF_2'(k1_xboole_0, k1_xboole_0))=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_174])).
% 5.30/2.15  tff(c_2343, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2338, c_193])).
% 5.30/2.15  tff(c_3974, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3960, c_3960, c_2343])).
% 5.30/2.15  tff(c_4006, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3974, c_2297])).
% 5.30/2.15  tff(c_3973, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3960, c_3960, c_2345])).
% 5.30/2.15  tff(c_3996, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3973, c_83])).
% 5.30/2.15  tff(c_4089, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4006, c_3996])).
% 5.30/2.15  tff(c_4131, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4128, c_4089])).
% 5.30/2.15  tff(c_4132, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')))), inference(splitRight, [status(thm)], [c_70])).
% 5.30/2.15  tff(c_4423, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4415, c_4132])).
% 5.30/2.15  tff(c_4435, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_12, c_64, c_4423])).
% 5.30/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.30/2.15  
% 5.30/2.15  Inference rules
% 5.30/2.15  ----------------------
% 5.30/2.15  #Ref     : 0
% 5.30/2.15  #Sup     : 887
% 5.30/2.15  #Fact    : 0
% 5.30/2.15  #Define  : 0
% 5.30/2.15  #Split   : 27
% 5.30/2.15  #Chain   : 0
% 5.30/2.15  #Close   : 0
% 5.30/2.15  
% 5.30/2.15  Ordering : KBO
% 5.30/2.15  
% 5.30/2.15  Simplification rules
% 5.30/2.15  ----------------------
% 5.30/2.15  #Subsume      : 124
% 5.30/2.15  #Demod        : 1479
% 5.30/2.15  #Tautology    : 402
% 5.30/2.15  #SimpNegUnit  : 6
% 5.30/2.15  #BackRed      : 387
% 5.30/2.15  
% 5.30/2.16  #Partial instantiations: 0
% 5.30/2.16  #Strategies tried      : 1
% 5.30/2.16  
% 5.30/2.16  Timing (in seconds)
% 5.30/2.16  ----------------------
% 5.30/2.16  Preprocessing        : 0.32
% 5.30/2.16  Parsing              : 0.16
% 5.30/2.16  CNF conversion       : 0.02
% 5.30/2.16  Main loop            : 0.92
% 5.30/2.16  Inferencing          : 0.29
% 5.30/2.16  Reduction            : 0.31
% 5.30/2.16  Demodulation         : 0.22
% 5.30/2.16  BG Simplification    : 0.04
% 5.30/2.16  Subsumption          : 0.20
% 5.30/2.16  Abstraction          : 0.05
% 5.30/2.16  MUC search           : 0.00
% 5.30/2.16  Cooper               : 0.00
% 5.30/2.16  Total                : 1.29
% 5.30/2.16  Index Insertion      : 0.00
% 5.30/2.16  Index Deletion       : 0.00
% 5.30/2.16  Index Matching       : 0.00
% 5.30/2.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
