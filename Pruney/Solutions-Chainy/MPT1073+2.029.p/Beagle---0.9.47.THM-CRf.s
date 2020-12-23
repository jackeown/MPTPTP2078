%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:01 EST 2020

% Result     : Theorem 7.57s
% Output     : CNFRefutation 7.57s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 180 expanded)
%              Number of leaves         :   42 (  79 expanded)
%              Depth                    :   11
%              Number of atoms          :  149 ( 397 expanded)
%              Number of equality atoms :   33 (  99 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_143,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_127,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_93,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_64,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_325,plain,(
    ! [A_100,B_101,C_102] :
      ( k2_relset_1(A_100,B_101,C_102) = k2_relat_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_352,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_325])).

tff(c_62,plain,(
    r2_hidden('#skF_4',k2_relset_1('#skF_5','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_88,plain,(
    ~ v1_xboole_0(k2_relset_1('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_62,c_2])).

tff(c_357,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_88])).

tff(c_598,plain,(
    ! [A_128,B_129,C_130] :
      ( m1_subset_1(k2_relset_1(A_128,B_129,C_130),k1_zfmisc_1(B_129))
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_628,plain,
    ( m1_subset_1(k2_relat_1('#skF_7'),k1_zfmisc_1('#skF_6'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_598])).

tff(c_639,plain,(
    m1_subset_1(k2_relat_1('#skF_7'),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_628])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_258,plain,(
    ! [C_88,A_89,B_90] :
      ( r2_hidden(C_88,A_89)
      | ~ r2_hidden(C_88,B_90)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_439,plain,(
    ! [A_113,A_114] :
      ( r2_hidden('#skF_1'(A_113),A_114)
      | ~ m1_subset_1(A_113,k1_zfmisc_1(A_114))
      | v1_xboole_0(A_113) ) ),
    inference(resolution,[status(thm)],[c_4,c_258])).

tff(c_466,plain,(
    ! [A_114,A_113] :
      ( ~ v1_xboole_0(A_114)
      | ~ m1_subset_1(A_113,k1_zfmisc_1(A_114))
      | v1_xboole_0(A_113) ) ),
    inference(resolution,[status(thm)],[c_439,c_2])).

tff(c_695,plain,
    ( ~ v1_xboole_0('#skF_6')
    | v1_xboole_0(k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_639,c_466])).

tff(c_706,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_357,c_695])).

tff(c_358,plain,(
    r2_hidden('#skF_4',k2_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_62])).

tff(c_147,plain,(
    ! [C_69,A_70,B_71] :
      ( v1_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_169,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_147])).

tff(c_66,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_396,plain,(
    ! [A_107,B_108,C_109] :
      ( k1_relset_1(A_107,B_108,C_109) = k1_relat_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_423,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_396])).

tff(c_1941,plain,(
    ! [B_219,A_220,C_221] :
      ( k1_xboole_0 = B_219
      | k1_relset_1(A_220,B_219,C_221) = A_220
      | ~ v1_funct_2(C_221,A_220,B_219)
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(A_220,B_219))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1968,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_1941])).

tff(c_1986,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_423,c_1968])).

tff(c_1990,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1986])).

tff(c_30,plain,(
    ! [A_27] :
      ( k9_relat_1(A_27,k1_relat_1(A_27)) = k2_relat_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2004,plain,
    ( k9_relat_1('#skF_7','#skF_5') = k2_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1990,c_30])).

tff(c_2014,plain,(
    k9_relat_1('#skF_7','#skF_5') = k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_2004])).

tff(c_827,plain,(
    ! [A_140,B_141,C_142] :
      ( r2_hidden('#skF_3'(A_140,B_141,C_142),B_141)
      | ~ r2_hidden(A_140,k9_relat_1(C_142,B_141))
      | ~ v1_relat_1(C_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,B_13)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3282,plain,(
    ! [A_275,B_276,C_277] :
      ( m1_subset_1('#skF_3'(A_275,B_276,C_277),B_276)
      | ~ r2_hidden(A_275,k9_relat_1(C_277,B_276))
      | ~ v1_relat_1(C_277) ) ),
    inference(resolution,[status(thm)],[c_827,c_12])).

tff(c_3286,plain,(
    ! [A_275] :
      ( m1_subset_1('#skF_3'(A_275,'#skF_5','#skF_7'),'#skF_5')
      | ~ r2_hidden(A_275,k2_relat_1('#skF_7'))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2014,c_3282])).

tff(c_4261,plain,(
    ! [A_314] :
      ( m1_subset_1('#skF_3'(A_314,'#skF_5','#skF_7'),'#skF_5')
      | ~ r2_hidden(A_314,k2_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_3286])).

tff(c_4308,plain,(
    m1_subset_1('#skF_3'('#skF_4','#skF_5','#skF_7'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_358,c_4261])).

tff(c_60,plain,(
    ! [E_49] :
      ( k1_funct_1('#skF_7',E_49) != '#skF_4'
      | ~ m1_subset_1(E_49,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_4318,plain,(
    k1_funct_1('#skF_7','#skF_3'('#skF_4','#skF_5','#skF_7')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_4308,c_60])).

tff(c_68,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1323,plain,(
    ! [A_180,B_181,C_182] :
      ( r2_hidden(k4_tarski('#skF_3'(A_180,B_181,C_182),A_180),C_182)
      | ~ r2_hidden(A_180,k9_relat_1(C_182,B_181))
      | ~ v1_relat_1(C_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_34,plain,(
    ! [C_30,A_28,B_29] :
      ( k1_funct_1(C_30,A_28) = B_29
      | ~ r2_hidden(k4_tarski(A_28,B_29),C_30)
      | ~ v1_funct_1(C_30)
      | ~ v1_relat_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_8137,plain,(
    ! [C_478,A_479,B_480] :
      ( k1_funct_1(C_478,'#skF_3'(A_479,B_480,C_478)) = A_479
      | ~ v1_funct_1(C_478)
      | ~ r2_hidden(A_479,k9_relat_1(C_478,B_480))
      | ~ v1_relat_1(C_478) ) ),
    inference(resolution,[status(thm)],[c_1323,c_34])).

tff(c_8162,plain,(
    ! [A_479] :
      ( k1_funct_1('#skF_7','#skF_3'(A_479,'#skF_5','#skF_7')) = A_479
      | ~ v1_funct_1('#skF_7')
      | ~ r2_hidden(A_479,k2_relat_1('#skF_7'))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2014,c_8137])).

tff(c_8934,plain,(
    ! [A_510] :
      ( k1_funct_1('#skF_7','#skF_3'(A_510,'#skF_5','#skF_7')) = A_510
      | ~ r2_hidden(A_510,k2_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_68,c_8162])).

tff(c_8989,plain,(
    k1_funct_1('#skF_7','#skF_3'('#skF_4','#skF_5','#skF_7')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_358,c_8934])).

tff(c_9016,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4318,c_8989])).

tff(c_9017,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1986])).

tff(c_10,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_115,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(A_63,B_64)
      | ~ m1_subset_1(A_63,k1_zfmisc_1(B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_134,plain,(
    ! [A_65] : r1_tarski(k1_xboole_0,A_65) ),
    inference(resolution,[status(thm)],[c_10,c_115])).

tff(c_89,plain,(
    ! [A_59] :
      ( v1_xboole_0(A_59)
      | r2_hidden('#skF_1'(A_59),A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ! [B_32,A_31] :
      ( ~ r1_tarski(B_32,A_31)
      | ~ r2_hidden(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_100,plain,(
    ! [A_59] :
      ( ~ r1_tarski(A_59,'#skF_1'(A_59))
      | v1_xboole_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_89,c_38])).

tff(c_139,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_134,c_100])).

tff(c_9063,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9017,c_139])).

tff(c_9068,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_706,c_9063])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:22:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.57/2.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.57/2.72  
% 7.57/2.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.57/2.72  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3
% 7.57/2.72  
% 7.57/2.72  %Foreground sorts:
% 7.57/2.72  
% 7.57/2.72  
% 7.57/2.72  %Background operators:
% 7.57/2.72  
% 7.57/2.72  
% 7.57/2.72  %Foreground operators:
% 7.57/2.72  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.57/2.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.57/2.72  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.57/2.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.57/2.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.57/2.72  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.57/2.72  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.57/2.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.57/2.72  tff('#skF_7', type, '#skF_7': $i).
% 7.57/2.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.57/2.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.57/2.72  tff('#skF_5', type, '#skF_5': $i).
% 7.57/2.72  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.57/2.72  tff('#skF_6', type, '#skF_6': $i).
% 7.57/2.72  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.57/2.72  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.57/2.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.57/2.72  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.57/2.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.57/2.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.57/2.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.57/2.72  tff('#skF_4', type, '#skF_4': $i).
% 7.57/2.72  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.57/2.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.57/2.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.57/2.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.57/2.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.57/2.72  
% 7.57/2.73  tff(f_143, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_funct_2)).
% 7.57/2.73  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.57/2.73  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.57/2.73  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 7.57/2.73  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 7.57/2.73  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.57/2.73  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.57/2.73  tff(f_127, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 7.57/2.73  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 7.57/2.73  tff(f_74, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 7.57/2.73  tff(f_47, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 7.57/2.73  tff(f_88, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 7.57/2.73  tff(f_43, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 7.57/2.73  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.57/2.73  tff(f_93, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 7.57/2.73  tff(c_64, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.57/2.73  tff(c_325, plain, (![A_100, B_101, C_102]: (k2_relset_1(A_100, B_101, C_102)=k2_relat_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.57/2.73  tff(c_352, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_64, c_325])).
% 7.57/2.73  tff(c_62, plain, (r2_hidden('#skF_4', k2_relset_1('#skF_5', '#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.57/2.73  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.57/2.73  tff(c_88, plain, (~v1_xboole_0(k2_relset_1('#skF_5', '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_62, c_2])).
% 7.57/2.73  tff(c_357, plain, (~v1_xboole_0(k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_352, c_88])).
% 7.57/2.73  tff(c_598, plain, (![A_128, B_129, C_130]: (m1_subset_1(k2_relset_1(A_128, B_129, C_130), k1_zfmisc_1(B_129)) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.57/2.73  tff(c_628, plain, (m1_subset_1(k2_relat_1('#skF_7'), k1_zfmisc_1('#skF_6')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_352, c_598])).
% 7.57/2.73  tff(c_639, plain, (m1_subset_1(k2_relat_1('#skF_7'), k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_628])).
% 7.57/2.73  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.57/2.73  tff(c_258, plain, (![C_88, A_89, B_90]: (r2_hidden(C_88, A_89) | ~r2_hidden(C_88, B_90) | ~m1_subset_1(B_90, k1_zfmisc_1(A_89)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.57/2.73  tff(c_439, plain, (![A_113, A_114]: (r2_hidden('#skF_1'(A_113), A_114) | ~m1_subset_1(A_113, k1_zfmisc_1(A_114)) | v1_xboole_0(A_113))), inference(resolution, [status(thm)], [c_4, c_258])).
% 7.57/2.73  tff(c_466, plain, (![A_114, A_113]: (~v1_xboole_0(A_114) | ~m1_subset_1(A_113, k1_zfmisc_1(A_114)) | v1_xboole_0(A_113))), inference(resolution, [status(thm)], [c_439, c_2])).
% 7.57/2.73  tff(c_695, plain, (~v1_xboole_0('#skF_6') | v1_xboole_0(k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_639, c_466])).
% 7.57/2.73  tff(c_706, plain, (~v1_xboole_0('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_357, c_695])).
% 7.57/2.73  tff(c_358, plain, (r2_hidden('#skF_4', k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_352, c_62])).
% 7.57/2.73  tff(c_147, plain, (![C_69, A_70, B_71]: (v1_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.57/2.73  tff(c_169, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_64, c_147])).
% 7.57/2.73  tff(c_66, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.57/2.73  tff(c_396, plain, (![A_107, B_108, C_109]: (k1_relset_1(A_107, B_108, C_109)=k1_relat_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.57/2.73  tff(c_423, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_64, c_396])).
% 7.57/2.73  tff(c_1941, plain, (![B_219, A_220, C_221]: (k1_xboole_0=B_219 | k1_relset_1(A_220, B_219, C_221)=A_220 | ~v1_funct_2(C_221, A_220, B_219) | ~m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(A_220, B_219))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.57/2.73  tff(c_1968, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_5' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_64, c_1941])).
% 7.57/2.73  tff(c_1986, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_423, c_1968])).
% 7.57/2.73  tff(c_1990, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitLeft, [status(thm)], [c_1986])).
% 7.57/2.73  tff(c_30, plain, (![A_27]: (k9_relat_1(A_27, k1_relat_1(A_27))=k2_relat_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.57/2.73  tff(c_2004, plain, (k9_relat_1('#skF_7', '#skF_5')=k2_relat_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1990, c_30])).
% 7.57/2.73  tff(c_2014, plain, (k9_relat_1('#skF_7', '#skF_5')=k2_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_2004])).
% 7.57/2.73  tff(c_827, plain, (![A_140, B_141, C_142]: (r2_hidden('#skF_3'(A_140, B_141, C_142), B_141) | ~r2_hidden(A_140, k9_relat_1(C_142, B_141)) | ~v1_relat_1(C_142))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.57/2.73  tff(c_12, plain, (![A_12, B_13]: (m1_subset_1(A_12, B_13) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.57/2.73  tff(c_3282, plain, (![A_275, B_276, C_277]: (m1_subset_1('#skF_3'(A_275, B_276, C_277), B_276) | ~r2_hidden(A_275, k9_relat_1(C_277, B_276)) | ~v1_relat_1(C_277))), inference(resolution, [status(thm)], [c_827, c_12])).
% 7.57/2.73  tff(c_3286, plain, (![A_275]: (m1_subset_1('#skF_3'(A_275, '#skF_5', '#skF_7'), '#skF_5') | ~r2_hidden(A_275, k2_relat_1('#skF_7')) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2014, c_3282])).
% 7.57/2.73  tff(c_4261, plain, (![A_314]: (m1_subset_1('#skF_3'(A_314, '#skF_5', '#skF_7'), '#skF_5') | ~r2_hidden(A_314, k2_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_3286])).
% 7.57/2.73  tff(c_4308, plain, (m1_subset_1('#skF_3'('#skF_4', '#skF_5', '#skF_7'), '#skF_5')), inference(resolution, [status(thm)], [c_358, c_4261])).
% 7.57/2.73  tff(c_60, plain, (![E_49]: (k1_funct_1('#skF_7', E_49)!='#skF_4' | ~m1_subset_1(E_49, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.57/2.73  tff(c_4318, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_4', '#skF_5', '#skF_7'))!='#skF_4'), inference(resolution, [status(thm)], [c_4308, c_60])).
% 7.57/2.73  tff(c_68, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.57/2.73  tff(c_1323, plain, (![A_180, B_181, C_182]: (r2_hidden(k4_tarski('#skF_3'(A_180, B_181, C_182), A_180), C_182) | ~r2_hidden(A_180, k9_relat_1(C_182, B_181)) | ~v1_relat_1(C_182))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.57/2.73  tff(c_34, plain, (![C_30, A_28, B_29]: (k1_funct_1(C_30, A_28)=B_29 | ~r2_hidden(k4_tarski(A_28, B_29), C_30) | ~v1_funct_1(C_30) | ~v1_relat_1(C_30))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.57/2.73  tff(c_8137, plain, (![C_478, A_479, B_480]: (k1_funct_1(C_478, '#skF_3'(A_479, B_480, C_478))=A_479 | ~v1_funct_1(C_478) | ~r2_hidden(A_479, k9_relat_1(C_478, B_480)) | ~v1_relat_1(C_478))), inference(resolution, [status(thm)], [c_1323, c_34])).
% 7.57/2.73  tff(c_8162, plain, (![A_479]: (k1_funct_1('#skF_7', '#skF_3'(A_479, '#skF_5', '#skF_7'))=A_479 | ~v1_funct_1('#skF_7') | ~r2_hidden(A_479, k2_relat_1('#skF_7')) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2014, c_8137])).
% 7.57/2.73  tff(c_8934, plain, (![A_510]: (k1_funct_1('#skF_7', '#skF_3'(A_510, '#skF_5', '#skF_7'))=A_510 | ~r2_hidden(A_510, k2_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_68, c_8162])).
% 7.57/2.73  tff(c_8989, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_4', '#skF_5', '#skF_7'))='#skF_4'), inference(resolution, [status(thm)], [c_358, c_8934])).
% 7.57/2.73  tff(c_9016, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4318, c_8989])).
% 7.57/2.73  tff(c_9017, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_1986])).
% 7.57/2.73  tff(c_10, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.57/2.73  tff(c_115, plain, (![A_63, B_64]: (r1_tarski(A_63, B_64) | ~m1_subset_1(A_63, k1_zfmisc_1(B_64)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.57/2.73  tff(c_134, plain, (![A_65]: (r1_tarski(k1_xboole_0, A_65))), inference(resolution, [status(thm)], [c_10, c_115])).
% 7.57/2.73  tff(c_89, plain, (![A_59]: (v1_xboole_0(A_59) | r2_hidden('#skF_1'(A_59), A_59))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.57/2.73  tff(c_38, plain, (![B_32, A_31]: (~r1_tarski(B_32, A_31) | ~r2_hidden(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.57/2.73  tff(c_100, plain, (![A_59]: (~r1_tarski(A_59, '#skF_1'(A_59)) | v1_xboole_0(A_59))), inference(resolution, [status(thm)], [c_89, c_38])).
% 7.57/2.73  tff(c_139, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_134, c_100])).
% 7.57/2.73  tff(c_9063, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_9017, c_139])).
% 7.57/2.73  tff(c_9068, plain, $false, inference(negUnitSimplification, [status(thm)], [c_706, c_9063])).
% 7.57/2.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.57/2.73  
% 7.57/2.73  Inference rules
% 7.57/2.73  ----------------------
% 7.57/2.73  #Ref     : 0
% 7.57/2.73  #Sup     : 1808
% 7.57/2.73  #Fact    : 0
% 7.57/2.73  #Define  : 0
% 7.57/2.73  #Split   : 34
% 7.57/2.73  #Chain   : 0
% 7.57/2.73  #Close   : 0
% 7.57/2.73  
% 7.57/2.73  Ordering : KBO
% 7.57/2.73  
% 7.57/2.73  Simplification rules
% 7.57/2.73  ----------------------
% 7.57/2.73  #Subsume      : 284
% 7.57/2.73  #Demod        : 480
% 7.57/2.73  #Tautology    : 203
% 7.57/2.73  #SimpNegUnit  : 39
% 7.57/2.73  #BackRed      : 81
% 7.57/2.73  
% 7.57/2.73  #Partial instantiations: 0
% 7.57/2.73  #Strategies tried      : 1
% 7.57/2.73  
% 7.57/2.73  Timing (in seconds)
% 7.57/2.73  ----------------------
% 7.57/2.74  Preprocessing        : 0.35
% 7.57/2.74  Parsing              : 0.18
% 7.57/2.74  CNF conversion       : 0.02
% 7.57/2.74  Main loop            : 1.62
% 7.57/2.74  Inferencing          : 0.46
% 7.57/2.74  Reduction            : 0.55
% 7.57/2.74  Demodulation         : 0.36
% 7.57/2.74  BG Simplification    : 0.06
% 7.57/2.74  Subsumption          : 0.39
% 7.57/2.74  Abstraction          : 0.07
% 7.57/2.74  MUC search           : 0.00
% 7.57/2.74  Cooper               : 0.00
% 7.57/2.74  Total                : 2.00
% 7.57/2.74  Index Insertion      : 0.00
% 7.57/2.74  Index Deletion       : 0.00
% 7.57/2.74  Index Matching       : 0.00
% 7.57/2.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
