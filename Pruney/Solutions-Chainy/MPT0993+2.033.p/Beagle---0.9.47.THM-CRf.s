%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:47 EST 2020

% Result     : Theorem 4.43s
% Output     : CNFRefutation 4.84s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 723 expanded)
%              Number of leaves         :   32 ( 238 expanded)
%              Depth                    :   14
%              Number of atoms          :  223 (1655 expanded)
%              Number of equality atoms :   94 ( 593 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(A,C)
         => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_87,axiom,(
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

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_300,plain,(
    ! [A_62,B_63,D_64] :
      ( r2_relset_1(A_62,B_63,D_64,D_64)
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_311,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_300])).

tff(c_48,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_132,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_145,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_132])).

tff(c_52,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_365,plain,(
    ! [A_82,B_83,C_84] :
      ( k1_relset_1(A_82,B_83,C_84) = k1_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_380,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_365])).

tff(c_663,plain,(
    ! [B_127,A_128,C_129] :
      ( k1_xboole_0 = B_127
      | k1_relset_1(A_128,B_127,C_129) = A_128
      | ~ v1_funct_2(C_129,A_128,B_127)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_128,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_670,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_663])).

tff(c_680,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_380,c_670])).

tff(c_682,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_680])).

tff(c_22,plain,(
    ! [B_11,A_10] :
      ( k7_relat_1(B_11,A_10) = B_11
      | ~ r1_tarski(k1_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_690,plain,(
    ! [A_10] :
      ( k7_relat_1('#skF_4',A_10) = '#skF_4'
      | ~ r1_tarski('#skF_1',A_10)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_682,c_22])).

tff(c_716,plain,(
    ! [A_130] :
      ( k7_relat_1('#skF_4',A_130) = '#skF_4'
      | ~ r1_tarski('#skF_1',A_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_690])).

tff(c_726,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_48,c_716])).

tff(c_54,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_474,plain,(
    ! [A_98,B_99,C_100,D_101] :
      ( k2_partfun1(A_98,B_99,C_100,D_101) = k7_relat_1(C_100,D_101)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99)))
      | ~ v1_funct_1(C_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_479,plain,(
    ! [D_101] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_101) = k7_relat_1('#skF_4',D_101)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_474])).

tff(c_487,plain,(
    ! [D_101] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_101) = k7_relat_1('#skF_4',D_101) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_479])).

tff(c_46,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_489,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_46])).

tff(c_727,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_726,c_489])).

tff(c_730,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_727])).

tff(c_731,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_680])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_762,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_731,c_8])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_760,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_731,c_731,c_12])).

tff(c_86,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,B_38)
      | ~ m1_subset_1(A_37,k1_zfmisc_1(B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_94,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_86])).

tff(c_95,plain,(
    ! [B_39,A_40] :
      ( B_39 = A_40
      | ~ r1_tarski(B_39,A_40)
      | ~ r1_tarski(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_106,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_94,c_95])).

tff(c_147,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_808,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_760,c_147])).

tff(c_813,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_762,c_808])).

tff(c_814,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_817,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_814,c_50])).

tff(c_1028,plain,(
    ! [A_156,B_157,D_158] :
      ( r2_relset_1(A_156,B_157,D_158,D_158)
      | ~ m1_subset_1(D_158,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1049,plain,(
    ! [D_164] :
      ( r2_relset_1('#skF_1','#skF_2',D_164,D_164)
      | ~ m1_subset_1(D_164,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_814,c_1028])).

tff(c_1055,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_817,c_1049])).

tff(c_1068,plain,(
    ! [A_171,B_172,C_173] :
      ( k1_relset_1(A_171,B_172,C_173) = k1_relat_1(C_173)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1132,plain,(
    ! [C_181] :
      ( k1_relset_1('#skF_1','#skF_2',C_181) = k1_relat_1(C_181)
      | ~ m1_subset_1(C_181,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_814,c_1068])).

tff(c_1140,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_817,c_1132])).

tff(c_1573,plain,(
    ! [B_226,C_227,A_228] :
      ( k1_xboole_0 = B_226
      | v1_funct_2(C_227,A_228,B_226)
      | k1_relset_1(A_228,B_226,C_227) != A_228
      | ~ m1_subset_1(C_227,k1_zfmisc_1(k2_zfmisc_1(A_228,B_226))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1576,plain,(
    ! [C_227] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_2(C_227,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',C_227) != '#skF_1'
      | ~ m1_subset_1(C_227,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_814,c_1573])).

tff(c_1615,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1576])).

tff(c_853,plain,(
    ! [B_138,A_139] :
      ( k1_xboole_0 = B_138
      | k1_xboole_0 = A_139
      | k2_zfmisc_1(A_139,B_138) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_856,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_814,c_853])).

tff(c_868,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_856])).

tff(c_1638,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1615,c_868])).

tff(c_1795,plain,(
    ! [A_241] : k2_zfmisc_1(A_241,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1615,c_1615,c_12])).

tff(c_1838,plain,(
    '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1795,c_814])).

tff(c_1859,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1638,c_1838])).

tff(c_1861,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1576])).

tff(c_1874,plain,(
    ! [B_244,A_245,C_246] :
      ( k1_xboole_0 = B_244
      | k1_relset_1(A_245,B_244,C_246) = A_245
      | ~ v1_funct_2(C_246,A_245,B_244)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(A_245,B_244))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1877,plain,(
    ! [C_246] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_246) = '#skF_1'
      | ~ v1_funct_2(C_246,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_246,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_814,c_1874])).

tff(c_1891,plain,(
    ! [C_247] :
      ( k1_relset_1('#skF_1','#skF_2',C_247) = '#skF_1'
      | ~ v1_funct_2(C_247,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_247,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1861,c_1877])).

tff(c_1894,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_817,c_1891])).

tff(c_1901,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1140,c_1894])).

tff(c_1916,plain,(
    ! [A_10] :
      ( k7_relat_1('#skF_4',A_10) = '#skF_4'
      | ~ r1_tarski('#skF_1',A_10)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1901,c_22])).

tff(c_1961,plain,(
    ! [A_248] :
      ( k7_relat_1('#skF_4',A_248) = '#skF_4'
      | ~ r1_tarski('#skF_1',A_248) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_1916])).

tff(c_1971,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_48,c_1961])).

tff(c_1499,plain,(
    ! [A_216,B_217,C_218,D_219] :
      ( k2_partfun1(A_216,B_217,C_218,D_219) = k7_relat_1(C_218,D_219)
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(A_216,B_217)))
      | ~ v1_funct_1(C_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1533,plain,(
    ! [C_221,D_222] :
      ( k2_partfun1('#skF_1','#skF_2',C_221,D_222) = k7_relat_1(C_221,D_222)
      | ~ m1_subset_1(C_221,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_221) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_814,c_1499])).

tff(c_1535,plain,(
    ! [D_222] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_222) = k7_relat_1('#skF_4',D_222)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_817,c_1533])).

tff(c_1541,plain,(
    ! [D_222] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_222) = k7_relat_1('#skF_4',D_222) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1535])).

tff(c_1543,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1541,c_46])).

tff(c_2011,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1971,c_1543])).

tff(c_2014,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1055,c_2011])).

tff(c_2016,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_856])).

tff(c_2024,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2016,c_8])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2840,plain,(
    ! [A_366,B_367,D_368] :
      ( r2_relset_1(A_366,B_367,D_368,D_368)
      | ~ m1_subset_1(D_368,k1_zfmisc_1(k2_zfmisc_1(A_366,B_367))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2957,plain,(
    ! [A_392,B_393,A_394] :
      ( r2_relset_1(A_392,B_393,A_394,A_394)
      | ~ r1_tarski(A_394,k2_zfmisc_1(A_392,B_393)) ) ),
    inference(resolution,[status(thm)],[c_18,c_2840])).

tff(c_2971,plain,(
    ! [A_392,B_393] : r2_relset_1(A_392,B_393,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_2024,c_2957])).

tff(c_20,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k7_relat_1(B_9,A_8),B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_112,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_95])).

tff(c_2780,plain,(
    ! [A_361] :
      ( A_361 = '#skF_4'
      | ~ r1_tarski(A_361,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2016,c_2016,c_112])).

tff(c_2788,plain,(
    ! [A_8] :
      ( k7_relat_1('#skF_4',A_8) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_20,c_2780])).

tff(c_2797,plain,(
    ! [A_8] : k7_relat_1('#skF_4',A_8) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_2788])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2023,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_4',B_5) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2016,c_2016,c_14])).

tff(c_3014,plain,(
    ! [A_401,B_402,C_403,D_404] :
      ( k2_partfun1(A_401,B_402,C_403,D_404) = k7_relat_1(C_403,D_404)
      | ~ m1_subset_1(C_403,k1_zfmisc_1(k2_zfmisc_1(A_401,B_402)))
      | ~ v1_funct_1(C_403) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3479,plain,(
    ! [B_457,C_458,D_459] :
      ( k2_partfun1('#skF_4',B_457,C_458,D_459) = k7_relat_1(C_458,D_459)
      | ~ m1_subset_1(C_458,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_458) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2023,c_3014])).

tff(c_3481,plain,(
    ! [B_457,D_459] :
      ( k2_partfun1('#skF_4',B_457,'#skF_4',D_459) = k7_relat_1('#skF_4',D_459)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_817,c_3479])).

tff(c_3487,plain,(
    ! [B_457,D_459] : k2_partfun1('#skF_4',B_457,'#skF_4',D_459) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2797,c_3481])).

tff(c_2176,plain,(
    ! [A_265,B_266,D_267] :
      ( r2_relset_1(A_265,B_266,D_267,D_267)
      | ~ m1_subset_1(D_267,k1_zfmisc_1(k2_zfmisc_1(A_265,B_266))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2265,plain,(
    ! [A_292,B_293,A_294] :
      ( r2_relset_1(A_292,B_293,A_294,A_294)
      | ~ r1_tarski(A_294,k2_zfmisc_1(A_292,B_293)) ) ),
    inference(resolution,[status(thm)],[c_18,c_2176])).

tff(c_2279,plain,(
    ! [A_292,B_293] : r2_relset_1(A_292,B_293,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_2024,c_2265])).

tff(c_2105,plain,(
    ! [A_260] :
      ( A_260 = '#skF_4'
      | ~ r1_tarski(A_260,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2016,c_2016,c_112])).

tff(c_2113,plain,(
    ! [A_8] :
      ( k7_relat_1('#skF_4',A_8) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_20,c_2105])).

tff(c_2122,plain,(
    ! [A_8] : k7_relat_1('#skF_4',A_8) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_2113])).

tff(c_2022,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2016,c_2016,c_12])).

tff(c_2255,plain,(
    ! [A_286,B_287,C_288,D_289] :
      ( k2_partfun1(A_286,B_287,C_288,D_289) = k7_relat_1(C_288,D_289)
      | ~ m1_subset_1(C_288,k1_zfmisc_1(k2_zfmisc_1(A_286,B_287)))
      | ~ v1_funct_1(C_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2718,plain,(
    ! [A_355,C_356,D_357] :
      ( k2_partfun1(A_355,'#skF_4',C_356,D_357) = k7_relat_1(C_356,D_357)
      | ~ m1_subset_1(C_356,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_356) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2022,c_2255])).

tff(c_2720,plain,(
    ! [A_355,D_357] :
      ( k2_partfun1(A_355,'#skF_4','#skF_4',D_357) = k7_relat_1('#skF_4',D_357)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_817,c_2718])).

tff(c_2726,plain,(
    ! [A_355,D_357] : k2_partfun1(A_355,'#skF_4','#skF_4',D_357) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2122,c_2720])).

tff(c_2015,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_856])).

tff(c_2045,plain,
    ( '#skF_1' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2016,c_2016,c_2015])).

tff(c_2046,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2045])).

tff(c_2048,plain,(
    ~ r2_relset_1('#skF_1','#skF_4',k2_partfun1('#skF_1','#skF_4','#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2046,c_2046,c_46])).

tff(c_2728,plain,(
    ~ r2_relset_1('#skF_1','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2726,c_2048])).

tff(c_2731,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2279,c_2728])).

tff(c_2732,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2045])).

tff(c_2736,plain,(
    ~ r2_relset_1('#skF_4','#skF_2',k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2732,c_2732,c_46])).

tff(c_3489,plain,(
    ~ r2_relset_1('#skF_4','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3487,c_2736])).

tff(c_3492,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2971,c_3489])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:42:57 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.43/1.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.43/1.88  
% 4.43/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.43/1.89  %$ r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.43/1.89  
% 4.43/1.89  %Foreground sorts:
% 4.43/1.89  
% 4.43/1.89  
% 4.43/1.89  %Background operators:
% 4.43/1.89  
% 4.43/1.89  
% 4.43/1.89  %Foreground operators:
% 4.43/1.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.43/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.43/1.89  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.43/1.89  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.43/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.43/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.43/1.89  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.43/1.89  tff('#skF_2', type, '#skF_2': $i).
% 4.43/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.43/1.89  tff('#skF_1', type, '#skF_1': $i).
% 4.43/1.89  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.43/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.43/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.43/1.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.43/1.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.43/1.89  tff('#skF_4', type, '#skF_4': $i).
% 4.43/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.43/1.89  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 4.43/1.89  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.43/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.43/1.89  
% 4.84/1.91  tff(f_104, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_funct_2)).
% 4.84/1.91  tff(f_69, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.84/1.91  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.84/1.91  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.84/1.91  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.84/1.91  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 4.84/1.91  tff(f_93, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 4.84/1.91  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.84/1.91  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.84/1.91  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.84/1.91  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.84/1.91  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 4.84/1.91  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.84/1.91  tff(c_300, plain, (![A_62, B_63, D_64]: (r2_relset_1(A_62, B_63, D_64, D_64) | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.84/1.91  tff(c_311, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_300])).
% 4.84/1.91  tff(c_48, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.84/1.91  tff(c_132, plain, (![C_42, A_43, B_44]: (v1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.84/1.91  tff(c_145, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_132])).
% 4.84/1.91  tff(c_52, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.84/1.91  tff(c_365, plain, (![A_82, B_83, C_84]: (k1_relset_1(A_82, B_83, C_84)=k1_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.84/1.91  tff(c_380, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_365])).
% 4.84/1.91  tff(c_663, plain, (![B_127, A_128, C_129]: (k1_xboole_0=B_127 | k1_relset_1(A_128, B_127, C_129)=A_128 | ~v1_funct_2(C_129, A_128, B_127) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_128, B_127))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.84/1.91  tff(c_670, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_50, c_663])).
% 4.84/1.91  tff(c_680, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_380, c_670])).
% 4.84/1.91  tff(c_682, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(splitLeft, [status(thm)], [c_680])).
% 4.84/1.91  tff(c_22, plain, (![B_11, A_10]: (k7_relat_1(B_11, A_10)=B_11 | ~r1_tarski(k1_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.84/1.91  tff(c_690, plain, (![A_10]: (k7_relat_1('#skF_4', A_10)='#skF_4' | ~r1_tarski('#skF_1', A_10) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_682, c_22])).
% 4.84/1.91  tff(c_716, plain, (![A_130]: (k7_relat_1('#skF_4', A_130)='#skF_4' | ~r1_tarski('#skF_1', A_130))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_690])).
% 4.84/1.91  tff(c_726, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_48, c_716])).
% 4.84/1.91  tff(c_54, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.84/1.91  tff(c_474, plain, (![A_98, B_99, C_100, D_101]: (k2_partfun1(A_98, B_99, C_100, D_101)=k7_relat_1(C_100, D_101) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))) | ~v1_funct_1(C_100))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.84/1.91  tff(c_479, plain, (![D_101]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_101)=k7_relat_1('#skF_4', D_101) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_474])).
% 4.84/1.91  tff(c_487, plain, (![D_101]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_101)=k7_relat_1('#skF_4', D_101))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_479])).
% 4.84/1.91  tff(c_46, plain, (~r2_relset_1('#skF_1', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.84/1.91  tff(c_489, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_487, c_46])).
% 4.84/1.91  tff(c_727, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_726, c_489])).
% 4.84/1.91  tff(c_730, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_311, c_727])).
% 4.84/1.91  tff(c_731, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_680])).
% 4.84/1.91  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.84/1.91  tff(c_762, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_731, c_8])).
% 4.84/1.91  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.84/1.91  tff(c_760, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_731, c_731, c_12])).
% 4.84/1.91  tff(c_86, plain, (![A_37, B_38]: (r1_tarski(A_37, B_38) | ~m1_subset_1(A_37, k1_zfmisc_1(B_38)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.84/1.91  tff(c_94, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_50, c_86])).
% 4.84/1.91  tff(c_95, plain, (![B_39, A_40]: (B_39=A_40 | ~r1_tarski(B_39, A_40) | ~r1_tarski(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.84/1.91  tff(c_106, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_94, c_95])).
% 4.84/1.91  tff(c_147, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_4')), inference(splitLeft, [status(thm)], [c_106])).
% 4.84/1.91  tff(c_808, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_760, c_147])).
% 4.84/1.91  tff(c_813, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_762, c_808])).
% 4.84/1.91  tff(c_814, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_4'), inference(splitRight, [status(thm)], [c_106])).
% 4.84/1.91  tff(c_817, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_814, c_50])).
% 4.84/1.91  tff(c_1028, plain, (![A_156, B_157, D_158]: (r2_relset_1(A_156, B_157, D_158, D_158) | ~m1_subset_1(D_158, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.84/1.91  tff(c_1049, plain, (![D_164]: (r2_relset_1('#skF_1', '#skF_2', D_164, D_164) | ~m1_subset_1(D_164, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_814, c_1028])).
% 4.84/1.91  tff(c_1055, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_817, c_1049])).
% 4.84/1.91  tff(c_1068, plain, (![A_171, B_172, C_173]: (k1_relset_1(A_171, B_172, C_173)=k1_relat_1(C_173) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.84/1.91  tff(c_1132, plain, (![C_181]: (k1_relset_1('#skF_1', '#skF_2', C_181)=k1_relat_1(C_181) | ~m1_subset_1(C_181, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_814, c_1068])).
% 4.84/1.91  tff(c_1140, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_817, c_1132])).
% 4.84/1.91  tff(c_1573, plain, (![B_226, C_227, A_228]: (k1_xboole_0=B_226 | v1_funct_2(C_227, A_228, B_226) | k1_relset_1(A_228, B_226, C_227)!=A_228 | ~m1_subset_1(C_227, k1_zfmisc_1(k2_zfmisc_1(A_228, B_226))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.84/1.91  tff(c_1576, plain, (![C_227]: (k1_xboole_0='#skF_2' | v1_funct_2(C_227, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', C_227)!='#skF_1' | ~m1_subset_1(C_227, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_814, c_1573])).
% 4.84/1.91  tff(c_1615, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1576])).
% 4.84/1.91  tff(c_853, plain, (![B_138, A_139]: (k1_xboole_0=B_138 | k1_xboole_0=A_139 | k2_zfmisc_1(A_139, B_138)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.84/1.91  tff(c_856, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_814, c_853])).
% 4.84/1.91  tff(c_868, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_856])).
% 4.84/1.91  tff(c_1638, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1615, c_868])).
% 4.84/1.91  tff(c_1795, plain, (![A_241]: (k2_zfmisc_1(A_241, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1615, c_1615, c_12])).
% 4.84/1.91  tff(c_1838, plain, ('#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1795, c_814])).
% 4.84/1.91  tff(c_1859, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1638, c_1838])).
% 4.84/1.91  tff(c_1861, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_1576])).
% 4.84/1.91  tff(c_1874, plain, (![B_244, A_245, C_246]: (k1_xboole_0=B_244 | k1_relset_1(A_245, B_244, C_246)=A_245 | ~v1_funct_2(C_246, A_245, B_244) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(A_245, B_244))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.84/1.91  tff(c_1877, plain, (![C_246]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_246)='#skF_1' | ~v1_funct_2(C_246, '#skF_1', '#skF_2') | ~m1_subset_1(C_246, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_814, c_1874])).
% 4.84/1.91  tff(c_1891, plain, (![C_247]: (k1_relset_1('#skF_1', '#skF_2', C_247)='#skF_1' | ~v1_funct_2(C_247, '#skF_1', '#skF_2') | ~m1_subset_1(C_247, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_1861, c_1877])).
% 4.84/1.91  tff(c_1894, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_817, c_1891])).
% 4.84/1.91  tff(c_1901, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1140, c_1894])).
% 4.84/1.91  tff(c_1916, plain, (![A_10]: (k7_relat_1('#skF_4', A_10)='#skF_4' | ~r1_tarski('#skF_1', A_10) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1901, c_22])).
% 4.84/1.91  tff(c_1961, plain, (![A_248]: (k7_relat_1('#skF_4', A_248)='#skF_4' | ~r1_tarski('#skF_1', A_248))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_1916])).
% 4.84/1.91  tff(c_1971, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_48, c_1961])).
% 4.84/1.91  tff(c_1499, plain, (![A_216, B_217, C_218, D_219]: (k2_partfun1(A_216, B_217, C_218, D_219)=k7_relat_1(C_218, D_219) | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(A_216, B_217))) | ~v1_funct_1(C_218))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.84/1.91  tff(c_1533, plain, (![C_221, D_222]: (k2_partfun1('#skF_1', '#skF_2', C_221, D_222)=k7_relat_1(C_221, D_222) | ~m1_subset_1(C_221, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_221))), inference(superposition, [status(thm), theory('equality')], [c_814, c_1499])).
% 4.84/1.91  tff(c_1535, plain, (![D_222]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_222)=k7_relat_1('#skF_4', D_222) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_817, c_1533])).
% 4.84/1.91  tff(c_1541, plain, (![D_222]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_222)=k7_relat_1('#skF_4', D_222))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1535])).
% 4.84/1.91  tff(c_1543, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1541, c_46])).
% 4.84/1.91  tff(c_2011, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1971, c_1543])).
% 4.84/1.91  tff(c_2014, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1055, c_2011])).
% 4.84/1.91  tff(c_2016, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_856])).
% 4.84/1.91  tff(c_2024, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2016, c_8])).
% 4.84/1.91  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.84/1.91  tff(c_2840, plain, (![A_366, B_367, D_368]: (r2_relset_1(A_366, B_367, D_368, D_368) | ~m1_subset_1(D_368, k1_zfmisc_1(k2_zfmisc_1(A_366, B_367))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.84/1.91  tff(c_2957, plain, (![A_392, B_393, A_394]: (r2_relset_1(A_392, B_393, A_394, A_394) | ~r1_tarski(A_394, k2_zfmisc_1(A_392, B_393)))), inference(resolution, [status(thm)], [c_18, c_2840])).
% 4.84/1.91  tff(c_2971, plain, (![A_392, B_393]: (r2_relset_1(A_392, B_393, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_2024, c_2957])).
% 4.84/1.91  tff(c_20, plain, (![B_9, A_8]: (r1_tarski(k7_relat_1(B_9, A_8), B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.84/1.91  tff(c_112, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_95])).
% 4.84/1.91  tff(c_2780, plain, (![A_361]: (A_361='#skF_4' | ~r1_tarski(A_361, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2016, c_2016, c_112])).
% 4.84/1.91  tff(c_2788, plain, (![A_8]: (k7_relat_1('#skF_4', A_8)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_20, c_2780])).
% 4.84/1.91  tff(c_2797, plain, (![A_8]: (k7_relat_1('#skF_4', A_8)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_2788])).
% 4.84/1.91  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.84/1.91  tff(c_2023, plain, (![B_5]: (k2_zfmisc_1('#skF_4', B_5)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2016, c_2016, c_14])).
% 4.84/1.91  tff(c_3014, plain, (![A_401, B_402, C_403, D_404]: (k2_partfun1(A_401, B_402, C_403, D_404)=k7_relat_1(C_403, D_404) | ~m1_subset_1(C_403, k1_zfmisc_1(k2_zfmisc_1(A_401, B_402))) | ~v1_funct_1(C_403))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.84/1.91  tff(c_3479, plain, (![B_457, C_458, D_459]: (k2_partfun1('#skF_4', B_457, C_458, D_459)=k7_relat_1(C_458, D_459) | ~m1_subset_1(C_458, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_458))), inference(superposition, [status(thm), theory('equality')], [c_2023, c_3014])).
% 4.84/1.91  tff(c_3481, plain, (![B_457, D_459]: (k2_partfun1('#skF_4', B_457, '#skF_4', D_459)=k7_relat_1('#skF_4', D_459) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_817, c_3479])).
% 4.84/1.91  tff(c_3487, plain, (![B_457, D_459]: (k2_partfun1('#skF_4', B_457, '#skF_4', D_459)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2797, c_3481])).
% 4.84/1.91  tff(c_2176, plain, (![A_265, B_266, D_267]: (r2_relset_1(A_265, B_266, D_267, D_267) | ~m1_subset_1(D_267, k1_zfmisc_1(k2_zfmisc_1(A_265, B_266))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.84/1.91  tff(c_2265, plain, (![A_292, B_293, A_294]: (r2_relset_1(A_292, B_293, A_294, A_294) | ~r1_tarski(A_294, k2_zfmisc_1(A_292, B_293)))), inference(resolution, [status(thm)], [c_18, c_2176])).
% 4.84/1.91  tff(c_2279, plain, (![A_292, B_293]: (r2_relset_1(A_292, B_293, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_2024, c_2265])).
% 4.84/1.91  tff(c_2105, plain, (![A_260]: (A_260='#skF_4' | ~r1_tarski(A_260, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2016, c_2016, c_112])).
% 4.84/1.91  tff(c_2113, plain, (![A_8]: (k7_relat_1('#skF_4', A_8)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_20, c_2105])).
% 4.84/1.91  tff(c_2122, plain, (![A_8]: (k7_relat_1('#skF_4', A_8)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_2113])).
% 4.84/1.91  tff(c_2022, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2016, c_2016, c_12])).
% 4.84/1.91  tff(c_2255, plain, (![A_286, B_287, C_288, D_289]: (k2_partfun1(A_286, B_287, C_288, D_289)=k7_relat_1(C_288, D_289) | ~m1_subset_1(C_288, k1_zfmisc_1(k2_zfmisc_1(A_286, B_287))) | ~v1_funct_1(C_288))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.84/1.91  tff(c_2718, plain, (![A_355, C_356, D_357]: (k2_partfun1(A_355, '#skF_4', C_356, D_357)=k7_relat_1(C_356, D_357) | ~m1_subset_1(C_356, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_356))), inference(superposition, [status(thm), theory('equality')], [c_2022, c_2255])).
% 4.84/1.91  tff(c_2720, plain, (![A_355, D_357]: (k2_partfun1(A_355, '#skF_4', '#skF_4', D_357)=k7_relat_1('#skF_4', D_357) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_817, c_2718])).
% 4.84/1.91  tff(c_2726, plain, (![A_355, D_357]: (k2_partfun1(A_355, '#skF_4', '#skF_4', D_357)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2122, c_2720])).
% 4.84/1.91  tff(c_2015, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_856])).
% 4.84/1.91  tff(c_2045, plain, ('#skF_1'='#skF_4' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2016, c_2016, c_2015])).
% 4.84/1.91  tff(c_2046, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_2045])).
% 4.84/1.91  tff(c_2048, plain, (~r2_relset_1('#skF_1', '#skF_4', k2_partfun1('#skF_1', '#skF_4', '#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2046, c_2046, c_46])).
% 4.84/1.91  tff(c_2728, plain, (~r2_relset_1('#skF_1', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2726, c_2048])).
% 4.84/1.91  tff(c_2731, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2279, c_2728])).
% 4.84/1.91  tff(c_2732, plain, ('#skF_1'='#skF_4'), inference(splitRight, [status(thm)], [c_2045])).
% 4.84/1.91  tff(c_2736, plain, (~r2_relset_1('#skF_4', '#skF_2', k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2732, c_2732, c_46])).
% 4.84/1.91  tff(c_3489, plain, (~r2_relset_1('#skF_4', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3487, c_2736])).
% 4.84/1.91  tff(c_3492, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2971, c_3489])).
% 4.84/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.84/1.91  
% 4.84/1.91  Inference rules
% 4.84/1.91  ----------------------
% 4.84/1.91  #Ref     : 0
% 4.84/1.91  #Sup     : 732
% 4.84/1.91  #Fact    : 0
% 4.84/1.91  #Define  : 0
% 4.84/1.91  #Split   : 13
% 4.84/1.91  #Chain   : 0
% 4.84/1.91  #Close   : 0
% 4.84/1.91  
% 4.84/1.91  Ordering : KBO
% 4.84/1.91  
% 4.84/1.91  Simplification rules
% 4.84/1.91  ----------------------
% 4.84/1.91  #Subsume      : 61
% 4.84/1.91  #Demod        : 930
% 4.84/1.91  #Tautology    : 466
% 4.84/1.91  #SimpNegUnit  : 3
% 4.84/1.91  #BackRed      : 101
% 4.84/1.91  
% 4.84/1.91  #Partial instantiations: 0
% 4.84/1.91  #Strategies tried      : 1
% 4.84/1.91  
% 4.84/1.91  Timing (in seconds)
% 4.84/1.91  ----------------------
% 4.84/1.91  Preprocessing        : 0.34
% 4.84/1.91  Parsing              : 0.18
% 4.84/1.91  CNF conversion       : 0.02
% 4.84/1.91  Main loop            : 0.74
% 4.84/1.91  Inferencing          : 0.28
% 4.84/1.91  Reduction            : 0.25
% 4.84/1.91  Demodulation         : 0.18
% 4.84/1.91  BG Simplification    : 0.03
% 4.84/1.91  Subsumption          : 0.12
% 4.84/1.91  Abstraction          : 0.04
% 4.84/1.91  MUC search           : 0.00
% 4.84/1.91  Cooper               : 0.00
% 4.84/1.91  Total                : 1.13
% 4.84/1.91  Index Insertion      : 0.00
% 4.84/1.91  Index Deletion       : 0.00
% 4.84/1.91  Index Matching       : 0.00
% 4.84/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
