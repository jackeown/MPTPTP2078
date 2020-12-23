%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:35 EST 2020

% Result     : Theorem 8.39s
% Output     : CNFRefutation 8.77s
% Verified   : 
% Statistics : Number of formulae       :  328 (3726 expanded)
%              Number of leaves         :   47 (1216 expanded)
%              Depth                    :   20
%              Number of atoms          :  508 (8494 expanded)
%              Number of equality atoms :  140 (1904 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_163,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_130,axiom,(
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

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_146,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_104,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_134,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_136,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_61,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

tff(c_80,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_2339,plain,(
    ! [C_186,A_187,B_188] :
      ( v1_relat_1(C_186)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2360,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_2339])).

tff(c_84,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_588,plain,(
    ! [C_91,B_92,A_93] :
      ( v5_relat_1(C_91,B_92)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_93,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_607,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_588])).

tff(c_509,plain,(
    ! [C_77,A_78,B_79] :
      ( v1_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_526,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_509])).

tff(c_76,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_1350,plain,(
    ! [A_149,B_150,C_151] :
      ( k2_relset_1(A_149,B_150,C_151) = k2_relat_1(C_151)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1360,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_1350])).

tff(c_1371,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1360])).

tff(c_20,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1386,plain,(
    ! [A_9] :
      ( r1_tarski('#skF_2',A_9)
      | ~ v5_relat_1('#skF_3',A_9)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1371,c_20])).

tff(c_1463,plain,(
    ! [A_156] :
      ( r1_tarski('#skF_2',A_156)
      | ~ v5_relat_1('#skF_3',A_156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_1386])).

tff(c_1476,plain,(
    r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_607,c_1463])).

tff(c_16,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_30,plain,(
    ! [A_14] :
      ( v1_funct_1(k2_funct_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_74,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_177,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_180,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_177])).

tff(c_183,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_180])).

tff(c_294,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_304,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_294])).

tff(c_314,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_304])).

tff(c_315,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_485,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_315])).

tff(c_495,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_16,c_485])).

tff(c_82,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_1427,plain,(
    ! [A_152,B_153,C_154] :
      ( k1_relset_1(A_152,B_153,C_154) = k1_relat_1(C_154)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1446,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_1427])).

tff(c_1823,plain,(
    ! [B_168,A_169,C_170] :
      ( k1_xboole_0 = B_168
      | k1_relset_1(A_169,B_168,C_170) = A_169
      | ~ v1_funct_2(C_170,A_169,B_168)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(A_169,B_168))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1842,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_1823])).

tff(c_1861,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1446,c_1842])).

tff(c_1863,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1861])).

tff(c_32,plain,(
    ! [A_14] :
      ( v1_relat_1(k2_funct_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_78,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_687,plain,(
    ! [A_108] :
      ( k4_relat_1(A_108) = k2_funct_1(A_108)
      | ~ v2_funct_1(A_108)
      | ~ v1_funct_1(A_108)
      | ~ v1_relat_1(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_690,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_687])).

tff(c_693,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_84,c_690])).

tff(c_22,plain,(
    ! [A_11] :
      ( k2_relat_1(k4_relat_1(A_11)) = k1_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_697,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_693,c_22])).

tff(c_704,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_697])).

tff(c_711,plain,(
    ! [A_9] :
      ( r1_tarski(k1_relat_1('#skF_3'),A_9)
      | ~ v5_relat_1(k2_funct_1('#skF_3'),A_9)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_704,c_20])).

tff(c_772,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_711])).

tff(c_775,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_772])).

tff(c_779,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_84,c_775])).

tff(c_781,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_711])).

tff(c_316,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_24,plain,(
    ! [A_11] :
      ( k1_relat_1(k4_relat_1(A_11)) = k2_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_700,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_693,c_24])).

tff(c_706,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_700])).

tff(c_1373,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1371,c_706])).

tff(c_1509,plain,(
    ! [A_160] :
      ( m1_subset_1(A_160,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_160),k2_relat_1(A_160))))
      | ~ v1_funct_1(A_160)
      | ~ v1_relat_1(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1560,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_704,c_1509])).

tff(c_1588,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_781,c_316,c_1373,c_1560])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1797,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_1588,c_14])).

tff(c_1864,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1863,c_1797])).

tff(c_1884,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_495,c_1864])).

tff(c_1885,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1861])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( v5_relat_1(B_10,A_9)
      | ~ r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1389,plain,(
    ! [A_9] :
      ( v5_relat_1('#skF_3',A_9)
      | ~ r1_tarski('#skF_2',A_9)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1371,c_18])).

tff(c_1451,plain,(
    ! [A_155] :
      ( v5_relat_1('#skF_3',A_155)
      | ~ r1_tarski('#skF_2',A_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_1389])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_875,plain,(
    ! [C_121,A_122,B_123] :
      ( v1_xboole_0(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123)))
      | ~ v1_xboole_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_891,plain,(
    ! [C_121] :
      ( v1_xboole_0(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_875])).

tff(c_928,plain,(
    ! [C_127] :
      ( v1_xboole_0(C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_891])).

tff(c_939,plain,(
    ! [A_128] :
      ( v1_xboole_0(A_128)
      | ~ r1_tarski(A_128,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_928])).

tff(c_950,plain,(
    ! [B_10] :
      ( v1_xboole_0(k2_relat_1(B_10))
      | ~ v5_relat_1(B_10,k1_xboole_0)
      | ~ v1_relat_1(B_10) ) ),
    inference(resolution,[status(thm)],[c_20,c_939])).

tff(c_1377,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v5_relat_1('#skF_3',k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1371,c_950])).

tff(c_1393,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v5_relat_1('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_1377])).

tff(c_1422,plain,(
    ~ v5_relat_1('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1393])).

tff(c_1459,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1451,c_1422])).

tff(c_1893,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1885,c_1459])).

tff(c_1937,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1476,c_1893])).

tff(c_1938,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1393])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_2011,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1938,c_4])).

tff(c_8,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2048,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2011,c_2011,c_8])).

tff(c_335,plain,(
    ! [B_64,A_65] :
      ( v1_xboole_0(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65))
      | ~ v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_353,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_80,c_335])).

tff(c_377,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_353])).

tff(c_2284,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2048,c_377])).

tff(c_2289,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1938,c_2284])).

tff(c_2291,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_315])).

tff(c_2413,plain,(
    ! [C_197,B_198,A_199] :
      ( v5_relat_1(C_197,B_198)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_199,B_198))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2433,plain,(
    v5_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_2291,c_2413])).

tff(c_2357,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2291,c_2339])).

tff(c_2599,plain,(
    ! [A_221] :
      ( k4_relat_1(A_221) = k2_funct_1(A_221)
      | ~ v2_funct_1(A_221)
      | ~ v1_funct_1(A_221)
      | ~ v1_relat_1(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2602,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_2599])).

tff(c_2605,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2360,c_84,c_2602])).

tff(c_2609,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2605,c_22])).

tff(c_2616,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2360,c_2609])).

tff(c_2637,plain,(
    ! [A_9] :
      ( r1_tarski(k1_relat_1('#skF_3'),A_9)
      | ~ v5_relat_1(k2_funct_1('#skF_3'),A_9)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2616,c_20])).

tff(c_2800,plain,(
    ! [A_236] :
      ( r1_tarski(k1_relat_1('#skF_3'),A_236)
      | ~ v5_relat_1(k2_funct_1('#skF_3'),A_236) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2357,c_2637])).

tff(c_2809,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_2433,c_2800])).

tff(c_2290,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_315])).

tff(c_4138,plain,(
    ! [A_288,B_289,C_290] :
      ( k2_relset_1(A_288,B_289,C_290) = k2_relat_1(C_290)
      | ~ m1_subset_1(C_290,k1_zfmisc_1(k2_zfmisc_1(A_288,B_289))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_4157,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_4138])).

tff(c_4172,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_4157])).

tff(c_2612,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2605,c_24])).

tff(c_2618,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2360,c_2612])).

tff(c_4177,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4172,c_2618])).

tff(c_4287,plain,(
    ! [A_293,B_294,C_295] :
      ( k1_relset_1(A_293,B_294,C_295) = k1_relat_1(C_295)
      | ~ m1_subset_1(C_295,k1_zfmisc_1(k2_zfmisc_1(A_293,B_294))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_4293,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2291,c_4287])).

tff(c_4312,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4177,c_4293])).

tff(c_4518,plain,(
    ! [B_302,C_303,A_304] :
      ( k1_xboole_0 = B_302
      | v1_funct_2(C_303,A_304,B_302)
      | k1_relset_1(A_304,B_302,C_303) != A_304
      | ~ m1_subset_1(C_303,k1_zfmisc_1(k2_zfmisc_1(A_304,B_302))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_4530,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_2291,c_4518])).

tff(c_4556,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4312,c_4530])).

tff(c_4557,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_2290,c_4556])).

tff(c_2640,plain,(
    ! [A_9] :
      ( v5_relat_1(k2_funct_1('#skF_3'),A_9)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_9)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2616,c_18])).

tff(c_3984,plain,(
    ! [A_281] :
      ( v5_relat_1(k2_funct_1('#skF_3'),A_281)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_281) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2357,c_2640])).

tff(c_2526,plain,(
    ! [C_213,A_214,B_215] :
      ( v1_xboole_0(C_213)
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1(A_214,B_215)))
      | ~ v1_xboole_0(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2545,plain,(
    ! [C_213] :
      ( v1_xboole_0(C_213)
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2526])).

tff(c_2588,plain,(
    ! [C_220] :
      ( v1_xboole_0(C_220)
      | ~ m1_subset_1(C_220,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2545])).

tff(c_2620,plain,(
    ! [A_222] :
      ( v1_xboole_0(A_222)
      | ~ r1_tarski(A_222,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_2588])).

tff(c_3897,plain,(
    ! [B_279] :
      ( v1_xboole_0(k2_relat_1(B_279))
      | ~ v5_relat_1(B_279,k1_xboole_0)
      | ~ v1_relat_1(B_279) ) ),
    inference(resolution,[status(thm)],[c_20,c_2620])).

tff(c_3912,plain,
    ( v1_xboole_0(k1_relat_1('#skF_3'))
    | ~ v5_relat_1(k2_funct_1('#skF_3'),k1_xboole_0)
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2616,c_3897])).

tff(c_3921,plain,
    ( v1_xboole_0(k1_relat_1('#skF_3'))
    | ~ v5_relat_1(k2_funct_1('#skF_3'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2357,c_3912])).

tff(c_3979,plain,(
    ~ v5_relat_1(k2_funct_1('#skF_3'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_3921])).

tff(c_3991,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3984,c_3979])).

tff(c_4575,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4557,c_3991])).

tff(c_4610,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2809,c_4575])).

tff(c_4611,plain,(
    v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3921])).

tff(c_4620,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4611,c_4])).

tff(c_68,plain,(
    ! [A_37] :
      ( m1_subset_1(A_37,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_37),k2_relat_1(A_37))))
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_4632,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_3'))))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4620,c_68])).

tff(c_4639,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2360,c_84,c_10,c_4632])).

tff(c_2551,plain,(
    ! [C_213] :
      ( v1_xboole_0(C_213)
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2545])).

tff(c_4700,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4639,c_2551])).

tff(c_4715,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4700,c_4])).

tff(c_154,plain,(
    ! [A_46] : m1_subset_1(k6_partfun1(A_46),k1_zfmisc_1(k2_zfmisc_1(A_46,A_46))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_158,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_154])).

tff(c_338,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_158,c_335])).

tff(c_350,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_338])).

tff(c_357,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_350,c_4])).

tff(c_360,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_158])).

tff(c_2732,plain,(
    ! [C_229,B_230] :
      ( v5_relat_1(C_229,B_230)
      | ~ m1_subset_1(C_229,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2413])).

tff(c_2738,plain,(
    ! [B_230] : v5_relat_1(k1_xboole_0,B_230) ),
    inference(resolution,[status(thm)],[c_360,c_2732])).

tff(c_66,plain,(
    ! [A_36] : k6_relat_1(A_36) = k6_partfun1(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_26,plain,(
    ! [A_12] : k4_relat_1(k6_relat_1(A_12)) = k6_relat_1(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_85,plain,(
    ! [A_12] : k4_relat_1(k6_partfun1(A_12)) = k6_partfun1(A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_66,c_26])).

tff(c_368,plain,(
    k6_partfun1(k1_xboole_0) = k4_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_85])).

tff(c_375,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_368])).

tff(c_381,plain,
    ( k2_relat_1(k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_22])).

tff(c_426,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_381])).

tff(c_64,plain,(
    ! [A_35] : m1_subset_1(k6_partfun1(A_35),k1_zfmisc_1(k2_zfmisc_1(A_35,A_35))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_460,plain,(
    ! [C_72,A_73,B_74] :
      ( v1_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_478,plain,(
    ! [A_75] : v1_relat_1(k6_partfun1(A_75)) ),
    inference(resolution,[status(thm)],[c_64,c_460])).

tff(c_480,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_478])).

tff(c_482,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_426,c_480])).

tff(c_484,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_381])).

tff(c_483,plain,(
    k2_relat_1(k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_381])).

tff(c_2479,plain,(
    ! [B_207,A_208] :
      ( r1_tarski(k2_relat_1(B_207),A_208)
      | ~ v5_relat_1(B_207,A_208)
      | ~ v1_relat_1(B_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2496,plain,(
    ! [A_208] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),A_208)
      | ~ v5_relat_1(k1_xboole_0,A_208)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_2479])).

tff(c_2505,plain,(
    ! [A_208] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),A_208)
      | ~ v5_relat_1(k1_xboole_0,A_208) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_484,c_2496])).

tff(c_2747,plain,(
    ! [A_234] : r1_tarski(k1_relat_1(k1_xboole_0),A_234) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2738,c_2505])).

tff(c_2598,plain,(
    ! [A_7] :
      ( v1_xboole_0(A_7)
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_2588])).

tff(c_2763,plain,(
    v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_2747,c_2598])).

tff(c_2798,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2763,c_4])).

tff(c_2813,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2798,c_483])).

tff(c_4738,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4715,c_4715,c_2813])).

tff(c_5003,plain,(
    ! [A_313,B_314,C_315] :
      ( k2_relset_1(A_313,B_314,C_315) = k2_relat_1(C_315)
      | ~ m1_subset_1(C_315,k1_zfmisc_1(k2_zfmisc_1(A_313,B_314))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_5016,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_5003])).

tff(c_5021,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4738,c_76,c_5016])).

tff(c_2546,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2291,c_2526])).

tff(c_2565,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2546])).

tff(c_5023,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5021,c_2565])).

tff(c_5031,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4700,c_5023])).

tff(c_5033,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2546])).

tff(c_5037,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_5033,c_4])).

tff(c_5054,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5037,c_5037,c_8])).

tff(c_5128,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5054,c_377])).

tff(c_5133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5033,c_5128])).

tff(c_5134,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_353])).

tff(c_5139,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_5134,c_4])).

tff(c_5153,plain,(
    k6_partfun1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5139,c_5139,c_357])).

tff(c_5605,plain,(
    ! [A_360] : k2_zfmisc_1(A_360,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5139,c_5139,c_8])).

tff(c_5614,plain,(
    m1_subset_1(k6_partfun1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5605,c_64])).

tff(c_5622,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5153,c_5614])).

tff(c_5156,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_3',B_3) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5139,c_5139,c_10])).

tff(c_6569,plain,(
    ! [C_435,B_436,A_437] :
      ( v5_relat_1(C_435,B_436)
      | ~ m1_subset_1(C_435,k1_zfmisc_1(k2_zfmisc_1(A_437,B_436))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6607,plain,(
    ! [C_442,B_443] :
      ( v5_relat_1(C_442,B_443)
      | ~ m1_subset_1(C_442,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5156,c_6569])).

tff(c_6613,plain,(
    ! [B_443] : v5_relat_1('#skF_3',B_443) ),
    inference(resolution,[status(thm)],[c_5622,c_6607])).

tff(c_5666,plain,(
    ! [C_362,A_363,B_364] :
      ( v1_relat_1(C_362)
      | ~ m1_subset_1(C_362,k1_zfmisc_1(k2_zfmisc_1(A_363,B_364))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_5686,plain,(
    ! [A_365] : v1_relat_1(k6_partfun1(A_365)) ),
    inference(resolution,[status(thm)],[c_64,c_5666])).

tff(c_5688,plain,(
    v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5153,c_5686])).

tff(c_5581,plain,(
    k4_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5139,c_5139,c_375])).

tff(c_5588,plain,
    ( k2_relat_1('#skF_3') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5581,c_24])).

tff(c_5733,plain,(
    k2_relat_1('#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5688,c_5588])).

tff(c_5737,plain,(
    ! [A_9] :
      ( r1_tarski(k1_relat_1('#skF_3'),A_9)
      | ~ v5_relat_1('#skF_3',A_9)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5733,c_20])).

tff(c_5741,plain,(
    ! [A_9] :
      ( r1_tarski(k1_relat_1('#skF_3'),A_9)
      | ~ v5_relat_1('#skF_3',A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5688,c_5737])).

tff(c_6645,plain,(
    ! [A_454] : r1_tarski(k1_relat_1('#skF_3'),A_454) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6613,c_5741])).

tff(c_351,plain,(
    ! [A_7,B_8] :
      ( v1_xboole_0(A_7)
      | ~ v1_xboole_0(B_8)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(resolution,[status(thm)],[c_16,c_335])).

tff(c_6657,plain,(
    ! [A_454] :
      ( v1_xboole_0(k1_relat_1('#skF_3'))
      | ~ v1_xboole_0(A_454) ) ),
    inference(resolution,[status(thm)],[c_6645,c_351])).

tff(c_6664,plain,(
    ! [A_454] : ~ v1_xboole_0(A_454) ),
    inference(splitLeft,[status(thm)],[c_6657])).

tff(c_6669,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6664,c_5134])).

tff(c_6670,plain,(
    v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_6657])).

tff(c_5155,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5139,c_4])).

tff(c_6698,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6670,c_5155])).

tff(c_6644,plain,(
    ! [A_9] : r1_tarski(k1_relat_1('#skF_3'),A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6613,c_5741])).

tff(c_6701,plain,(
    ! [A_9] : r1_tarski('#skF_3',A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6698,c_6644])).

tff(c_7157,plain,(
    ! [A_485,B_486,C_487] :
      ( k1_relset_1(A_485,B_486,C_487) = k1_relat_1(C_487)
      | ~ m1_subset_1(C_487,k1_zfmisc_1(k2_zfmisc_1(A_485,B_486))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_9469,plain,(
    ! [A_569,B_570,A_571] :
      ( k1_relset_1(A_569,B_570,A_571) = k1_relat_1(A_571)
      | ~ r1_tarski(A_571,k2_zfmisc_1(A_569,B_570)) ) ),
    inference(resolution,[status(thm)],[c_16,c_7157])).

tff(c_9480,plain,(
    ! [A_569,B_570] : k1_relset_1(A_569,B_570,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6701,c_9469])).

tff(c_9497,plain,(
    ! [A_569,B_570] : k1_relset_1(A_569,B_570,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6698,c_9480])).

tff(c_54,plain,(
    ! [C_34,B_33] :
      ( v1_funct_2(C_34,k1_xboole_0,B_33)
      | k1_relset_1(k1_xboole_0,B_33,C_34) != k1_xboole_0
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_87,plain,(
    ! [C_34,B_33] :
      ( v1_funct_2(C_34,k1_xboole_0,B_33)
      | k1_relset_1(k1_xboole_0,B_33,C_34) != k1_xboole_0
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_54])).

tff(c_7929,plain,(
    ! [C_525,B_526] :
      ( v1_funct_2(C_525,'#skF_3',B_526)
      | k1_relset_1('#skF_3',B_526,C_525) != '#skF_3'
      | ~ m1_subset_1(C_525,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5139,c_5139,c_5139,c_5139,c_87])).

tff(c_8790,plain,(
    ! [B_551] :
      ( v1_funct_2('#skF_3','#skF_3',B_551)
      | k1_relset_1('#skF_3',B_551,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_5622,c_7929])).

tff(c_5135,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_353])).

tff(c_5625,plain,(
    ! [A_361] :
      ( A_361 = '#skF_3'
      | ~ v1_xboole_0(A_361) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5139,c_4])).

tff(c_5632,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_5135,c_5625])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( k1_xboole_0 = B_3
      | k1_xboole_0 = A_2
      | k2_zfmisc_1(A_2,B_3) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_6128,plain,(
    ! [B_413,A_414] :
      ( B_413 = '#skF_3'
      | A_414 = '#skF_3'
      | k2_zfmisc_1(A_414,B_413) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5139,c_5139,c_5139,c_6])).

tff(c_6138,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_5632,c_6128])).

tff(c_6143,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_6138])).

tff(c_6197,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6143,c_5134])).

tff(c_5154,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5139,c_5139,c_8])).

tff(c_6191,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6143,c_6143,c_5154])).

tff(c_5246,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5139,c_5139,c_360])).

tff(c_5351,plain,(
    ! [C_334,B_335,A_336] :
      ( v5_relat_1(C_334,B_335)
      | ~ m1_subset_1(C_334,k1_zfmisc_1(k2_zfmisc_1(A_336,B_335))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_5429,plain,(
    ! [C_346,B_347] :
      ( v5_relat_1(C_346,B_347)
      | ~ m1_subset_1(C_346,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5156,c_5351])).

tff(c_5435,plain,(
    ! [B_347] : v5_relat_1('#skF_3',B_347) ),
    inference(resolution,[status(thm)],[c_5246,c_5429])).

tff(c_5262,plain,(
    ! [C_323,A_324,B_325] :
      ( v1_relat_1(C_323)
      | ~ m1_subset_1(C_323,k1_zfmisc_1(k2_zfmisc_1(A_324,B_325))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_5278,plain,(
    ! [A_326] : v1_relat_1(k6_partfun1(A_326)) ),
    inference(resolution,[status(thm)],[c_64,c_5262])).

tff(c_5280,plain,(
    v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5153,c_5278])).

tff(c_5179,plain,(
    k4_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5139,c_5139,c_375])).

tff(c_5186,plain,
    ( k2_relat_1('#skF_3') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5179,c_24])).

tff(c_5324,plain,(
    k2_relat_1('#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5280,c_5186])).

tff(c_5328,plain,(
    ! [A_9] :
      ( r1_tarski(k1_relat_1('#skF_3'),A_9)
      | ~ v5_relat_1('#skF_3',A_9)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5324,c_20])).

tff(c_5332,plain,(
    ! [A_9] :
      ( r1_tarski(k1_relat_1('#skF_3'),A_9)
      | ~ v5_relat_1('#skF_3',A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5280,c_5328])).

tff(c_5443,plain,(
    ! [A_351] : r1_tarski(k1_relat_1('#skF_3'),A_351) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5435,c_5332])).

tff(c_5456,plain,(
    ! [A_351] :
      ( v1_xboole_0(k1_relat_1('#skF_3'))
      | ~ v1_xboole_0(A_351) ) ),
    inference(resolution,[status(thm)],[c_5443,c_351])).

tff(c_5492,plain,(
    ! [A_351] : ~ v1_xboole_0(A_351) ),
    inference(splitLeft,[status(thm)],[c_5456])).

tff(c_5497,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5492,c_5134])).

tff(c_5498,plain,(
    v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_5456])).

tff(c_5502,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_5498,c_5155])).

tff(c_5442,plain,(
    ! [A_9] : r1_tarski(k1_relat_1('#skF_3'),A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5435,c_5332])).

tff(c_5505,plain,(
    ! [A_9] : r1_tarski('#skF_3',A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5502,c_5442])).

tff(c_5513,plain,(
    ! [A_357] :
      ( k4_relat_1(A_357) = k2_funct_1(A_357)
      | ~ v2_funct_1(A_357)
      | ~ v1_funct_1(A_357)
      | ~ v1_relat_1(A_357) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_5516,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_5513])).

tff(c_5519,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5280,c_84,c_5179,c_5516])).

tff(c_5177,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_315])).

tff(c_5521,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5519,c_5177])).

tff(c_5573,plain,(
    ~ r1_tarski('#skF_3',k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_16,c_5521])).

tff(c_5577,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5505,c_5573])).

tff(c_5579,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_315])).

tff(c_12,plain,(
    ! [B_6,A_4] :
      ( v1_xboole_0(B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_4))
      | ~ v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5641,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_5579,c_12])).

tff(c_5743,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_5641])).

tff(c_6424,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6191,c_5743])).

tff(c_6427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6197,c_6424])).

tff(c_6428,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6138])).

tff(c_6432,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6428,c_5743])).

tff(c_6439,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5134,c_5156,c_6432])).

tff(c_6441,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_5641])).

tff(c_6472,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6441,c_5155])).

tff(c_6911,plain,(
    ! [B_473,A_474] :
      ( B_473 = '#skF_3'
      | A_474 = '#skF_3'
      | k2_zfmisc_1(A_474,B_473) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5139,c_5139,c_5139,c_6])).

tff(c_6924,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_6472,c_6911])).

tff(c_6947,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_6924])).

tff(c_6440,plain,(
    v1_xboole_0(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_5641])).

tff(c_6445,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6440,c_5155])).

tff(c_5578,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_315])).

tff(c_6450,plain,(
    ~ v1_funct_2('#skF_3','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6445,c_5578])).

tff(c_6949,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6947,c_6450])).

tff(c_8806,plain,(
    k1_relset_1('#skF_3','#skF_1','#skF_3') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_8790,c_6949])).

tff(c_9506,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9497,c_8806])).

tff(c_9507,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_6924])).

tff(c_9508,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6924])).

tff(c_9549,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9507,c_9508])).

tff(c_50,plain,(
    ! [A_32] :
      ( v1_funct_2(k1_xboole_0,A_32,k1_xboole_0)
      | k1_xboole_0 = A_32
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_32,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_89,plain,(
    ! [A_32] :
      ( v1_funct_2(k1_xboole_0,A_32,k1_xboole_0)
      | k1_xboole_0 = A_32
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_50])).

tff(c_6661,plain,(
    ! [A_32] :
      ( v1_funct_2('#skF_3',A_32,'#skF_3')
      | A_32 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5622,c_5139,c_5139,c_5139,c_5139,c_5139,c_89])).

tff(c_10102,plain,(
    ! [A_605] :
      ( v1_funct_2('#skF_1',A_605,'#skF_1')
      | A_605 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9507,c_9507,c_9507,c_6661])).

tff(c_9526,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9507,c_6450])).

tff(c_10107,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_10102,c_9526])).

tff(c_10115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9549,c_10107])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:00:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.39/3.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.77/3.15  
% 8.77/3.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.77/3.15  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 8.77/3.15  
% 8.77/3.15  %Foreground sorts:
% 8.77/3.15  
% 8.77/3.15  
% 8.77/3.15  %Background operators:
% 8.77/3.15  
% 8.77/3.15  
% 8.77/3.15  %Foreground operators:
% 8.77/3.15  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.77/3.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.77/3.15  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.77/3.15  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.77/3.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.77/3.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.77/3.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.77/3.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.77/3.15  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.77/3.15  tff('#skF_2', type, '#skF_2': $i).
% 8.77/3.15  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 8.77/3.15  tff('#skF_3', type, '#skF_3': $i).
% 8.77/3.15  tff('#skF_1', type, '#skF_1': $i).
% 8.77/3.15  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.77/3.15  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.77/3.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.77/3.15  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 8.77/3.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.77/3.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.77/3.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.77/3.15  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.77/3.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.77/3.15  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.77/3.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.77/3.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.77/3.15  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 8.77/3.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.77/3.15  
% 8.77/3.19  tff(f_163, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 8.77/3.19  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.77/3.19  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.77/3.19  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.77/3.19  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.77/3.19  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 8.77/3.19  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.77/3.19  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 8.77/3.19  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.77/3.19  tff(f_130, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 8.77/3.19  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 8.77/3.19  tff(f_59, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 8.77/3.19  tff(f_146, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 8.77/3.19  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.77/3.19  tff(f_104, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 8.77/3.19  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 8.77/3.19  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 8.77/3.19  tff(f_134, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 8.77/3.19  tff(f_136, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 8.77/3.19  tff(f_61, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_relat_1)).
% 8.77/3.19  tff(c_80, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 8.77/3.19  tff(c_2339, plain, (![C_186, A_187, B_188]: (v1_relat_1(C_186) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.77/3.19  tff(c_2360, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_2339])).
% 8.77/3.19  tff(c_84, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 8.77/3.19  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.77/3.19  tff(c_588, plain, (![C_91, B_92, A_93]: (v5_relat_1(C_91, B_92) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_93, B_92))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.77/3.19  tff(c_607, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_80, c_588])).
% 8.77/3.19  tff(c_509, plain, (![C_77, A_78, B_79]: (v1_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.77/3.19  tff(c_526, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_509])).
% 8.77/3.19  tff(c_76, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_163])).
% 8.77/3.19  tff(c_1350, plain, (![A_149, B_150, C_151]: (k2_relset_1(A_149, B_150, C_151)=k2_relat_1(C_151) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.77/3.19  tff(c_1360, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_1350])).
% 8.77/3.19  tff(c_1371, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1360])).
% 8.77/3.19  tff(c_20, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.77/3.19  tff(c_1386, plain, (![A_9]: (r1_tarski('#skF_2', A_9) | ~v5_relat_1('#skF_3', A_9) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1371, c_20])).
% 8.77/3.19  tff(c_1463, plain, (![A_156]: (r1_tarski('#skF_2', A_156) | ~v5_relat_1('#skF_3', A_156))), inference(demodulation, [status(thm), theory('equality')], [c_526, c_1386])).
% 8.77/3.19  tff(c_1476, plain, (r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_607, c_1463])).
% 8.77/3.19  tff(c_16, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.77/3.19  tff(c_30, plain, (![A_14]: (v1_funct_1(k2_funct_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.77/3.19  tff(c_74, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 8.77/3.19  tff(c_177, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_74])).
% 8.77/3.19  tff(c_180, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_177])).
% 8.77/3.19  tff(c_183, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_180])).
% 8.77/3.19  tff(c_294, plain, (![C_58, A_59, B_60]: (v1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.77/3.19  tff(c_304, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_294])).
% 8.77/3.19  tff(c_314, plain, $false, inference(negUnitSimplification, [status(thm)], [c_183, c_304])).
% 8.77/3.19  tff(c_315, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_74])).
% 8.77/3.19  tff(c_485, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_315])).
% 8.77/3.19  tff(c_495, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_16, c_485])).
% 8.77/3.19  tff(c_82, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 8.77/3.19  tff(c_1427, plain, (![A_152, B_153, C_154]: (k1_relset_1(A_152, B_153, C_154)=k1_relat_1(C_154) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.77/3.19  tff(c_1446, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_1427])).
% 8.77/3.19  tff(c_1823, plain, (![B_168, A_169, C_170]: (k1_xboole_0=B_168 | k1_relset_1(A_169, B_168, C_170)=A_169 | ~v1_funct_2(C_170, A_169, B_168) | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(A_169, B_168))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.77/3.19  tff(c_1842, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_80, c_1823])).
% 8.77/3.19  tff(c_1861, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1446, c_1842])).
% 8.77/3.19  tff(c_1863, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_1861])).
% 8.77/3.19  tff(c_32, plain, (![A_14]: (v1_relat_1(k2_funct_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.77/3.19  tff(c_78, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 8.77/3.19  tff(c_687, plain, (![A_108]: (k4_relat_1(A_108)=k2_funct_1(A_108) | ~v2_funct_1(A_108) | ~v1_funct_1(A_108) | ~v1_relat_1(A_108))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.77/3.19  tff(c_690, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_687])).
% 8.77/3.19  tff(c_693, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_526, c_84, c_690])).
% 8.77/3.19  tff(c_22, plain, (![A_11]: (k2_relat_1(k4_relat_1(A_11))=k1_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.77/3.19  tff(c_697, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_693, c_22])).
% 8.77/3.19  tff(c_704, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_526, c_697])).
% 8.77/3.19  tff(c_711, plain, (![A_9]: (r1_tarski(k1_relat_1('#skF_3'), A_9) | ~v5_relat_1(k2_funct_1('#skF_3'), A_9) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_704, c_20])).
% 8.77/3.19  tff(c_772, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_711])).
% 8.77/3.19  tff(c_775, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_772])).
% 8.77/3.19  tff(c_779, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_526, c_84, c_775])).
% 8.77/3.19  tff(c_781, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_711])).
% 8.77/3.19  tff(c_316, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_74])).
% 8.77/3.19  tff(c_24, plain, (![A_11]: (k1_relat_1(k4_relat_1(A_11))=k2_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.77/3.19  tff(c_700, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_693, c_24])).
% 8.77/3.19  tff(c_706, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_526, c_700])).
% 8.77/3.19  tff(c_1373, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1371, c_706])).
% 8.77/3.19  tff(c_1509, plain, (![A_160]: (m1_subset_1(A_160, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_160), k2_relat_1(A_160)))) | ~v1_funct_1(A_160) | ~v1_relat_1(A_160))), inference(cnfTransformation, [status(thm)], [f_146])).
% 8.77/3.19  tff(c_1560, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_704, c_1509])).
% 8.77/3.19  tff(c_1588, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_781, c_316, c_1373, c_1560])).
% 8.77/3.19  tff(c_14, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.77/3.19  tff(c_1797, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_1588, c_14])).
% 8.77/3.19  tff(c_1864, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1863, c_1797])).
% 8.77/3.19  tff(c_1884, plain, $false, inference(negUnitSimplification, [status(thm)], [c_495, c_1864])).
% 8.77/3.19  tff(c_1885, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1861])).
% 8.77/3.19  tff(c_18, plain, (![B_10, A_9]: (v5_relat_1(B_10, A_9) | ~r1_tarski(k2_relat_1(B_10), A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.77/3.19  tff(c_1389, plain, (![A_9]: (v5_relat_1('#skF_3', A_9) | ~r1_tarski('#skF_2', A_9) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1371, c_18])).
% 8.77/3.19  tff(c_1451, plain, (![A_155]: (v5_relat_1('#skF_3', A_155) | ~r1_tarski('#skF_2', A_155))), inference(demodulation, [status(thm), theory('equality')], [c_526, c_1389])).
% 8.77/3.19  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 8.77/3.19  tff(c_875, plain, (![C_121, A_122, B_123]: (v1_xboole_0(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))) | ~v1_xboole_0(A_122))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.77/3.19  tff(c_891, plain, (![C_121]: (v1_xboole_0(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_875])).
% 8.77/3.19  tff(c_928, plain, (![C_127]: (v1_xboole_0(C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_891])).
% 8.77/3.19  tff(c_939, plain, (![A_128]: (v1_xboole_0(A_128) | ~r1_tarski(A_128, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_928])).
% 8.77/3.19  tff(c_950, plain, (![B_10]: (v1_xboole_0(k2_relat_1(B_10)) | ~v5_relat_1(B_10, k1_xboole_0) | ~v1_relat_1(B_10))), inference(resolution, [status(thm)], [c_20, c_939])).
% 8.77/3.19  tff(c_1377, plain, (v1_xboole_0('#skF_2') | ~v5_relat_1('#skF_3', k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1371, c_950])).
% 8.77/3.19  tff(c_1393, plain, (v1_xboole_0('#skF_2') | ~v5_relat_1('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_526, c_1377])).
% 8.77/3.19  tff(c_1422, plain, (~v5_relat_1('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1393])).
% 8.77/3.19  tff(c_1459, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_1451, c_1422])).
% 8.77/3.19  tff(c_1893, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1885, c_1459])).
% 8.77/3.19  tff(c_1937, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1476, c_1893])).
% 8.77/3.19  tff(c_1938, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_1393])).
% 8.77/3.19  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 8.77/3.19  tff(c_2011, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_1938, c_4])).
% 8.77/3.19  tff(c_8, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.77/3.19  tff(c_2048, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2011, c_2011, c_8])).
% 8.77/3.19  tff(c_335, plain, (![B_64, A_65]: (v1_xboole_0(B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)) | ~v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.77/3.19  tff(c_353, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_80, c_335])).
% 8.77/3.19  tff(c_377, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_353])).
% 8.77/3.19  tff(c_2284, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2048, c_377])).
% 8.77/3.19  tff(c_2289, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1938, c_2284])).
% 8.77/3.19  tff(c_2291, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_315])).
% 8.77/3.19  tff(c_2413, plain, (![C_197, B_198, A_199]: (v5_relat_1(C_197, B_198) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_199, B_198))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.77/3.19  tff(c_2433, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_2291, c_2413])).
% 8.77/3.19  tff(c_2357, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2291, c_2339])).
% 8.77/3.19  tff(c_2599, plain, (![A_221]: (k4_relat_1(A_221)=k2_funct_1(A_221) | ~v2_funct_1(A_221) | ~v1_funct_1(A_221) | ~v1_relat_1(A_221))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.77/3.19  tff(c_2602, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_2599])).
% 8.77/3.19  tff(c_2605, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2360, c_84, c_2602])).
% 8.77/3.19  tff(c_2609, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2605, c_22])).
% 8.77/3.19  tff(c_2616, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2360, c_2609])).
% 8.77/3.19  tff(c_2637, plain, (![A_9]: (r1_tarski(k1_relat_1('#skF_3'), A_9) | ~v5_relat_1(k2_funct_1('#skF_3'), A_9) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2616, c_20])).
% 8.77/3.19  tff(c_2800, plain, (![A_236]: (r1_tarski(k1_relat_1('#skF_3'), A_236) | ~v5_relat_1(k2_funct_1('#skF_3'), A_236))), inference(demodulation, [status(thm), theory('equality')], [c_2357, c_2637])).
% 8.77/3.19  tff(c_2809, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_2433, c_2800])).
% 8.77/3.19  tff(c_2290, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_315])).
% 8.77/3.19  tff(c_4138, plain, (![A_288, B_289, C_290]: (k2_relset_1(A_288, B_289, C_290)=k2_relat_1(C_290) | ~m1_subset_1(C_290, k1_zfmisc_1(k2_zfmisc_1(A_288, B_289))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.77/3.19  tff(c_4157, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_4138])).
% 8.77/3.19  tff(c_4172, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_4157])).
% 8.77/3.19  tff(c_2612, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2605, c_24])).
% 8.77/3.19  tff(c_2618, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2360, c_2612])).
% 8.77/3.19  tff(c_4177, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4172, c_2618])).
% 8.77/3.19  tff(c_4287, plain, (![A_293, B_294, C_295]: (k1_relset_1(A_293, B_294, C_295)=k1_relat_1(C_295) | ~m1_subset_1(C_295, k1_zfmisc_1(k2_zfmisc_1(A_293, B_294))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.77/3.19  tff(c_4293, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2291, c_4287])).
% 8.77/3.19  tff(c_4312, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4177, c_4293])).
% 8.77/3.19  tff(c_4518, plain, (![B_302, C_303, A_304]: (k1_xboole_0=B_302 | v1_funct_2(C_303, A_304, B_302) | k1_relset_1(A_304, B_302, C_303)!=A_304 | ~m1_subset_1(C_303, k1_zfmisc_1(k2_zfmisc_1(A_304, B_302))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.77/3.19  tff(c_4530, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_2291, c_4518])).
% 8.77/3.19  tff(c_4556, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4312, c_4530])).
% 8.77/3.19  tff(c_4557, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_2290, c_4556])).
% 8.77/3.19  tff(c_2640, plain, (![A_9]: (v5_relat_1(k2_funct_1('#skF_3'), A_9) | ~r1_tarski(k1_relat_1('#skF_3'), A_9) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2616, c_18])).
% 8.77/3.19  tff(c_3984, plain, (![A_281]: (v5_relat_1(k2_funct_1('#skF_3'), A_281) | ~r1_tarski(k1_relat_1('#skF_3'), A_281))), inference(demodulation, [status(thm), theory('equality')], [c_2357, c_2640])).
% 8.77/3.19  tff(c_2526, plain, (![C_213, A_214, B_215]: (v1_xboole_0(C_213) | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1(A_214, B_215))) | ~v1_xboole_0(A_214))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.77/3.19  tff(c_2545, plain, (![C_213]: (v1_xboole_0(C_213) | ~m1_subset_1(C_213, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_2526])).
% 8.77/3.19  tff(c_2588, plain, (![C_220]: (v1_xboole_0(C_220) | ~m1_subset_1(C_220, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2545])).
% 8.77/3.19  tff(c_2620, plain, (![A_222]: (v1_xboole_0(A_222) | ~r1_tarski(A_222, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_2588])).
% 8.77/3.19  tff(c_3897, plain, (![B_279]: (v1_xboole_0(k2_relat_1(B_279)) | ~v5_relat_1(B_279, k1_xboole_0) | ~v1_relat_1(B_279))), inference(resolution, [status(thm)], [c_20, c_2620])).
% 8.77/3.19  tff(c_3912, plain, (v1_xboole_0(k1_relat_1('#skF_3')) | ~v5_relat_1(k2_funct_1('#skF_3'), k1_xboole_0) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2616, c_3897])).
% 8.77/3.19  tff(c_3921, plain, (v1_xboole_0(k1_relat_1('#skF_3')) | ~v5_relat_1(k2_funct_1('#skF_3'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2357, c_3912])).
% 8.77/3.19  tff(c_3979, plain, (~v5_relat_1(k2_funct_1('#skF_3'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_3921])).
% 8.77/3.19  tff(c_3991, plain, (~r1_tarski(k1_relat_1('#skF_3'), k1_xboole_0)), inference(resolution, [status(thm)], [c_3984, c_3979])).
% 8.77/3.19  tff(c_4575, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4557, c_3991])).
% 8.77/3.19  tff(c_4610, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2809, c_4575])).
% 8.77/3.19  tff(c_4611, plain, (v1_xboole_0(k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_3921])).
% 8.77/3.19  tff(c_4620, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_4611, c_4])).
% 8.77/3.19  tff(c_68, plain, (![A_37]: (m1_subset_1(A_37, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_37), k2_relat_1(A_37)))) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_146])).
% 8.77/3.19  tff(c_4632, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_3')))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4620, c_68])).
% 8.77/3.19  tff(c_4639, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2360, c_84, c_10, c_4632])).
% 8.77/3.19  tff(c_2551, plain, (![C_213]: (v1_xboole_0(C_213) | ~m1_subset_1(C_213, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2545])).
% 8.77/3.19  tff(c_4700, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_4639, c_2551])).
% 8.77/3.19  tff(c_4715, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_4700, c_4])).
% 8.77/3.19  tff(c_154, plain, (![A_46]: (m1_subset_1(k6_partfun1(A_46), k1_zfmisc_1(k2_zfmisc_1(A_46, A_46))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 8.77/3.19  tff(c_158, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_154])).
% 8.77/3.19  tff(c_338, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_158, c_335])).
% 8.77/3.19  tff(c_350, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_338])).
% 8.77/3.19  tff(c_357, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_350, c_4])).
% 8.77/3.19  tff(c_360, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_357, c_158])).
% 8.77/3.19  tff(c_2732, plain, (![C_229, B_230]: (v5_relat_1(C_229, B_230) | ~m1_subset_1(C_229, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_2413])).
% 8.77/3.19  tff(c_2738, plain, (![B_230]: (v5_relat_1(k1_xboole_0, B_230))), inference(resolution, [status(thm)], [c_360, c_2732])).
% 8.77/3.19  tff(c_66, plain, (![A_36]: (k6_relat_1(A_36)=k6_partfun1(A_36))), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.77/3.19  tff(c_26, plain, (![A_12]: (k4_relat_1(k6_relat_1(A_12))=k6_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.77/3.19  tff(c_85, plain, (![A_12]: (k4_relat_1(k6_partfun1(A_12))=k6_partfun1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_66, c_26])).
% 8.77/3.19  tff(c_368, plain, (k6_partfun1(k1_xboole_0)=k4_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_357, c_85])).
% 8.77/3.19  tff(c_375, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_357, c_368])).
% 8.77/3.19  tff(c_381, plain, (k2_relat_1(k1_xboole_0)=k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_375, c_22])).
% 8.77/3.19  tff(c_426, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_381])).
% 8.77/3.19  tff(c_64, plain, (![A_35]: (m1_subset_1(k6_partfun1(A_35), k1_zfmisc_1(k2_zfmisc_1(A_35, A_35))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 8.77/3.19  tff(c_460, plain, (![C_72, A_73, B_74]: (v1_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.77/3.19  tff(c_478, plain, (![A_75]: (v1_relat_1(k6_partfun1(A_75)))), inference(resolution, [status(thm)], [c_64, c_460])).
% 8.77/3.19  tff(c_480, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_357, c_478])).
% 8.77/3.19  tff(c_482, plain, $false, inference(negUnitSimplification, [status(thm)], [c_426, c_480])).
% 8.77/3.19  tff(c_484, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_381])).
% 8.77/3.19  tff(c_483, plain, (k2_relat_1(k1_xboole_0)=k1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_381])).
% 8.77/3.19  tff(c_2479, plain, (![B_207, A_208]: (r1_tarski(k2_relat_1(B_207), A_208) | ~v5_relat_1(B_207, A_208) | ~v1_relat_1(B_207))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.77/3.19  tff(c_2496, plain, (![A_208]: (r1_tarski(k1_relat_1(k1_xboole_0), A_208) | ~v5_relat_1(k1_xboole_0, A_208) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_483, c_2479])).
% 8.77/3.19  tff(c_2505, plain, (![A_208]: (r1_tarski(k1_relat_1(k1_xboole_0), A_208) | ~v5_relat_1(k1_xboole_0, A_208))), inference(demodulation, [status(thm), theory('equality')], [c_484, c_2496])).
% 8.77/3.19  tff(c_2747, plain, (![A_234]: (r1_tarski(k1_relat_1(k1_xboole_0), A_234))), inference(demodulation, [status(thm), theory('equality')], [c_2738, c_2505])).
% 8.77/3.19  tff(c_2598, plain, (![A_7]: (v1_xboole_0(A_7) | ~r1_tarski(A_7, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_2588])).
% 8.77/3.19  tff(c_2763, plain, (v1_xboole_0(k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2747, c_2598])).
% 8.77/3.19  tff(c_2798, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2763, c_4])).
% 8.77/3.19  tff(c_2813, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2798, c_483])).
% 8.77/3.19  tff(c_4738, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4715, c_4715, c_2813])).
% 8.77/3.19  tff(c_5003, plain, (![A_313, B_314, C_315]: (k2_relset_1(A_313, B_314, C_315)=k2_relat_1(C_315) | ~m1_subset_1(C_315, k1_zfmisc_1(k2_zfmisc_1(A_313, B_314))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.77/3.19  tff(c_5016, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_5003])).
% 8.77/3.19  tff(c_5021, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4738, c_76, c_5016])).
% 8.77/3.19  tff(c_2546, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_2291, c_2526])).
% 8.77/3.19  tff(c_2565, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_2546])).
% 8.77/3.19  tff(c_5023, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5021, c_2565])).
% 8.77/3.19  tff(c_5031, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4700, c_5023])).
% 8.77/3.19  tff(c_5033, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_2546])).
% 8.77/3.19  tff(c_5037, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_5033, c_4])).
% 8.77/3.19  tff(c_5054, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5037, c_5037, c_8])).
% 8.77/3.19  tff(c_5128, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5054, c_377])).
% 8.77/3.19  tff(c_5133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5033, c_5128])).
% 8.77/3.19  tff(c_5134, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_353])).
% 8.77/3.19  tff(c_5139, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_5134, c_4])).
% 8.77/3.19  tff(c_5153, plain, (k6_partfun1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5139, c_5139, c_357])).
% 8.77/3.19  tff(c_5605, plain, (![A_360]: (k2_zfmisc_1(A_360, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5139, c_5139, c_8])).
% 8.77/3.19  tff(c_5614, plain, (m1_subset_1(k6_partfun1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_5605, c_64])).
% 8.77/3.19  tff(c_5622, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5153, c_5614])).
% 8.77/3.19  tff(c_5156, plain, (![B_3]: (k2_zfmisc_1('#skF_3', B_3)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5139, c_5139, c_10])).
% 8.77/3.19  tff(c_6569, plain, (![C_435, B_436, A_437]: (v5_relat_1(C_435, B_436) | ~m1_subset_1(C_435, k1_zfmisc_1(k2_zfmisc_1(A_437, B_436))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.77/3.19  tff(c_6607, plain, (![C_442, B_443]: (v5_relat_1(C_442, B_443) | ~m1_subset_1(C_442, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5156, c_6569])).
% 8.77/3.19  tff(c_6613, plain, (![B_443]: (v5_relat_1('#skF_3', B_443))), inference(resolution, [status(thm)], [c_5622, c_6607])).
% 8.77/3.19  tff(c_5666, plain, (![C_362, A_363, B_364]: (v1_relat_1(C_362) | ~m1_subset_1(C_362, k1_zfmisc_1(k2_zfmisc_1(A_363, B_364))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.77/3.19  tff(c_5686, plain, (![A_365]: (v1_relat_1(k6_partfun1(A_365)))), inference(resolution, [status(thm)], [c_64, c_5666])).
% 8.77/3.19  tff(c_5688, plain, (v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5153, c_5686])).
% 8.77/3.19  tff(c_5581, plain, (k4_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5139, c_5139, c_375])).
% 8.77/3.19  tff(c_5588, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5581, c_24])).
% 8.77/3.19  tff(c_5733, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5688, c_5588])).
% 8.77/3.19  tff(c_5737, plain, (![A_9]: (r1_tarski(k1_relat_1('#skF_3'), A_9) | ~v5_relat_1('#skF_3', A_9) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_5733, c_20])).
% 8.77/3.19  tff(c_5741, plain, (![A_9]: (r1_tarski(k1_relat_1('#skF_3'), A_9) | ~v5_relat_1('#skF_3', A_9))), inference(demodulation, [status(thm), theory('equality')], [c_5688, c_5737])).
% 8.77/3.19  tff(c_6645, plain, (![A_454]: (r1_tarski(k1_relat_1('#skF_3'), A_454))), inference(demodulation, [status(thm), theory('equality')], [c_6613, c_5741])).
% 8.77/3.19  tff(c_351, plain, (![A_7, B_8]: (v1_xboole_0(A_7) | ~v1_xboole_0(B_8) | ~r1_tarski(A_7, B_8))), inference(resolution, [status(thm)], [c_16, c_335])).
% 8.77/3.19  tff(c_6657, plain, (![A_454]: (v1_xboole_0(k1_relat_1('#skF_3')) | ~v1_xboole_0(A_454))), inference(resolution, [status(thm)], [c_6645, c_351])).
% 8.77/3.19  tff(c_6664, plain, (![A_454]: (~v1_xboole_0(A_454))), inference(splitLeft, [status(thm)], [c_6657])).
% 8.77/3.19  tff(c_6669, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6664, c_5134])).
% 8.77/3.19  tff(c_6670, plain, (v1_xboole_0(k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_6657])).
% 8.77/3.19  tff(c_5155, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_5139, c_4])).
% 8.77/3.19  tff(c_6698, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_6670, c_5155])).
% 8.77/3.19  tff(c_6644, plain, (![A_9]: (r1_tarski(k1_relat_1('#skF_3'), A_9))), inference(demodulation, [status(thm), theory('equality')], [c_6613, c_5741])).
% 8.77/3.19  tff(c_6701, plain, (![A_9]: (r1_tarski('#skF_3', A_9))), inference(demodulation, [status(thm), theory('equality')], [c_6698, c_6644])).
% 8.77/3.19  tff(c_7157, plain, (![A_485, B_486, C_487]: (k1_relset_1(A_485, B_486, C_487)=k1_relat_1(C_487) | ~m1_subset_1(C_487, k1_zfmisc_1(k2_zfmisc_1(A_485, B_486))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.77/3.19  tff(c_9469, plain, (![A_569, B_570, A_571]: (k1_relset_1(A_569, B_570, A_571)=k1_relat_1(A_571) | ~r1_tarski(A_571, k2_zfmisc_1(A_569, B_570)))), inference(resolution, [status(thm)], [c_16, c_7157])).
% 8.77/3.19  tff(c_9480, plain, (![A_569, B_570]: (k1_relset_1(A_569, B_570, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_6701, c_9469])).
% 8.77/3.19  tff(c_9497, plain, (![A_569, B_570]: (k1_relset_1(A_569, B_570, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6698, c_9480])).
% 8.77/3.19  tff(c_54, plain, (![C_34, B_33]: (v1_funct_2(C_34, k1_xboole_0, B_33) | k1_relset_1(k1_xboole_0, B_33, C_34)!=k1_xboole_0 | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_33))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.77/3.19  tff(c_87, plain, (![C_34, B_33]: (v1_funct_2(C_34, k1_xboole_0, B_33) | k1_relset_1(k1_xboole_0, B_33, C_34)!=k1_xboole_0 | ~m1_subset_1(C_34, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_54])).
% 8.77/3.19  tff(c_7929, plain, (![C_525, B_526]: (v1_funct_2(C_525, '#skF_3', B_526) | k1_relset_1('#skF_3', B_526, C_525)!='#skF_3' | ~m1_subset_1(C_525, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_5139, c_5139, c_5139, c_5139, c_87])).
% 8.77/3.19  tff(c_8790, plain, (![B_551]: (v1_funct_2('#skF_3', '#skF_3', B_551) | k1_relset_1('#skF_3', B_551, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_5622, c_7929])).
% 8.77/3.19  tff(c_5135, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_353])).
% 8.77/3.19  tff(c_5625, plain, (![A_361]: (A_361='#skF_3' | ~v1_xboole_0(A_361))), inference(demodulation, [status(thm), theory('equality')], [c_5139, c_4])).
% 8.77/3.19  tff(c_5632, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_5135, c_5625])).
% 8.77/3.19  tff(c_6, plain, (![B_3, A_2]: (k1_xboole_0=B_3 | k1_xboole_0=A_2 | k2_zfmisc_1(A_2, B_3)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.77/3.19  tff(c_6128, plain, (![B_413, A_414]: (B_413='#skF_3' | A_414='#skF_3' | k2_zfmisc_1(A_414, B_413)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5139, c_5139, c_5139, c_6])).
% 8.77/3.19  tff(c_6138, plain, ('#skF_2'='#skF_3' | '#skF_3'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_5632, c_6128])).
% 8.77/3.19  tff(c_6143, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_6138])).
% 8.77/3.19  tff(c_6197, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6143, c_5134])).
% 8.77/3.19  tff(c_5154, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5139, c_5139, c_8])).
% 8.77/3.19  tff(c_6191, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6143, c_6143, c_5154])).
% 8.77/3.19  tff(c_5246, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5139, c_5139, c_360])).
% 8.77/3.19  tff(c_5351, plain, (![C_334, B_335, A_336]: (v5_relat_1(C_334, B_335) | ~m1_subset_1(C_334, k1_zfmisc_1(k2_zfmisc_1(A_336, B_335))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.77/3.19  tff(c_5429, plain, (![C_346, B_347]: (v5_relat_1(C_346, B_347) | ~m1_subset_1(C_346, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5156, c_5351])).
% 8.77/3.19  tff(c_5435, plain, (![B_347]: (v5_relat_1('#skF_3', B_347))), inference(resolution, [status(thm)], [c_5246, c_5429])).
% 8.77/3.19  tff(c_5262, plain, (![C_323, A_324, B_325]: (v1_relat_1(C_323) | ~m1_subset_1(C_323, k1_zfmisc_1(k2_zfmisc_1(A_324, B_325))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.77/3.19  tff(c_5278, plain, (![A_326]: (v1_relat_1(k6_partfun1(A_326)))), inference(resolution, [status(thm)], [c_64, c_5262])).
% 8.77/3.19  tff(c_5280, plain, (v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5153, c_5278])).
% 8.77/3.19  tff(c_5179, plain, (k4_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5139, c_5139, c_375])).
% 8.77/3.19  tff(c_5186, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5179, c_24])).
% 8.77/3.19  tff(c_5324, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5280, c_5186])).
% 8.77/3.19  tff(c_5328, plain, (![A_9]: (r1_tarski(k1_relat_1('#skF_3'), A_9) | ~v5_relat_1('#skF_3', A_9) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_5324, c_20])).
% 8.77/3.19  tff(c_5332, plain, (![A_9]: (r1_tarski(k1_relat_1('#skF_3'), A_9) | ~v5_relat_1('#skF_3', A_9))), inference(demodulation, [status(thm), theory('equality')], [c_5280, c_5328])).
% 8.77/3.19  tff(c_5443, plain, (![A_351]: (r1_tarski(k1_relat_1('#skF_3'), A_351))), inference(demodulation, [status(thm), theory('equality')], [c_5435, c_5332])).
% 8.77/3.19  tff(c_5456, plain, (![A_351]: (v1_xboole_0(k1_relat_1('#skF_3')) | ~v1_xboole_0(A_351))), inference(resolution, [status(thm)], [c_5443, c_351])).
% 8.77/3.19  tff(c_5492, plain, (![A_351]: (~v1_xboole_0(A_351))), inference(splitLeft, [status(thm)], [c_5456])).
% 8.77/3.19  tff(c_5497, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5492, c_5134])).
% 8.77/3.19  tff(c_5498, plain, (v1_xboole_0(k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_5456])).
% 8.77/3.19  tff(c_5502, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_5498, c_5155])).
% 8.77/3.19  tff(c_5442, plain, (![A_9]: (r1_tarski(k1_relat_1('#skF_3'), A_9))), inference(demodulation, [status(thm), theory('equality')], [c_5435, c_5332])).
% 8.77/3.19  tff(c_5505, plain, (![A_9]: (r1_tarski('#skF_3', A_9))), inference(demodulation, [status(thm), theory('equality')], [c_5502, c_5442])).
% 8.77/3.19  tff(c_5513, plain, (![A_357]: (k4_relat_1(A_357)=k2_funct_1(A_357) | ~v2_funct_1(A_357) | ~v1_funct_1(A_357) | ~v1_relat_1(A_357))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.77/3.19  tff(c_5516, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_5513])).
% 8.77/3.19  tff(c_5519, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5280, c_84, c_5179, c_5516])).
% 8.77/3.19  tff(c_5177, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_315])).
% 8.77/3.19  tff(c_5521, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_5519, c_5177])).
% 8.77/3.19  tff(c_5573, plain, (~r1_tarski('#skF_3', k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_16, c_5521])).
% 8.77/3.19  tff(c_5577, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5505, c_5573])).
% 8.77/3.19  tff(c_5579, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_315])).
% 8.77/3.19  tff(c_12, plain, (![B_6, A_4]: (v1_xboole_0(B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_4)) | ~v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.77/3.19  tff(c_5641, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_5579, c_12])).
% 8.77/3.19  tff(c_5743, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_5641])).
% 8.77/3.19  tff(c_6424, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6191, c_5743])).
% 8.77/3.19  tff(c_6427, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6197, c_6424])).
% 8.77/3.19  tff(c_6428, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_6138])).
% 8.77/3.19  tff(c_6432, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6428, c_5743])).
% 8.77/3.19  tff(c_6439, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5134, c_5156, c_6432])).
% 8.77/3.19  tff(c_6441, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_5641])).
% 8.77/3.19  tff(c_6472, plain, (k2_zfmisc_1('#skF_2', '#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_6441, c_5155])).
% 8.77/3.19  tff(c_6911, plain, (![B_473, A_474]: (B_473='#skF_3' | A_474='#skF_3' | k2_zfmisc_1(A_474, B_473)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5139, c_5139, c_5139, c_6])).
% 8.77/3.19  tff(c_6924, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_6472, c_6911])).
% 8.77/3.19  tff(c_6947, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_6924])).
% 8.77/3.19  tff(c_6440, plain, (v1_xboole_0(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_5641])).
% 8.77/3.19  tff(c_6445, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_6440, c_5155])).
% 8.77/3.19  tff(c_5578, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_315])).
% 8.77/3.19  tff(c_6450, plain, (~v1_funct_2('#skF_3', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6445, c_5578])).
% 8.77/3.19  tff(c_6949, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6947, c_6450])).
% 8.77/3.19  tff(c_8806, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_3')!='#skF_3'), inference(resolution, [status(thm)], [c_8790, c_6949])).
% 8.77/3.19  tff(c_9506, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9497, c_8806])).
% 8.77/3.19  tff(c_9507, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_6924])).
% 8.77/3.19  tff(c_9508, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_6924])).
% 8.77/3.19  tff(c_9549, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9507, c_9508])).
% 8.77/3.19  tff(c_50, plain, (![A_32]: (v1_funct_2(k1_xboole_0, A_32, k1_xboole_0) | k1_xboole_0=A_32 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_32, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.77/3.19  tff(c_89, plain, (![A_32]: (v1_funct_2(k1_xboole_0, A_32, k1_xboole_0) | k1_xboole_0=A_32 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_50])).
% 8.77/3.19  tff(c_6661, plain, (![A_32]: (v1_funct_2('#skF_3', A_32, '#skF_3') | A_32='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5622, c_5139, c_5139, c_5139, c_5139, c_5139, c_89])).
% 8.77/3.19  tff(c_10102, plain, (![A_605]: (v1_funct_2('#skF_1', A_605, '#skF_1') | A_605='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9507, c_9507, c_9507, c_6661])).
% 8.77/3.19  tff(c_9526, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9507, c_6450])).
% 8.77/3.19  tff(c_10107, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_10102, c_9526])).
% 8.77/3.19  tff(c_10115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9549, c_10107])).
% 8.77/3.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.77/3.19  
% 8.77/3.19  Inference rules
% 8.77/3.19  ----------------------
% 8.77/3.19  #Ref     : 0
% 8.77/3.19  #Sup     : 2150
% 8.77/3.19  #Fact    : 0
% 8.77/3.19  #Define  : 0
% 8.77/3.19  #Split   : 42
% 8.77/3.19  #Chain   : 0
% 8.77/3.19  #Close   : 0
% 8.77/3.19  
% 9.10/3.19  Ordering : KBO
% 9.10/3.19  
% 9.10/3.19  Simplification rules
% 9.10/3.19  ----------------------
% 9.10/3.19  #Subsume      : 235
% 9.10/3.19  #Demod        : 2806
% 9.10/3.19  #Tautology    : 1233
% 9.10/3.19  #SimpNegUnit  : 43
% 9.10/3.19  #BackRed      : 516
% 9.10/3.19  
% 9.10/3.19  #Partial instantiations: 0
% 9.10/3.19  #Strategies tried      : 1
% 9.10/3.19  
% 9.10/3.19  Timing (in seconds)
% 9.10/3.19  ----------------------
% 9.10/3.20  Preprocessing        : 0.57
% 9.10/3.20  Parsing              : 0.31
% 9.10/3.20  CNF conversion       : 0.04
% 9.10/3.20  Main loop            : 1.68
% 9.10/3.20  Inferencing          : 0.53
% 9.10/3.20  Reduction            : 0.62
% 9.10/3.20  Demodulation         : 0.44
% 9.10/3.20  BG Simplification    : 0.06
% 9.10/3.20  Subsumption          : 0.28
% 9.10/3.20  Abstraction          : 0.07
% 9.10/3.20  MUC search           : 0.00
% 9.10/3.20  Cooper               : 0.00
% 9.10/3.20  Total                : 2.35
% 9.10/3.20  Index Insertion      : 0.00
% 9.10/3.20  Index Deletion       : 0.00
% 9.10/3.20  Index Matching       : 0.00
% 9.10/3.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
