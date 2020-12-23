%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:41 EST 2020

% Result     : Theorem 10.99s
% Output     : CNFRefutation 11.19s
% Verified   : 
% Statistics : Number of formulae       :  226 (1480 expanded)
%              Number of leaves         :   42 ( 491 expanded)
%              Depth                    :   14
%              Number of atoms          :  378 (3781 expanded)
%              Number of equality atoms :  123 ( 768 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_151,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_106,axiom,(
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

tff(f_122,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_110,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_112,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_62,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_134,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_117,plain,(
    ! [C_43,A_44,B_45] :
      ( v1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_125,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_117])).

tff(c_72,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_20633,plain,(
    ! [C_536,B_537,A_538] :
      ( v1_xboole_0(C_536)
      | ~ m1_subset_1(C_536,k1_zfmisc_1(k2_zfmisc_1(B_537,A_538)))
      | ~ v1_xboole_0(A_538) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_20645,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_20633])).

tff(c_20646,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_20645])).

tff(c_64,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_166,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_xboole_0(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51)))
      | ~ v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_174,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_166])).

tff(c_175,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_174])).

tff(c_66,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_9529,plain,(
    ! [A_228,B_229,C_230] :
      ( k2_relset_1(A_228,B_229,C_230) = k2_relat_1(C_230)
      | ~ m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1(A_228,B_229))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_9544,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_9529])).

tff(c_9550,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_9544])).

tff(c_18,plain,(
    ! [A_6] :
      ( k1_relat_1(k2_funct_1(A_6)) = k2_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12,plain,(
    ! [A_5] :
      ( v1_funct_1(k2_funct_1(A_5))
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_62,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_140,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_143,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_140])).

tff(c_147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_72,c_143])).

tff(c_148,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_176,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_876,plain,(
    ! [A_88,B_89,C_90] :
      ( k2_relset_1(A_88,B_89,C_90) = k2_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_888,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_876])).

tff(c_893,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_888])).

tff(c_127,plain,(
    ! [A_47] :
      ( k1_relat_1(A_47) = k1_xboole_0
      | k2_relat_1(A_47) != k1_xboole_0
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_138,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_125,c_127])).

tff(c_150,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_894,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_893,c_150])).

tff(c_70,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_624,plain,(
    ! [A_74,B_75,C_76] :
      ( k1_relset_1(A_74,B_75,C_76) = k1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_640,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_624])).

tff(c_2185,plain,(
    ! [B_128,A_129,C_130] :
      ( k1_xboole_0 = B_128
      | k1_relset_1(A_129,B_128,C_130) = A_129
      | ~ v1_funct_2(C_130,A_129,B_128)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_129,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2206,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_2185])).

tff(c_2221,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_640,c_2206])).

tff(c_2222,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_894,c_2221])).

tff(c_16,plain,(
    ! [A_6] :
      ( k2_relat_1(k2_funct_1(A_6)) = k1_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14,plain,(
    ! [A_5] :
      ( v1_relat_1(k2_funct_1(A_5))
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_149,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_332,plain,(
    ! [A_63] :
      ( k2_relat_1(k2_funct_1(A_63)) = k1_relat_1(A_63)
      | ~ v2_funct_1(A_63)
      | ~ v1_funct_1(A_63)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_52,plain,(
    ! [A_30] :
      ( v1_funct_2(A_30,k1_relat_1(A_30),k2_relat_1(A_30))
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_6765,plain,(
    ! [A_177] :
      ( v1_funct_2(k2_funct_1(A_177),k1_relat_1(k2_funct_1(A_177)),k1_relat_1(A_177))
      | ~ v1_funct_1(k2_funct_1(A_177))
      | ~ v1_relat_1(k2_funct_1(A_177))
      | ~ v2_funct_1(A_177)
      | ~ v1_funct_1(A_177)
      | ~ v1_relat_1(A_177) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_52])).

tff(c_6771,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2222,c_6765])).

tff(c_6793,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_72,c_66,c_149,c_6771])).

tff(c_6968,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_6793])).

tff(c_6971,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_6968])).

tff(c_6975,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_72,c_6971])).

tff(c_6977,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_6793])).

tff(c_904,plain,(
    ! [A_91] :
      ( m1_subset_1(A_91,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_91),k2_relat_1(A_91))))
      | ~ v1_funct_1(A_91)
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_8558,plain,(
    ! [A_193] :
      ( m1_subset_1(k2_funct_1(A_193),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_193),k2_relat_1(k2_funct_1(A_193)))))
      | ~ v1_funct_1(k2_funct_1(A_193))
      | ~ v1_relat_1(k2_funct_1(A_193))
      | ~ v2_funct_1(A_193)
      | ~ v1_funct_1(A_193)
      | ~ v1_relat_1(A_193) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_904])).

tff(c_8594,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3')))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_893,c_8558])).

tff(c_8628,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_72,c_66,c_6977,c_149,c_8594])).

tff(c_8665,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3'))))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_8628])).

tff(c_8682,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_72,c_66,c_2222,c_8665])).

tff(c_8684,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_8682])).

tff(c_8685,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_8686,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_9694,plain,(
    ! [A_236,B_237,C_238] :
      ( k1_relset_1(A_236,B_237,C_238) = k1_relat_1(C_238)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_236,B_237))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_9712,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_8686,c_9694])).

tff(c_11888,plain,(
    ! [B_289,C_290,A_291] :
      ( k1_xboole_0 = B_289
      | v1_funct_2(C_290,A_291,B_289)
      | k1_relset_1(A_291,B_289,C_290) != A_291
      | ~ m1_subset_1(C_290,k1_zfmisc_1(k2_zfmisc_1(A_291,B_289))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_11906,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_8686,c_11888])).

tff(c_11924,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9712,c_11906])).

tff(c_11925,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_8685,c_11924])).

tff(c_11931,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_11925])).

tff(c_11934,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_11931])).

tff(c_11937,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_72,c_66,c_9550,c_11934])).

tff(c_11938,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_11925])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_11991,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11938,c_2])).

tff(c_11993,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_175,c_11991])).

tff(c_11995,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_98,plain,(
    ! [B_37,A_38] :
      ( ~ v1_xboole_0(B_37)
      | B_37 = A_38
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_101,plain,(
    ! [A_38] :
      ( k1_xboole_0 = A_38
      | ~ v1_xboole_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_2,c_98])).

tff(c_12009,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_11995,c_101])).

tff(c_11994,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_12002,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_11994,c_101])).

tff(c_12023,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12009,c_12002])).

tff(c_12032,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12023,c_64])).

tff(c_12030,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12023,c_125])).

tff(c_12035,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12023,c_72])).

tff(c_12034,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12023,c_66])).

tff(c_46,plain,(
    ! [A_28] : m1_subset_1(k6_partfun1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_12059,plain,(
    ! [A_297] :
      ( v1_xboole_0(k6_partfun1(A_297))
      | ~ v1_xboole_0(A_297) ) ),
    inference(resolution,[status(thm)],[c_46,c_166])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( ~ v1_xboole_0(B_3)
      | B_3 = A_2
      | ~ v1_xboole_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12010,plain,(
    ! [A_2] :
      ( A_2 = '#skF_1'
      | ~ v1_xboole_0(A_2) ) ),
    inference(resolution,[status(thm)],[c_11995,c_6])).

tff(c_12071,plain,(
    ! [A_298] :
      ( k6_partfun1(A_298) = '#skF_1'
      | ~ v1_xboole_0(A_298) ) ),
    inference(resolution,[status(thm)],[c_12059,c_12010])).

tff(c_12079,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_11995,c_12071])).

tff(c_48,plain,(
    ! [A_29] : k6_relat_1(A_29) = k6_partfun1(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_20,plain,(
    ! [A_7] : k2_funct_1(k6_relat_1(A_7)) = k6_relat_1(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_73,plain,(
    ! [A_7] : k2_funct_1(k6_partfun1(A_7)) = k6_partfun1(A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_20])).

tff(c_12091,plain,(
    k6_partfun1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_12079,c_73])).

tff(c_12100,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12079,c_12091])).

tff(c_12260,plain,(
    ! [A_307] :
      ( k1_relat_1(k2_funct_1(A_307)) = k2_relat_1(A_307)
      | ~ v2_funct_1(A_307)
      | ~ v1_funct_1(A_307)
      | ~ v1_relat_1(A_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12272,plain,
    ( k2_relat_1('#skF_1') = k1_relat_1('#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_12100,c_12260])).

tff(c_12279,plain,(
    k2_relat_1('#skF_1') = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12030,c_12035,c_12034,c_12272])).

tff(c_12031,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12023,c_68])).

tff(c_14000,plain,(
    ! [A_345,B_346,C_347] :
      ( k2_relset_1(A_345,B_346,C_347) = k2_relat_1(C_347)
      | ~ m1_subset_1(C_347,k1_zfmisc_1(k2_zfmisc_1(A_345,B_346))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_14015,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_1') = k2_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_12031,c_14000])).

tff(c_14027,plain,(
    k1_relat_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12032,c_12279,c_14015])).

tff(c_151,plain,(
    ! [A_48] :
      ( k2_relat_1(A_48) = k1_xboole_0
      | k1_relat_1(A_48) != k1_xboole_0
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_157,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_125,c_151])).

tff(c_164,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_157])).

tff(c_12011,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12002,c_164])).

tff(c_12045,plain,(
    k1_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12023,c_12023,c_12011])).

tff(c_14032,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14027,c_12045])).

tff(c_12033,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12023,c_70])).

tff(c_14103,plain,(
    ! [A_348,B_349,C_350] :
      ( k1_relset_1(A_348,B_349,C_350) = k1_relat_1(C_350)
      | ~ m1_subset_1(C_350,k1_zfmisc_1(k2_zfmisc_1(A_348,B_349))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_14118,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_12031,c_14103])).

tff(c_14130,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14027,c_14118])).

tff(c_40,plain,(
    ! [B_26,C_27] :
      ( k1_relset_1(k1_xboole_0,B_26,C_27) = k1_xboole_0
      | ~ v1_funct_2(C_27,k1_xboole_0,B_26)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_15582,plain,(
    ! [B_392,C_393] :
      ( k1_relset_1('#skF_1',B_392,C_393) = '#skF_1'
      | ~ v1_funct_2(C_393,'#skF_1',B_392)
      | ~ m1_subset_1(C_393,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_392))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12009,c_12009,c_12009,c_12009,c_40])).

tff(c_15588,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_1'
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_12031,c_15582])).

tff(c_15598,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12033,c_14130,c_15588])).

tff(c_15600,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14032,c_15598])).

tff(c_15602,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_21010,plain,(
    ! [A_561,B_562,C_563] :
      ( k2_relset_1(A_561,B_562,C_563) = k2_relat_1(C_563)
      | ~ m1_subset_1(C_563,k1_zfmisc_1(k2_zfmisc_1(A_561,B_562))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_21025,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_21010])).

tff(c_21032,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_15602,c_21025])).

tff(c_21061,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21032,c_2])).

tff(c_21063,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20646,c_21061])).

tff(c_21064,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_20645])).

tff(c_21071,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_21064,c_101])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_21089,plain,(
    ! [A_1] : r1_tarski('#skF_3',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21071,c_4])).

tff(c_21085,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21071,c_15602])).

tff(c_15601,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_21086,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21071,c_15601])).

tff(c_22721,plain,(
    ! [B_624,A_625] :
      ( v1_funct_2(B_624,k1_relat_1(B_624),A_625)
      | ~ r1_tarski(k2_relat_1(B_624),A_625)
      | ~ v1_funct_1(B_624)
      | ~ v1_relat_1(B_624) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_22733,plain,(
    ! [A_625] :
      ( v1_funct_2('#skF_3','#skF_3',A_625)
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_625)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21086,c_22721])).

tff(c_22739,plain,(
    ! [A_625] : v1_funct_2('#skF_3','#skF_3',A_625) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_72,c_21089,c_21085,c_22733])).

tff(c_21158,plain,(
    ! [A_570] :
      ( v1_xboole_0(k6_partfun1(A_570))
      | ~ v1_xboole_0(A_570) ) ),
    inference(resolution,[status(thm)],[c_46,c_20633])).

tff(c_21065,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_20645])).

tff(c_21078,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_21065,c_101])).

tff(c_21096,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21071,c_21078])).

tff(c_21079,plain,(
    ! [A_2] :
      ( A_2 = '#skF_2'
      | ~ v1_xboole_0(A_2) ) ),
    inference(resolution,[status(thm)],[c_21065,c_6])).

tff(c_21128,plain,(
    ! [A_2] :
      ( A_2 = '#skF_3'
      | ~ v1_xboole_0(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21096,c_21079])).

tff(c_21199,plain,(
    ! [A_572] :
      ( k6_partfun1(A_572) = '#skF_3'
      | ~ v1_xboole_0(A_572) ) ),
    inference(resolution,[status(thm)],[c_21158,c_21128])).

tff(c_21207,plain,(
    k6_partfun1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_21064,c_21199])).

tff(c_21219,plain,(
    k6_partfun1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_21207,c_73])).

tff(c_21228,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21207,c_21219])).

tff(c_15882,plain,(
    ! [A_413] :
      ( m1_subset_1(A_413,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_413),k2_relat_1(A_413))))
      | ~ v1_funct_1(A_413)
      | ~ v1_relat_1(A_413) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_15906,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k1_xboole_0)))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_15602,c_15882])).

tff(c_15917,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_72,c_15601,c_15906])).

tff(c_24,plain,(
    ! [C_14,A_11,B_12] :
      ( v1_xboole_0(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12)))
      | ~ v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_15925,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_15917,c_24])).

tff(c_15936,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_15925])).

tff(c_15951,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_15936,c_101])).

tff(c_15970,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15951,c_15602])).

tff(c_16005,plain,(
    ! [A_414,B_415,C_416] :
      ( k2_relset_1(A_414,B_415,C_416) = k2_relat_1(C_416)
      | ~ m1_subset_1(C_416,k1_zfmisc_1(k2_zfmisc_1(A_414,B_415))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_16014,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_16005])).

tff(c_16018,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_16014])).

tff(c_16051,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15970,c_16018])).

tff(c_15641,plain,(
    ! [C_397,B_398,A_399] :
      ( v1_xboole_0(C_397)
      | ~ m1_subset_1(C_397,k1_zfmisc_1(k2_zfmisc_1(B_398,A_399)))
      | ~ v1_xboole_0(A_399) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_15649,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_15641])).

tff(c_15650,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_15649])).

tff(c_16067,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16051,c_15650])).

tff(c_16074,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15936,c_16067])).

tff(c_16075,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_15649])).

tff(c_16082,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_16075,c_101])).

tff(c_16098,plain,(
    ! [A_1] : r1_tarski('#skF_3',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16082,c_4])).

tff(c_16094,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16082,c_15602])).

tff(c_16095,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16082,c_15601])).

tff(c_20331,plain,(
    ! [B_521,A_522] :
      ( m1_subset_1(B_521,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_521),A_522)))
      | ~ r1_tarski(k2_relat_1(B_521),A_522)
      | ~ v1_funct_1(B_521)
      | ~ v1_relat_1(B_521) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_20369,plain,(
    ! [A_522] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_522)))
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_522)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16095,c_20331])).

tff(c_20386,plain,(
    ! [A_522] : m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_522))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_72,c_16098,c_16094,c_20369])).

tff(c_16148,plain,(
    ! [A_423] :
      ( v1_xboole_0(k6_partfun1(A_423))
      | ~ v1_xboole_0(A_423) ) ),
    inference(resolution,[status(thm)],[c_46,c_15641])).

tff(c_16076,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_15649])).

tff(c_16089,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_16076,c_101])).

tff(c_16106,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16082,c_16089])).

tff(c_16090,plain,(
    ! [A_2] :
      ( A_2 = '#skF_2'
      | ~ v1_xboole_0(A_2) ) ),
    inference(resolution,[status(thm)],[c_16076,c_6])).

tff(c_16136,plain,(
    ! [A_2] :
      ( A_2 = '#skF_3'
      | ~ v1_xboole_0(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16106,c_16090])).

tff(c_16176,plain,(
    ! [A_424] :
      ( k6_partfun1(A_424) = '#skF_3'
      | ~ v1_xboole_0(A_424) ) ),
    inference(resolution,[status(thm)],[c_16148,c_16136])).

tff(c_16184,plain,(
    k6_partfun1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_16075,c_16176])).

tff(c_16196,plain,(
    k6_partfun1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16184,c_73])).

tff(c_16205,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16184,c_16196])).

tff(c_15626,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_16108,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16106,c_15626])).

tff(c_16312,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16205,c_16108])).

tff(c_20390,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20386,c_16312])).

tff(c_20391,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_21099,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21096,c_20391])).

tff(c_21231,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21228,c_21099])).

tff(c_22743,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22739,c_21231])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:02:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.99/3.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.03/3.70  
% 11.03/3.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.03/3.70  %$ v1_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 11.03/3.70  
% 11.03/3.70  %Foreground sorts:
% 11.03/3.70  
% 11.03/3.70  
% 11.03/3.70  %Background operators:
% 11.03/3.70  
% 11.03/3.70  
% 11.03/3.70  %Foreground operators:
% 11.03/3.70  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.03/3.70  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.03/3.70  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 11.03/3.70  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 11.03/3.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.03/3.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.03/3.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.03/3.70  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.03/3.70  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.03/3.70  tff('#skF_2', type, '#skF_2': $i).
% 11.03/3.70  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 11.03/3.70  tff('#skF_3', type, '#skF_3': $i).
% 11.03/3.70  tff('#skF_1', type, '#skF_1': $i).
% 11.03/3.70  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.03/3.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.03/3.70  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 11.03/3.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.03/3.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.03/3.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.03/3.70  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 11.03/3.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.03/3.70  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.03/3.70  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.03/3.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.03/3.70  
% 11.19/3.73  tff(f_151, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 11.19/3.73  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.19/3.73  tff(f_80, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 11.19/3.73  tff(f_73, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 11.19/3.73  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 11.19/3.73  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 11.19/3.73  tff(f_50, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 11.19/3.73  tff(f_42, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 11.19/3.73  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.19/3.73  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 11.19/3.73  tff(f_122, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 11.19/3.73  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 11.19/3.73  tff(f_36, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 11.19/3.73  tff(f_110, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 11.19/3.73  tff(f_112, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 11.19/3.73  tff(f_62, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_1)).
% 11.19/3.73  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.19/3.73  tff(f_134, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 11.19/3.73  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 11.19/3.73  tff(c_117, plain, (![C_43, A_44, B_45]: (v1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 11.19/3.73  tff(c_125, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_117])).
% 11.19/3.73  tff(c_72, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 11.19/3.73  tff(c_20633, plain, (![C_536, B_537, A_538]: (v1_xboole_0(C_536) | ~m1_subset_1(C_536, k1_zfmisc_1(k2_zfmisc_1(B_537, A_538))) | ~v1_xboole_0(A_538))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.19/3.73  tff(c_20645, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_20633])).
% 11.19/3.73  tff(c_20646, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_20645])).
% 11.19/3.73  tff(c_64, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_151])).
% 11.19/3.73  tff(c_166, plain, (![C_49, A_50, B_51]: (v1_xboole_0(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))) | ~v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.19/3.73  tff(c_174, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_68, c_166])).
% 11.19/3.73  tff(c_175, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_174])).
% 11.19/3.73  tff(c_66, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 11.19/3.73  tff(c_9529, plain, (![A_228, B_229, C_230]: (k2_relset_1(A_228, B_229, C_230)=k2_relat_1(C_230) | ~m1_subset_1(C_230, k1_zfmisc_1(k2_zfmisc_1(A_228, B_229))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.19/3.73  tff(c_9544, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_9529])).
% 11.19/3.73  tff(c_9550, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_9544])).
% 11.19/3.73  tff(c_18, plain, (![A_6]: (k1_relat_1(k2_funct_1(A_6))=k2_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.19/3.73  tff(c_12, plain, (![A_5]: (v1_funct_1(k2_funct_1(A_5)) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.19/3.73  tff(c_62, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 11.19/3.73  tff(c_140, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_62])).
% 11.19/3.73  tff(c_143, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_140])).
% 11.19/3.73  tff(c_147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_72, c_143])).
% 11.19/3.73  tff(c_148, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_62])).
% 11.19/3.73  tff(c_176, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_148])).
% 11.19/3.73  tff(c_876, plain, (![A_88, B_89, C_90]: (k2_relset_1(A_88, B_89, C_90)=k2_relat_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.19/3.73  tff(c_888, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_876])).
% 11.19/3.73  tff(c_893, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_888])).
% 11.19/3.73  tff(c_127, plain, (![A_47]: (k1_relat_1(A_47)=k1_xboole_0 | k2_relat_1(A_47)!=k1_xboole_0 | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.19/3.73  tff(c_138, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_125, c_127])).
% 11.19/3.73  tff(c_150, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_138])).
% 11.19/3.73  tff(c_894, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_893, c_150])).
% 11.19/3.73  tff(c_70, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 11.19/3.73  tff(c_624, plain, (![A_74, B_75, C_76]: (k1_relset_1(A_74, B_75, C_76)=k1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.19/3.73  tff(c_640, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_624])).
% 11.19/3.73  tff(c_2185, plain, (![B_128, A_129, C_130]: (k1_xboole_0=B_128 | k1_relset_1(A_129, B_128, C_130)=A_129 | ~v1_funct_2(C_130, A_129, B_128) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_129, B_128))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.19/3.73  tff(c_2206, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_2185])).
% 11.19/3.73  tff(c_2221, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_640, c_2206])).
% 11.19/3.73  tff(c_2222, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_894, c_2221])).
% 11.19/3.73  tff(c_16, plain, (![A_6]: (k2_relat_1(k2_funct_1(A_6))=k1_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.19/3.73  tff(c_14, plain, (![A_5]: (v1_relat_1(k2_funct_1(A_5)) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.19/3.73  tff(c_149, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_62])).
% 11.19/3.73  tff(c_332, plain, (![A_63]: (k2_relat_1(k2_funct_1(A_63))=k1_relat_1(A_63) | ~v2_funct_1(A_63) | ~v1_funct_1(A_63) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.19/3.73  tff(c_52, plain, (![A_30]: (v1_funct_2(A_30, k1_relat_1(A_30), k2_relat_1(A_30)) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_122])).
% 11.19/3.73  tff(c_6765, plain, (![A_177]: (v1_funct_2(k2_funct_1(A_177), k1_relat_1(k2_funct_1(A_177)), k1_relat_1(A_177)) | ~v1_funct_1(k2_funct_1(A_177)) | ~v1_relat_1(k2_funct_1(A_177)) | ~v2_funct_1(A_177) | ~v1_funct_1(A_177) | ~v1_relat_1(A_177))), inference(superposition, [status(thm), theory('equality')], [c_332, c_52])).
% 11.19/3.73  tff(c_6771, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2222, c_6765])).
% 11.19/3.73  tff(c_6793, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_72, c_66, c_149, c_6771])).
% 11.19/3.73  tff(c_6968, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_6793])).
% 11.19/3.73  tff(c_6971, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_6968])).
% 11.19/3.73  tff(c_6975, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_72, c_6971])).
% 11.19/3.73  tff(c_6977, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_6793])).
% 11.19/3.73  tff(c_904, plain, (![A_91]: (m1_subset_1(A_91, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_91), k2_relat_1(A_91)))) | ~v1_funct_1(A_91) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_122])).
% 11.19/3.73  tff(c_8558, plain, (![A_193]: (m1_subset_1(k2_funct_1(A_193), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_193), k2_relat_1(k2_funct_1(A_193))))) | ~v1_funct_1(k2_funct_1(A_193)) | ~v1_relat_1(k2_funct_1(A_193)) | ~v2_funct_1(A_193) | ~v1_funct_1(A_193) | ~v1_relat_1(A_193))), inference(superposition, [status(thm), theory('equality')], [c_18, c_904])).
% 11.19/3.73  tff(c_8594, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3'))))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_893, c_8558])).
% 11.19/3.73  tff(c_8628, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_72, c_66, c_6977, c_149, c_8594])).
% 11.19/3.73  tff(c_8665, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3')))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_8628])).
% 11.19/3.73  tff(c_8682, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_72, c_66, c_2222, c_8665])).
% 11.19/3.73  tff(c_8684, plain, $false, inference(negUnitSimplification, [status(thm)], [c_176, c_8682])).
% 11.19/3.73  tff(c_8685, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_148])).
% 11.19/3.73  tff(c_8686, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_148])).
% 11.19/3.73  tff(c_9694, plain, (![A_236, B_237, C_238]: (k1_relset_1(A_236, B_237, C_238)=k1_relat_1(C_238) | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_236, B_237))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.19/3.73  tff(c_9712, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_8686, c_9694])).
% 11.19/3.73  tff(c_11888, plain, (![B_289, C_290, A_291]: (k1_xboole_0=B_289 | v1_funct_2(C_290, A_291, B_289) | k1_relset_1(A_291, B_289, C_290)!=A_291 | ~m1_subset_1(C_290, k1_zfmisc_1(k2_zfmisc_1(A_291, B_289))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.19/3.73  tff(c_11906, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_8686, c_11888])).
% 11.19/3.73  tff(c_11924, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_9712, c_11906])).
% 11.19/3.73  tff(c_11925, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_8685, c_11924])).
% 11.19/3.73  tff(c_11931, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_11925])).
% 11.19/3.73  tff(c_11934, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18, c_11931])).
% 11.19/3.73  tff(c_11937, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_72, c_66, c_9550, c_11934])).
% 11.19/3.73  tff(c_11938, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_11925])).
% 11.19/3.73  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 11.19/3.73  tff(c_11991, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11938, c_2])).
% 11.19/3.73  tff(c_11993, plain, $false, inference(negUnitSimplification, [status(thm)], [c_175, c_11991])).
% 11.19/3.73  tff(c_11995, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_174])).
% 11.19/3.73  tff(c_98, plain, (![B_37, A_38]: (~v1_xboole_0(B_37) | B_37=A_38 | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.19/3.73  tff(c_101, plain, (![A_38]: (k1_xboole_0=A_38 | ~v1_xboole_0(A_38))), inference(resolution, [status(thm)], [c_2, c_98])).
% 11.19/3.73  tff(c_12009, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_11995, c_101])).
% 11.19/3.73  tff(c_11994, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_174])).
% 11.19/3.73  tff(c_12002, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_11994, c_101])).
% 11.19/3.73  tff(c_12023, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12009, c_12002])).
% 11.19/3.73  tff(c_12032, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12023, c_64])).
% 11.19/3.73  tff(c_12030, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12023, c_125])).
% 11.19/3.73  tff(c_12035, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12023, c_72])).
% 11.19/3.73  tff(c_12034, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12023, c_66])).
% 11.19/3.73  tff(c_46, plain, (![A_28]: (m1_subset_1(k6_partfun1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.19/3.73  tff(c_12059, plain, (![A_297]: (v1_xboole_0(k6_partfun1(A_297)) | ~v1_xboole_0(A_297))), inference(resolution, [status(thm)], [c_46, c_166])).
% 11.19/3.73  tff(c_6, plain, (![B_3, A_2]: (~v1_xboole_0(B_3) | B_3=A_2 | ~v1_xboole_0(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.19/3.73  tff(c_12010, plain, (![A_2]: (A_2='#skF_1' | ~v1_xboole_0(A_2))), inference(resolution, [status(thm)], [c_11995, c_6])).
% 11.19/3.73  tff(c_12071, plain, (![A_298]: (k6_partfun1(A_298)='#skF_1' | ~v1_xboole_0(A_298))), inference(resolution, [status(thm)], [c_12059, c_12010])).
% 11.19/3.73  tff(c_12079, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_11995, c_12071])).
% 11.19/3.73  tff(c_48, plain, (![A_29]: (k6_relat_1(A_29)=k6_partfun1(A_29))), inference(cnfTransformation, [status(thm)], [f_112])).
% 11.19/3.73  tff(c_20, plain, (![A_7]: (k2_funct_1(k6_relat_1(A_7))=k6_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.19/3.73  tff(c_73, plain, (![A_7]: (k2_funct_1(k6_partfun1(A_7))=k6_partfun1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_20])).
% 11.19/3.73  tff(c_12091, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_12079, c_73])).
% 11.19/3.73  tff(c_12100, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12079, c_12091])).
% 11.19/3.73  tff(c_12260, plain, (![A_307]: (k1_relat_1(k2_funct_1(A_307))=k2_relat_1(A_307) | ~v2_funct_1(A_307) | ~v1_funct_1(A_307) | ~v1_relat_1(A_307))), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.19/3.73  tff(c_12272, plain, (k2_relat_1('#skF_1')=k1_relat_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_12100, c_12260])).
% 11.19/3.73  tff(c_12279, plain, (k2_relat_1('#skF_1')=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12030, c_12035, c_12034, c_12272])).
% 11.19/3.73  tff(c_12031, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_12023, c_68])).
% 11.19/3.73  tff(c_14000, plain, (![A_345, B_346, C_347]: (k2_relset_1(A_345, B_346, C_347)=k2_relat_1(C_347) | ~m1_subset_1(C_347, k1_zfmisc_1(k2_zfmisc_1(A_345, B_346))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.19/3.73  tff(c_14015, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_1')=k2_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_12031, c_14000])).
% 11.19/3.73  tff(c_14027, plain, (k1_relat_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12032, c_12279, c_14015])).
% 11.19/3.73  tff(c_151, plain, (![A_48]: (k2_relat_1(A_48)=k1_xboole_0 | k1_relat_1(A_48)!=k1_xboole_0 | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.19/3.73  tff(c_157, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_125, c_151])).
% 11.19/3.73  tff(c_164, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_150, c_157])).
% 11.19/3.73  tff(c_12011, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12002, c_164])).
% 11.19/3.73  tff(c_12045, plain, (k1_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12023, c_12023, c_12011])).
% 11.19/3.73  tff(c_14032, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14027, c_12045])).
% 11.19/3.73  tff(c_12033, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12023, c_70])).
% 11.19/3.73  tff(c_14103, plain, (![A_348, B_349, C_350]: (k1_relset_1(A_348, B_349, C_350)=k1_relat_1(C_350) | ~m1_subset_1(C_350, k1_zfmisc_1(k2_zfmisc_1(A_348, B_349))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.19/3.73  tff(c_14118, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_1')=k1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_12031, c_14103])).
% 11.19/3.73  tff(c_14130, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14027, c_14118])).
% 11.19/3.73  tff(c_40, plain, (![B_26, C_27]: (k1_relset_1(k1_xboole_0, B_26, C_27)=k1_xboole_0 | ~v1_funct_2(C_27, k1_xboole_0, B_26) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_26))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.19/3.73  tff(c_15582, plain, (![B_392, C_393]: (k1_relset_1('#skF_1', B_392, C_393)='#skF_1' | ~v1_funct_2(C_393, '#skF_1', B_392) | ~m1_subset_1(C_393, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_392))))), inference(demodulation, [status(thm), theory('equality')], [c_12009, c_12009, c_12009, c_12009, c_40])).
% 11.19/3.73  tff(c_15588, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_1' | ~v1_funct_2('#skF_1', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_12031, c_15582])).
% 11.19/3.73  tff(c_15598, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12033, c_14130, c_15588])).
% 11.19/3.73  tff(c_15600, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14032, c_15598])).
% 11.19/3.73  tff(c_15602, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_138])).
% 11.19/3.73  tff(c_21010, plain, (![A_561, B_562, C_563]: (k2_relset_1(A_561, B_562, C_563)=k2_relat_1(C_563) | ~m1_subset_1(C_563, k1_zfmisc_1(k2_zfmisc_1(A_561, B_562))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.19/3.73  tff(c_21025, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_21010])).
% 11.19/3.73  tff(c_21032, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_15602, c_21025])).
% 11.19/3.73  tff(c_21061, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_21032, c_2])).
% 11.19/3.73  tff(c_21063, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20646, c_21061])).
% 11.19/3.73  tff(c_21064, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_20645])).
% 11.19/3.73  tff(c_21071, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_21064, c_101])).
% 11.19/3.73  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 11.19/3.73  tff(c_21089, plain, (![A_1]: (r1_tarski('#skF_3', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_21071, c_4])).
% 11.19/3.73  tff(c_21085, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_21071, c_15602])).
% 11.19/3.73  tff(c_15601, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_138])).
% 11.19/3.73  tff(c_21086, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_21071, c_15601])).
% 11.19/3.73  tff(c_22721, plain, (![B_624, A_625]: (v1_funct_2(B_624, k1_relat_1(B_624), A_625) | ~r1_tarski(k2_relat_1(B_624), A_625) | ~v1_funct_1(B_624) | ~v1_relat_1(B_624))), inference(cnfTransformation, [status(thm)], [f_134])).
% 11.19/3.73  tff(c_22733, plain, (![A_625]: (v1_funct_2('#skF_3', '#skF_3', A_625) | ~r1_tarski(k2_relat_1('#skF_3'), A_625) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_21086, c_22721])).
% 11.19/3.73  tff(c_22739, plain, (![A_625]: (v1_funct_2('#skF_3', '#skF_3', A_625))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_72, c_21089, c_21085, c_22733])).
% 11.19/3.73  tff(c_21158, plain, (![A_570]: (v1_xboole_0(k6_partfun1(A_570)) | ~v1_xboole_0(A_570))), inference(resolution, [status(thm)], [c_46, c_20633])).
% 11.19/3.73  tff(c_21065, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_20645])).
% 11.19/3.73  tff(c_21078, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_21065, c_101])).
% 11.19/3.73  tff(c_21096, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_21071, c_21078])).
% 11.19/3.73  tff(c_21079, plain, (![A_2]: (A_2='#skF_2' | ~v1_xboole_0(A_2))), inference(resolution, [status(thm)], [c_21065, c_6])).
% 11.19/3.73  tff(c_21128, plain, (![A_2]: (A_2='#skF_3' | ~v1_xboole_0(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_21096, c_21079])).
% 11.19/3.73  tff(c_21199, plain, (![A_572]: (k6_partfun1(A_572)='#skF_3' | ~v1_xboole_0(A_572))), inference(resolution, [status(thm)], [c_21158, c_21128])).
% 11.19/3.73  tff(c_21207, plain, (k6_partfun1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_21064, c_21199])).
% 11.19/3.73  tff(c_21219, plain, (k6_partfun1('#skF_3')=k2_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_21207, c_73])).
% 11.19/3.73  tff(c_21228, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_21207, c_21219])).
% 11.19/3.73  tff(c_15882, plain, (![A_413]: (m1_subset_1(A_413, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_413), k2_relat_1(A_413)))) | ~v1_funct_1(A_413) | ~v1_relat_1(A_413))), inference(cnfTransformation, [status(thm)], [f_122])).
% 11.19/3.73  tff(c_15906, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k1_xboole_0))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_15602, c_15882])).
% 11.19/3.73  tff(c_15917, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_72, c_15601, c_15906])).
% 11.19/3.73  tff(c_24, plain, (![C_14, A_11, B_12]: (v1_xboole_0(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))) | ~v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.19/3.73  tff(c_15925, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_15917, c_24])).
% 11.19/3.73  tff(c_15936, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_15925])).
% 11.19/3.73  tff(c_15951, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_15936, c_101])).
% 11.19/3.73  tff(c_15970, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_15951, c_15602])).
% 11.19/3.73  tff(c_16005, plain, (![A_414, B_415, C_416]: (k2_relset_1(A_414, B_415, C_416)=k2_relat_1(C_416) | ~m1_subset_1(C_416, k1_zfmisc_1(k2_zfmisc_1(A_414, B_415))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.19/3.73  tff(c_16014, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_16005])).
% 11.19/3.73  tff(c_16018, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_16014])).
% 11.19/3.73  tff(c_16051, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_15970, c_16018])).
% 11.19/3.73  tff(c_15641, plain, (![C_397, B_398, A_399]: (v1_xboole_0(C_397) | ~m1_subset_1(C_397, k1_zfmisc_1(k2_zfmisc_1(B_398, A_399))) | ~v1_xboole_0(A_399))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.19/3.73  tff(c_15649, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_15641])).
% 11.19/3.73  tff(c_15650, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_15649])).
% 11.19/3.73  tff(c_16067, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16051, c_15650])).
% 11.19/3.73  tff(c_16074, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15936, c_16067])).
% 11.19/3.73  tff(c_16075, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_15649])).
% 11.19/3.73  tff(c_16082, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_16075, c_101])).
% 11.19/3.73  tff(c_16098, plain, (![A_1]: (r1_tarski('#skF_3', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_16082, c_4])).
% 11.19/3.73  tff(c_16094, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16082, c_15602])).
% 11.19/3.73  tff(c_16095, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16082, c_15601])).
% 11.19/3.73  tff(c_20331, plain, (![B_521, A_522]: (m1_subset_1(B_521, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_521), A_522))) | ~r1_tarski(k2_relat_1(B_521), A_522) | ~v1_funct_1(B_521) | ~v1_relat_1(B_521))), inference(cnfTransformation, [status(thm)], [f_134])).
% 11.19/3.73  tff(c_20369, plain, (![A_522]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_522))) | ~r1_tarski(k2_relat_1('#skF_3'), A_522) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_16095, c_20331])).
% 11.19/3.73  tff(c_20386, plain, (![A_522]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_522))))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_72, c_16098, c_16094, c_20369])).
% 11.19/3.73  tff(c_16148, plain, (![A_423]: (v1_xboole_0(k6_partfun1(A_423)) | ~v1_xboole_0(A_423))), inference(resolution, [status(thm)], [c_46, c_15641])).
% 11.19/3.73  tff(c_16076, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_15649])).
% 11.19/3.73  tff(c_16089, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_16076, c_101])).
% 11.19/3.73  tff(c_16106, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16082, c_16089])).
% 11.19/3.73  tff(c_16090, plain, (![A_2]: (A_2='#skF_2' | ~v1_xboole_0(A_2))), inference(resolution, [status(thm)], [c_16076, c_6])).
% 11.19/3.73  tff(c_16136, plain, (![A_2]: (A_2='#skF_3' | ~v1_xboole_0(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_16106, c_16090])).
% 11.19/3.73  tff(c_16176, plain, (![A_424]: (k6_partfun1(A_424)='#skF_3' | ~v1_xboole_0(A_424))), inference(resolution, [status(thm)], [c_16148, c_16136])).
% 11.19/3.73  tff(c_16184, plain, (k6_partfun1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_16075, c_16176])).
% 11.19/3.73  tff(c_16196, plain, (k6_partfun1('#skF_3')=k2_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16184, c_73])).
% 11.19/3.73  tff(c_16205, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16184, c_16196])).
% 11.19/3.73  tff(c_15626, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_148])).
% 11.19/3.73  tff(c_16108, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_16106, c_15626])).
% 11.19/3.73  tff(c_16312, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_16205, c_16108])).
% 11.19/3.73  tff(c_20390, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20386, c_16312])).
% 11.19/3.73  tff(c_20391, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_148])).
% 11.19/3.73  tff(c_21099, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_21096, c_20391])).
% 11.19/3.73  tff(c_21231, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_21228, c_21099])).
% 11.19/3.73  tff(c_22743, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22739, c_21231])).
% 11.19/3.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.19/3.73  
% 11.19/3.73  Inference rules
% 11.19/3.73  ----------------------
% 11.19/3.73  #Ref     : 0
% 11.19/3.73  #Sup     : 6200
% 11.19/3.73  #Fact    : 0
% 11.19/3.73  #Define  : 0
% 11.19/3.73  #Split   : 47
% 11.19/3.73  #Chain   : 0
% 11.19/3.73  #Close   : 0
% 11.19/3.73  
% 11.19/3.73  Ordering : KBO
% 11.19/3.73  
% 11.19/3.73  Simplification rules
% 11.19/3.73  ----------------------
% 11.19/3.73  #Subsume      : 1971
% 11.19/3.73  #Demod        : 3983
% 11.19/3.73  #Tautology    : 1592
% 11.19/3.73  #SimpNegUnit  : 75
% 11.19/3.73  #BackRed      : 184
% 11.19/3.73  
% 11.19/3.73  #Partial instantiations: 0
% 11.19/3.73  #Strategies tried      : 1
% 11.19/3.73  
% 11.19/3.73  Timing (in seconds)
% 11.19/3.73  ----------------------
% 11.27/3.73  Preprocessing        : 0.35
% 11.27/3.73  Parsing              : 0.19
% 11.27/3.73  CNF conversion       : 0.02
% 11.27/3.73  Main loop            : 2.58
% 11.27/3.73  Inferencing          : 0.70
% 11.27/3.73  Reduction            : 0.86
% 11.27/3.73  Demodulation         : 0.63
% 11.27/3.73  BG Simplification    : 0.10
% 11.27/3.73  Subsumption          : 0.75
% 11.27/3.73  Abstraction          : 0.12
% 11.27/3.73  MUC search           : 0.00
% 11.27/3.73  Cooper               : 0.00
% 11.27/3.73  Total                : 3.00
% 11.27/3.73  Index Insertion      : 0.00
% 11.27/3.73  Index Deletion       : 0.00
% 11.27/3.73  Index Matching       : 0.00
% 11.27/3.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
