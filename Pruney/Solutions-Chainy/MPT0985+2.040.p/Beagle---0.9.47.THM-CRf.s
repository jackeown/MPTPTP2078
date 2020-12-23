%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:32 EST 2020

% Result     : Theorem 7.45s
% Output     : CNFRefutation 7.76s
% Verified   : 
% Statistics : Number of formulae       :  197 ( 766 expanded)
%              Number of leaves         :   48 ( 264 expanded)
%              Depth                    :   15
%              Number of atoms          :  332 (2056 expanded)
%              Number of equality atoms :  105 ( 420 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_179,negated_conjecture,(
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

tff(f_103,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_92,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_146,axiom,(
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

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_162,axiom,(
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

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_150,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_152,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_58,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_78,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_267,plain,(
    ! [C_78,B_79,A_80] :
      ( v1_xboole_0(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(B_79,A_80)))
      | ~ v1_xboole_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_285,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_267])).

tff(c_290,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_285])).

tff(c_82,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_24,plain,(
    ! [A_13] :
      ( v1_funct_1(k2_funct_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_72,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_157,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_160,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_157])).

tff(c_163,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_160])).

tff(c_165,plain,(
    ! [C_56,A_57,B_58] :
      ( v1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_171,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_165])).

tff(c_184,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_163,c_171])).

tff(c_185,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_217,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_185])).

tff(c_218,plain,(
    ! [C_63,A_64,B_65] :
      ( v1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_234,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_218])).

tff(c_76,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_74,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_519,plain,(
    ! [A_102,B_103,C_104] :
      ( k2_relset_1(A_102,B_103,C_104) = k2_relat_1(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_528,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_519])).

tff(c_542,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_528])).

tff(c_32,plain,(
    ! [A_16] :
      ( k1_relat_1(k2_funct_1(A_16)) = k2_relat_1(A_16)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_26,plain,(
    ! [A_13] :
      ( v1_relat_1(k2_funct_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_80,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_692,plain,(
    ! [A_118,B_119,C_120] :
      ( k1_relset_1(A_118,B_119,C_120) = k1_relat_1(C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_718,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_692])).

tff(c_1278,plain,(
    ! [B_153,A_154,C_155] :
      ( k1_xboole_0 = B_153
      | k1_relset_1(A_154,B_153,C_155) = A_154
      | ~ v1_funct_2(C_155,A_154,B_153)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_154,B_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1290,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_1278])).

tff(c_1309,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_718,c_1290])).

tff(c_1313,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1309])).

tff(c_399,plain,(
    ! [A_90] :
      ( k2_relat_1(k2_funct_1(A_90)) = k1_relat_1(A_90)
      | ~ v2_funct_1(A_90)
      | ~ v1_funct_1(A_90)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_18,plain,(
    ! [A_10] :
      ( k10_relat_1(A_10,k2_relat_1(A_10)) = k1_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4103,plain,(
    ! [A_205] :
      ( k10_relat_1(k2_funct_1(A_205),k1_relat_1(A_205)) = k1_relat_1(k2_funct_1(A_205))
      | ~ v1_relat_1(k2_funct_1(A_205))
      | ~ v2_funct_1(A_205)
      | ~ v1_funct_1(A_205)
      | ~ v1_relat_1(A_205) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_18])).

tff(c_4118,plain,
    ( k10_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1313,c_4103])).

tff(c_4132,plain,
    ( k10_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_82,c_76,c_4118])).

tff(c_4135,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_4132])).

tff(c_4138,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_4135])).

tff(c_4142,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_82,c_4138])).

tff(c_4144,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_4132])).

tff(c_186,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_556,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_542,c_18])).

tff(c_566,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_556])).

tff(c_1320,plain,(
    k10_relat_1('#skF_3','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1313,c_566])).

tff(c_373,plain,(
    ! [A_88] :
      ( k1_relat_1(k2_funct_1(A_88)) = k2_relat_1(A_88)
      | ~ v2_funct_1(A_88)
      | ~ v1_funct_1(A_88)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_16,plain,(
    ! [A_9] :
      ( k9_relat_1(A_9,k1_relat_1(A_9)) = k2_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_5161,plain,(
    ! [A_215] :
      ( k9_relat_1(k2_funct_1(A_215),k2_relat_1(A_215)) = k2_relat_1(k2_funct_1(A_215))
      | ~ v1_relat_1(k2_funct_1(A_215))
      | ~ v2_funct_1(A_215)
      | ~ v1_funct_1(A_215)
      | ~ v1_relat_1(A_215) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_16])).

tff(c_5186,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_542,c_5161])).

tff(c_5199,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_82,c_76,c_4144,c_5186])).

tff(c_28,plain,(
    ! [B_15,A_14] :
      ( k9_relat_1(k2_funct_1(B_15),A_14) = k10_relat_1(B_15,A_14)
      | ~ v2_funct_1(B_15)
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_5203,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5199,c_28])).

tff(c_5210,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_82,c_76,c_1320,c_5203])).

tff(c_66,plain,(
    ! [A_42] :
      ( m1_subset_1(A_42,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_42),k2_relat_1(A_42))))
      | ~ v1_funct_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_5233,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5210,c_66])).

tff(c_5259,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4144,c_186,c_5233])).

tff(c_5330,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_5259])).

tff(c_5348,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_82,c_76,c_542,c_5330])).

tff(c_5350,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_217,c_5348])).

tff(c_5351,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1309])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_5390,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5351,c_2])).

tff(c_5392,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_290,c_5390])).

tff(c_5393,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_285])).

tff(c_135,plain,(
    ! [B_49,A_50] :
      ( ~ v1_xboole_0(B_49)
      | B_49 = A_50
      | ~ v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_138,plain,(
    ! [A_50] :
      ( k1_xboole_0 = A_50
      | ~ v1_xboole_0(A_50) ) ),
    inference(resolution,[status(thm)],[c_2,c_135])).

tff(c_5400,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_5393,c_138])).

tff(c_12,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_5419,plain,(
    ! [A_5] : m1_subset_1('#skF_3',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5400,c_12])).

tff(c_62,plain,(
    ! [A_40] : m1_subset_1(k6_partfun1(A_40),k1_zfmisc_1(k2_zfmisc_1(A_40,A_40))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_5519,plain,(
    ! [A_221] :
      ( v1_xboole_0(k6_partfun1(A_221))
      | ~ v1_xboole_0(A_221) ) ),
    inference(resolution,[status(thm)],[c_62,c_267])).

tff(c_5416,plain,(
    ! [A_50] :
      ( A_50 = '#skF_3'
      | ~ v1_xboole_0(A_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5400,c_138])).

tff(c_5530,plain,(
    ! [A_222] :
      ( k6_partfun1(A_222) = '#skF_3'
      | ~ v1_xboole_0(A_222) ) ),
    inference(resolution,[status(thm)],[c_5519,c_5416])).

tff(c_5538,plain,(
    k6_partfun1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_5393,c_5530])).

tff(c_5503,plain,(
    ! [A_220] :
      ( k4_relat_1(A_220) = k2_funct_1(A_220)
      | ~ v2_funct_1(A_220)
      | ~ v1_funct_1(A_220)
      | ~ v1_relat_1(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_5506,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_5503])).

tff(c_5509,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_82,c_5506])).

tff(c_64,plain,(
    ! [A_41] : k6_relat_1(A_41) = k6_partfun1(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_20,plain,(
    ! [A_11] : k4_relat_1(k6_relat_1(A_11)) = k6_relat_1(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_83,plain,(
    ! [A_11] : k4_relat_1(k6_partfun1(A_11)) = k6_partfun1(A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_64,c_20])).

tff(c_5554,plain,(
    k6_partfun1('#skF_3') = k4_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5538,c_83])).

tff(c_5565,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5538,c_5509,c_5554])).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_5418,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_3',B_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5400,c_5400,c_10])).

tff(c_5394,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_285])).

tff(c_5407,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_5394,c_138])).

tff(c_5427,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5400,c_5407])).

tff(c_5430,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5427,c_217])).

tff(c_5740,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5419,c_5565,c_5418,c_5430])).

tff(c_5742,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_5799,plain,(
    ! [C_250,B_251,A_252] :
      ( v1_xboole_0(C_250)
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(B_251,A_252)))
      | ~ v1_xboole_0(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_5819,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_5742,c_5799])).

tff(c_5827,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_5819])).

tff(c_5743,plain,(
    ! [C_236,A_237,B_238] :
      ( v1_relat_1(C_236)
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_5763,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_5743])).

tff(c_6515,plain,(
    ! [A_292,B_293,C_294] :
      ( k2_relset_1(A_292,B_293,C_294) = k2_relat_1(C_294)
      | ~ m1_subset_1(C_294,k1_zfmisc_1(k2_zfmisc_1(A_292,B_293))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_6524,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_6515])).

tff(c_6538,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_6524])).

tff(c_5741,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_6310,plain,(
    ! [A_285,B_286,C_287] :
      ( k1_relset_1(A_285,B_286,C_287) = k1_relat_1(C_287)
      | ~ m1_subset_1(C_287,k1_zfmisc_1(k2_zfmisc_1(A_285,B_286))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_6330,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_5742,c_6310])).

tff(c_7221,plain,(
    ! [B_331,C_332,A_333] :
      ( k1_xboole_0 = B_331
      | v1_funct_2(C_332,A_333,B_331)
      | k1_relset_1(A_333,B_331,C_332) != A_333
      | ~ m1_subset_1(C_332,k1_zfmisc_1(k2_zfmisc_1(A_333,B_331))) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_7227,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_5742,c_7221])).

tff(c_7246,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6330,c_7227])).

tff(c_7247,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_5741,c_7246])).

tff(c_7256,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_7247])).

tff(c_7259,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_7256])).

tff(c_7262,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5763,c_82,c_76,c_6538,c_7259])).

tff(c_7263,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_7247])).

tff(c_7305,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7263,c_2])).

tff(c_7307,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5827,c_7305])).

tff(c_7309,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_5819])).

tff(c_7315,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_7309,c_138])).

tff(c_48,plain,(
    ! [A_37] :
      ( v1_funct_2(k1_xboole_0,A_37,k1_xboole_0)
      | k1_xboole_0 = A_37
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_37,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_85,plain,(
    ! [A_37] :
      ( v1_funct_2(k1_xboole_0,A_37,k1_xboole_0)
      | k1_xboole_0 = A_37 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_48])).

tff(c_7715,plain,(
    ! [A_350] :
      ( v1_funct_2('#skF_1',A_350,'#skF_1')
      | A_350 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7315,c_7315,c_7315,c_85])).

tff(c_7308,plain,(
    v1_xboole_0(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_5819])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_7348,plain,(
    ! [A_335] :
      ( A_335 = '#skF_1'
      | ~ v1_xboole_0(A_335) ) ),
    inference(resolution,[status(thm)],[c_7309,c_4])).

tff(c_7355,plain,(
    k2_funct_1('#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_7308,c_7348])).

tff(c_7363,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7355,c_5741])).

tff(c_7719,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_7715,c_7363])).

tff(c_5821,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_5799])).

tff(c_5826,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_5821])).

tff(c_7723,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7719,c_5826])).

tff(c_7726,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7309,c_7723])).

tff(c_7727,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_5821])).

tff(c_7875,plain,(
    ! [A_359] :
      ( v1_xboole_0(k6_partfun1(A_359))
      | ~ v1_xboole_0(A_359) ) ),
    inference(resolution,[status(thm)],[c_62,c_5799])).

tff(c_7734,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_7727,c_138])).

tff(c_7757,plain,(
    ! [A_50] :
      ( A_50 = '#skF_3'
      | ~ v1_xboole_0(A_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7734,c_138])).

tff(c_7904,plain,(
    ! [A_362] :
      ( k6_partfun1(A_362) = '#skF_3'
      | ~ v1_xboole_0(A_362) ) ),
    inference(resolution,[status(thm)],[c_7875,c_7757])).

tff(c_7912,plain,(
    k6_partfun1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_7727,c_7904])).

tff(c_60,plain,(
    ! [A_40] : v1_partfun1(k6_partfun1(A_40),A_40) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_7929,plain,(
    v1_partfun1('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7912,c_60])).

tff(c_7760,plain,(
    ! [A_5] : m1_subset_1('#skF_3',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7734,c_12])).

tff(c_8531,plain,(
    ! [C_412,A_413,B_414] :
      ( v1_funct_2(C_412,A_413,B_414)
      | ~ v1_partfun1(C_412,A_413)
      | ~ v1_funct_1(C_412)
      | ~ m1_subset_1(C_412,k1_zfmisc_1(k2_zfmisc_1(A_413,B_414))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_8538,plain,(
    ! [A_413,B_414] :
      ( v1_funct_2('#skF_3',A_413,B_414)
      | ~ v1_partfun1('#skF_3',A_413)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_7760,c_8531])).

tff(c_8555,plain,(
    ! [A_415,B_416] :
      ( v1_funct_2('#skF_3',A_415,B_416)
      | ~ v1_partfun1('#skF_3',A_415) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_8538])).

tff(c_7743,plain,(
    ! [A_351] :
      ( k4_relat_1(A_351) = k2_funct_1(A_351)
      | ~ v2_funct_1(A_351)
      | ~ v1_funct_1(A_351)
      | ~ v1_relat_1(A_351) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_7746,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_7743])).

tff(c_7749,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5763,c_82,c_7746])).

tff(c_7926,plain,(
    k6_partfun1('#skF_3') = k4_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7912,c_83])).

tff(c_7936,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7912,c_7749,c_7926])).

tff(c_7728,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_5821])).

tff(c_7741,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_7728,c_138])).

tff(c_7768,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7734,c_7741])).

tff(c_7773,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7768,c_5741])).

tff(c_7939,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7936,c_7773])).

tff(c_8561,plain,(
    ~ v1_partfun1('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_8555,c_7939])).

tff(c_8569,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7929,c_8561])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:41:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.45/2.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.45/2.57  
% 7.45/2.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.45/2.57  %$ v1_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 7.45/2.57  
% 7.45/2.57  %Foreground sorts:
% 7.45/2.57  
% 7.45/2.57  
% 7.45/2.57  %Background operators:
% 7.45/2.57  
% 7.45/2.57  
% 7.45/2.57  %Foreground operators:
% 7.45/2.57  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.45/2.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.45/2.57  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.45/2.57  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.45/2.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.45/2.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.45/2.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.45/2.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.45/2.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.45/2.57  tff('#skF_2', type, '#skF_2': $i).
% 7.45/2.57  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.45/2.57  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.45/2.57  tff('#skF_3', type, '#skF_3': $i).
% 7.45/2.57  tff('#skF_1', type, '#skF_1': $i).
% 7.45/2.57  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.45/2.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.45/2.57  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.45/2.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.45/2.57  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.45/2.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.45/2.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.45/2.57  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.45/2.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.45/2.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.45/2.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.45/2.57  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 7.45/2.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.45/2.57  
% 7.76/2.60  tff(f_179, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 7.76/2.60  tff(f_103, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 7.76/2.60  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 7.76/2.60  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.76/2.60  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.76/2.60  tff(f_92, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 7.76/2.60  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.76/2.60  tff(f_146, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 7.76/2.60  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 7.76/2.60  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 7.76/2.60  tff(f_82, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 7.76/2.60  tff(f_162, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 7.76/2.60  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.76/2.60  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 7.76/2.60  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 7.76/2.60  tff(f_150, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.76/2.60  tff(f_66, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 7.76/2.60  tff(f_152, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.76/2.60  tff(f_58, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_relat_1)).
% 7.76/2.60  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.76/2.60  tff(f_121, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 7.76/2.60  tff(c_78, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.76/2.60  tff(c_267, plain, (![C_78, B_79, A_80]: (v1_xboole_0(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(B_79, A_80))) | ~v1_xboole_0(A_80))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.76/2.60  tff(c_285, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_78, c_267])).
% 7.76/2.60  tff(c_290, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_285])).
% 7.76/2.60  tff(c_82, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.76/2.60  tff(c_24, plain, (![A_13]: (v1_funct_1(k2_funct_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.76/2.60  tff(c_72, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.76/2.60  tff(c_157, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_72])).
% 7.76/2.60  tff(c_160, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_157])).
% 7.76/2.60  tff(c_163, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_160])).
% 7.76/2.60  tff(c_165, plain, (![C_56, A_57, B_58]: (v1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.76/2.60  tff(c_171, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_165])).
% 7.76/2.60  tff(c_184, plain, $false, inference(negUnitSimplification, [status(thm)], [c_163, c_171])).
% 7.76/2.60  tff(c_185, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_72])).
% 7.76/2.60  tff(c_217, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_185])).
% 7.76/2.60  tff(c_218, plain, (![C_63, A_64, B_65]: (v1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.76/2.60  tff(c_234, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_218])).
% 7.76/2.60  tff(c_76, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.76/2.60  tff(c_74, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.76/2.60  tff(c_519, plain, (![A_102, B_103, C_104]: (k2_relset_1(A_102, B_103, C_104)=k2_relat_1(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.76/2.60  tff(c_528, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_519])).
% 7.76/2.60  tff(c_542, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_528])).
% 7.76/2.60  tff(c_32, plain, (![A_16]: (k1_relat_1(k2_funct_1(A_16))=k2_relat_1(A_16) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.76/2.60  tff(c_26, plain, (![A_13]: (v1_relat_1(k2_funct_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.76/2.60  tff(c_80, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.76/2.60  tff(c_692, plain, (![A_118, B_119, C_120]: (k1_relset_1(A_118, B_119, C_120)=k1_relat_1(C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.76/2.60  tff(c_718, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_692])).
% 7.76/2.60  tff(c_1278, plain, (![B_153, A_154, C_155]: (k1_xboole_0=B_153 | k1_relset_1(A_154, B_153, C_155)=A_154 | ~v1_funct_2(C_155, A_154, B_153) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_154, B_153))))), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.76/2.60  tff(c_1290, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_78, c_1278])).
% 7.76/2.60  tff(c_1309, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_718, c_1290])).
% 7.76/2.60  tff(c_1313, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_1309])).
% 7.76/2.60  tff(c_399, plain, (![A_90]: (k2_relat_1(k2_funct_1(A_90))=k1_relat_1(A_90) | ~v2_funct_1(A_90) | ~v1_funct_1(A_90) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.76/2.60  tff(c_18, plain, (![A_10]: (k10_relat_1(A_10, k2_relat_1(A_10))=k1_relat_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.76/2.60  tff(c_4103, plain, (![A_205]: (k10_relat_1(k2_funct_1(A_205), k1_relat_1(A_205))=k1_relat_1(k2_funct_1(A_205)) | ~v1_relat_1(k2_funct_1(A_205)) | ~v2_funct_1(A_205) | ~v1_funct_1(A_205) | ~v1_relat_1(A_205))), inference(superposition, [status(thm), theory('equality')], [c_399, c_18])).
% 7.76/2.60  tff(c_4118, plain, (k10_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1313, c_4103])).
% 7.76/2.60  tff(c_4132, plain, (k10_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_234, c_82, c_76, c_4118])).
% 7.76/2.60  tff(c_4135, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_4132])).
% 7.76/2.60  tff(c_4138, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_4135])).
% 7.76/2.60  tff(c_4142, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_234, c_82, c_4138])).
% 7.76/2.60  tff(c_4144, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_4132])).
% 7.76/2.60  tff(c_186, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_72])).
% 7.76/2.60  tff(c_556, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_542, c_18])).
% 7.76/2.60  tff(c_566, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_234, c_556])).
% 7.76/2.60  tff(c_1320, plain, (k10_relat_1('#skF_3', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1313, c_566])).
% 7.76/2.60  tff(c_373, plain, (![A_88]: (k1_relat_1(k2_funct_1(A_88))=k2_relat_1(A_88) | ~v2_funct_1(A_88) | ~v1_funct_1(A_88) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.76/2.60  tff(c_16, plain, (![A_9]: (k9_relat_1(A_9, k1_relat_1(A_9))=k2_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.76/2.60  tff(c_5161, plain, (![A_215]: (k9_relat_1(k2_funct_1(A_215), k2_relat_1(A_215))=k2_relat_1(k2_funct_1(A_215)) | ~v1_relat_1(k2_funct_1(A_215)) | ~v2_funct_1(A_215) | ~v1_funct_1(A_215) | ~v1_relat_1(A_215))), inference(superposition, [status(thm), theory('equality')], [c_373, c_16])).
% 7.76/2.60  tff(c_5186, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_542, c_5161])).
% 7.76/2.60  tff(c_5199, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_234, c_82, c_76, c_4144, c_5186])).
% 7.76/2.60  tff(c_28, plain, (![B_15, A_14]: (k9_relat_1(k2_funct_1(B_15), A_14)=k10_relat_1(B_15, A_14) | ~v2_funct_1(B_15) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.76/2.60  tff(c_5203, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5199, c_28])).
% 7.76/2.60  tff(c_5210, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_234, c_82, c_76, c_1320, c_5203])).
% 7.76/2.60  tff(c_66, plain, (![A_42]: (m1_subset_1(A_42, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_42), k2_relat_1(A_42)))) | ~v1_funct_1(A_42) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_162])).
% 7.76/2.60  tff(c_5233, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_5210, c_66])).
% 7.76/2.60  tff(c_5259, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4144, c_186, c_5233])).
% 7.76/2.60  tff(c_5330, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_5259])).
% 7.76/2.60  tff(c_5348, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_234, c_82, c_76, c_542, c_5330])).
% 7.76/2.60  tff(c_5350, plain, $false, inference(negUnitSimplification, [status(thm)], [c_217, c_5348])).
% 7.76/2.60  tff(c_5351, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1309])).
% 7.76/2.60  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 7.76/2.60  tff(c_5390, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5351, c_2])).
% 7.76/2.60  tff(c_5392, plain, $false, inference(negUnitSimplification, [status(thm)], [c_290, c_5390])).
% 7.76/2.60  tff(c_5393, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_285])).
% 7.76/2.60  tff(c_135, plain, (![B_49, A_50]: (~v1_xboole_0(B_49) | B_49=A_50 | ~v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.76/2.60  tff(c_138, plain, (![A_50]: (k1_xboole_0=A_50 | ~v1_xboole_0(A_50))), inference(resolution, [status(thm)], [c_2, c_135])).
% 7.76/2.60  tff(c_5400, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_5393, c_138])).
% 7.76/2.60  tff(c_12, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.76/2.60  tff(c_5419, plain, (![A_5]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_5400, c_12])).
% 7.76/2.60  tff(c_62, plain, (![A_40]: (m1_subset_1(k6_partfun1(A_40), k1_zfmisc_1(k2_zfmisc_1(A_40, A_40))))), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.76/2.60  tff(c_5519, plain, (![A_221]: (v1_xboole_0(k6_partfun1(A_221)) | ~v1_xboole_0(A_221))), inference(resolution, [status(thm)], [c_62, c_267])).
% 7.76/2.60  tff(c_5416, plain, (![A_50]: (A_50='#skF_3' | ~v1_xboole_0(A_50))), inference(demodulation, [status(thm), theory('equality')], [c_5400, c_138])).
% 7.76/2.60  tff(c_5530, plain, (![A_222]: (k6_partfun1(A_222)='#skF_3' | ~v1_xboole_0(A_222))), inference(resolution, [status(thm)], [c_5519, c_5416])).
% 7.76/2.60  tff(c_5538, plain, (k6_partfun1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_5393, c_5530])).
% 7.76/2.60  tff(c_5503, plain, (![A_220]: (k4_relat_1(A_220)=k2_funct_1(A_220) | ~v2_funct_1(A_220) | ~v1_funct_1(A_220) | ~v1_relat_1(A_220))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.76/2.60  tff(c_5506, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_5503])).
% 7.76/2.60  tff(c_5509, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_234, c_82, c_5506])).
% 7.76/2.60  tff(c_64, plain, (![A_41]: (k6_relat_1(A_41)=k6_partfun1(A_41))), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.76/2.60  tff(c_20, plain, (![A_11]: (k4_relat_1(k6_relat_1(A_11))=k6_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.76/2.60  tff(c_83, plain, (![A_11]: (k4_relat_1(k6_partfun1(A_11))=k6_partfun1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_64, c_20])).
% 7.76/2.60  tff(c_5554, plain, (k6_partfun1('#skF_3')=k4_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5538, c_83])).
% 7.76/2.60  tff(c_5565, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5538, c_5509, c_5554])).
% 7.76/2.60  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.76/2.60  tff(c_5418, plain, (![B_4]: (k2_zfmisc_1('#skF_3', B_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5400, c_5400, c_10])).
% 7.76/2.60  tff(c_5394, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_285])).
% 7.76/2.60  tff(c_5407, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_5394, c_138])).
% 7.76/2.60  tff(c_5427, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5400, c_5407])).
% 7.76/2.60  tff(c_5430, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_5427, c_217])).
% 7.76/2.60  tff(c_5740, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5419, c_5565, c_5418, c_5430])).
% 7.76/2.60  tff(c_5742, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_185])).
% 7.76/2.60  tff(c_5799, plain, (![C_250, B_251, A_252]: (v1_xboole_0(C_250) | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(B_251, A_252))) | ~v1_xboole_0(A_252))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.76/2.60  tff(c_5819, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_5742, c_5799])).
% 7.76/2.60  tff(c_5827, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_5819])).
% 7.76/2.60  tff(c_5743, plain, (![C_236, A_237, B_238]: (v1_relat_1(C_236) | ~m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.76/2.60  tff(c_5763, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_5743])).
% 7.76/2.60  tff(c_6515, plain, (![A_292, B_293, C_294]: (k2_relset_1(A_292, B_293, C_294)=k2_relat_1(C_294) | ~m1_subset_1(C_294, k1_zfmisc_1(k2_zfmisc_1(A_292, B_293))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.76/2.60  tff(c_6524, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_6515])).
% 7.76/2.60  tff(c_6538, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_6524])).
% 7.76/2.60  tff(c_5741, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_185])).
% 7.76/2.60  tff(c_6310, plain, (![A_285, B_286, C_287]: (k1_relset_1(A_285, B_286, C_287)=k1_relat_1(C_287) | ~m1_subset_1(C_287, k1_zfmisc_1(k2_zfmisc_1(A_285, B_286))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.76/2.60  tff(c_6330, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_5742, c_6310])).
% 7.76/2.60  tff(c_7221, plain, (![B_331, C_332, A_333]: (k1_xboole_0=B_331 | v1_funct_2(C_332, A_333, B_331) | k1_relset_1(A_333, B_331, C_332)!=A_333 | ~m1_subset_1(C_332, k1_zfmisc_1(k2_zfmisc_1(A_333, B_331))))), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.76/2.60  tff(c_7227, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_5742, c_7221])).
% 7.76/2.60  tff(c_7246, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6330, c_7227])).
% 7.76/2.60  tff(c_7247, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_5741, c_7246])).
% 7.76/2.60  tff(c_7256, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_7247])).
% 7.76/2.60  tff(c_7259, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_7256])).
% 7.76/2.60  tff(c_7262, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5763, c_82, c_76, c_6538, c_7259])).
% 7.76/2.60  tff(c_7263, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_7247])).
% 7.76/2.60  tff(c_7305, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7263, c_2])).
% 7.76/2.60  tff(c_7307, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5827, c_7305])).
% 7.76/2.60  tff(c_7309, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_5819])).
% 7.76/2.60  tff(c_7315, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_7309, c_138])).
% 7.76/2.60  tff(c_48, plain, (![A_37]: (v1_funct_2(k1_xboole_0, A_37, k1_xboole_0) | k1_xboole_0=A_37 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_37, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.76/2.60  tff(c_85, plain, (![A_37]: (v1_funct_2(k1_xboole_0, A_37, k1_xboole_0) | k1_xboole_0=A_37)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_48])).
% 7.76/2.60  tff(c_7715, plain, (![A_350]: (v1_funct_2('#skF_1', A_350, '#skF_1') | A_350='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7315, c_7315, c_7315, c_85])).
% 7.76/2.60  tff(c_7308, plain, (v1_xboole_0(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_5819])).
% 7.76/2.60  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.76/2.60  tff(c_7348, plain, (![A_335]: (A_335='#skF_1' | ~v1_xboole_0(A_335))), inference(resolution, [status(thm)], [c_7309, c_4])).
% 7.76/2.60  tff(c_7355, plain, (k2_funct_1('#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_7308, c_7348])).
% 7.76/2.60  tff(c_7363, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7355, c_5741])).
% 7.76/2.60  tff(c_7719, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_7715, c_7363])).
% 7.76/2.60  tff(c_5821, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_78, c_5799])).
% 7.76/2.60  tff(c_5826, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_5821])).
% 7.76/2.60  tff(c_7723, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7719, c_5826])).
% 7.76/2.60  tff(c_7726, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7309, c_7723])).
% 7.76/2.60  tff(c_7727, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_5821])).
% 7.76/2.60  tff(c_7875, plain, (![A_359]: (v1_xboole_0(k6_partfun1(A_359)) | ~v1_xboole_0(A_359))), inference(resolution, [status(thm)], [c_62, c_5799])).
% 7.76/2.60  tff(c_7734, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_7727, c_138])).
% 7.76/2.60  tff(c_7757, plain, (![A_50]: (A_50='#skF_3' | ~v1_xboole_0(A_50))), inference(demodulation, [status(thm), theory('equality')], [c_7734, c_138])).
% 7.76/2.60  tff(c_7904, plain, (![A_362]: (k6_partfun1(A_362)='#skF_3' | ~v1_xboole_0(A_362))), inference(resolution, [status(thm)], [c_7875, c_7757])).
% 7.76/2.60  tff(c_7912, plain, (k6_partfun1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_7727, c_7904])).
% 7.76/2.60  tff(c_60, plain, (![A_40]: (v1_partfun1(k6_partfun1(A_40), A_40))), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.76/2.60  tff(c_7929, plain, (v1_partfun1('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7912, c_60])).
% 7.76/2.60  tff(c_7760, plain, (![A_5]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_7734, c_12])).
% 7.76/2.60  tff(c_8531, plain, (![C_412, A_413, B_414]: (v1_funct_2(C_412, A_413, B_414) | ~v1_partfun1(C_412, A_413) | ~v1_funct_1(C_412) | ~m1_subset_1(C_412, k1_zfmisc_1(k2_zfmisc_1(A_413, B_414))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.76/2.60  tff(c_8538, plain, (![A_413, B_414]: (v1_funct_2('#skF_3', A_413, B_414) | ~v1_partfun1('#skF_3', A_413) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_7760, c_8531])).
% 7.76/2.60  tff(c_8555, plain, (![A_415, B_416]: (v1_funct_2('#skF_3', A_415, B_416) | ~v1_partfun1('#skF_3', A_415))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_8538])).
% 7.76/2.60  tff(c_7743, plain, (![A_351]: (k4_relat_1(A_351)=k2_funct_1(A_351) | ~v2_funct_1(A_351) | ~v1_funct_1(A_351) | ~v1_relat_1(A_351))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.76/2.60  tff(c_7746, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_7743])).
% 7.76/2.60  tff(c_7749, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5763, c_82, c_7746])).
% 7.76/2.60  tff(c_7926, plain, (k6_partfun1('#skF_3')=k4_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7912, c_83])).
% 7.76/2.60  tff(c_7936, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7912, c_7749, c_7926])).
% 7.76/2.60  tff(c_7728, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_5821])).
% 7.76/2.60  tff(c_7741, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_7728, c_138])).
% 7.76/2.60  tff(c_7768, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7734, c_7741])).
% 7.76/2.60  tff(c_7773, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7768, c_5741])).
% 7.76/2.60  tff(c_7939, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7936, c_7773])).
% 7.76/2.60  tff(c_8561, plain, (~v1_partfun1('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_8555, c_7939])).
% 7.76/2.60  tff(c_8569, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7929, c_8561])).
% 7.76/2.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.76/2.60  
% 7.76/2.60  Inference rules
% 7.76/2.60  ----------------------
% 7.76/2.60  #Ref     : 0
% 7.76/2.60  #Sup     : 2203
% 7.76/2.60  #Fact    : 0
% 7.76/2.60  #Define  : 0
% 7.76/2.60  #Split   : 20
% 7.76/2.60  #Chain   : 0
% 7.76/2.60  #Close   : 0
% 7.76/2.60  
% 7.76/2.60  Ordering : KBO
% 7.76/2.60  
% 7.76/2.60  Simplification rules
% 7.76/2.60  ----------------------
% 7.76/2.60  #Subsume      : 611
% 7.76/2.60  #Demod        : 1514
% 7.76/2.60  #Tautology    : 769
% 7.76/2.60  #SimpNegUnit  : 12
% 7.76/2.60  #BackRed      : 191
% 7.76/2.60  
% 7.76/2.60  #Partial instantiations: 0
% 7.76/2.60  #Strategies tried      : 1
% 7.76/2.60  
% 7.76/2.60  Timing (in seconds)
% 7.76/2.60  ----------------------
% 7.76/2.60  Preprocessing        : 0.37
% 7.76/2.60  Parsing              : 0.20
% 7.76/2.60  CNF conversion       : 0.02
% 7.76/2.60  Main loop            : 1.43
% 7.76/2.60  Inferencing          : 0.45
% 7.76/2.60  Reduction            : 0.50
% 7.76/2.60  Demodulation         : 0.36
% 7.76/2.60  BG Simplification    : 0.06
% 7.76/2.60  Subsumption          : 0.33
% 7.76/2.60  Abstraction          : 0.07
% 7.76/2.60  MUC search           : 0.00
% 7.76/2.60  Cooper               : 0.00
% 7.76/2.60  Total                : 1.87
% 7.76/2.60  Index Insertion      : 0.00
% 7.76/2.60  Index Deletion       : 0.00
% 7.76/2.60  Index Matching       : 0.00
% 7.76/2.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
