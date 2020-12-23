%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:32 EST 2020

% Result     : Theorem 6.10s
% Output     : CNFRefutation 6.10s
% Verified   : 
% Statistics : Number of formulae       :  233 (3186 expanded)
%              Number of leaves         :   41 (1032 expanded)
%              Depth                    :   17
%              Number of atoms          :  407 (8699 expanded)
%              Number of equality atoms :  142 (2775 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_148,negated_conjecture,(
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

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_121,axiom,(
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

tff(f_131,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_103,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_68,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_72,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_3145,plain,(
    ! [C_384,A_385,B_386] :
      ( v1_relat_1(C_384)
      | ~ m1_subset_1(C_384,k1_zfmisc_1(k2_zfmisc_1(A_385,B_386))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3158,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_3145])).

tff(c_76,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_70,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_3427,plain,(
    ! [A_441,B_442,C_443] :
      ( k2_relset_1(A_441,B_442,C_443) = k2_relat_1(C_443)
      | ~ m1_subset_1(C_443,k1_zfmisc_1(k2_zfmisc_1(A_441,B_442))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_3437,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_3427])).

tff(c_3441,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3437])).

tff(c_34,plain,(
    ! [A_15] :
      ( k1_relat_1(k2_funct_1(A_15)) = k2_relat_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24,plain,(
    ! [A_13] :
      ( v1_funct_1(k2_funct_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_66,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_128,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_131,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_128])).

tff(c_134,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_131])).

tff(c_160,plain,(
    ! [C_55,A_56,B_57] :
      ( v1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_167,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_160])).

tff(c_172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_167])).

tff(c_173,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_175,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_173])).

tff(c_200,plain,(
    ! [C_63,A_64,B_65] :
      ( v1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_209,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_200])).

tff(c_482,plain,(
    ! [A_124,B_125,C_126] :
      ( k2_relset_1(A_124,B_125,C_126) = k2_relat_1(C_126)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_492,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_482])).

tff(c_496,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_492])).

tff(c_18,plain,(
    ! [A_12] :
      ( k2_relat_1(A_12) != k1_xboole_0
      | k1_xboole_0 = A_12
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_217,plain,
    ( k2_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_209,c_18])).

tff(c_219,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_217])).

tff(c_497,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_496,c_219])).

tff(c_74,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_440,plain,(
    ! [A_115,B_116,C_117] :
      ( k1_relset_1(A_115,B_116,C_117) = k1_relat_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_453,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_440])).

tff(c_937,plain,(
    ! [B_182,A_183,C_184] :
      ( k1_xboole_0 = B_182
      | k1_relset_1(A_183,B_182,C_184) = A_183
      | ~ v1_funct_2(C_184,A_183,B_182)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_183,B_182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_950,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_937])).

tff(c_959,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_453,c_950])).

tff(c_960,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_497,c_959])).

tff(c_32,plain,(
    ! [A_15] :
      ( k2_relat_1(k2_funct_1(A_15)) = k1_relat_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_26,plain,(
    ! [A_13] :
      ( v1_relat_1(k2_funct_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_174,plain,(
    v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_311,plain,(
    ! [A_90] :
      ( k2_relat_1(k2_funct_1(A_90)) = k1_relat_1(A_90)
      | ~ v2_funct_1(A_90)
      | ~ v1_funct_1(A_90)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_62,plain,(
    ! [A_35] :
      ( v1_funct_2(A_35,k1_relat_1(A_35),k2_relat_1(A_35))
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1626,plain,(
    ! [A_229] :
      ( v1_funct_2(k2_funct_1(A_229),k1_relat_1(k2_funct_1(A_229)),k1_relat_1(A_229))
      | ~ v1_funct_1(k2_funct_1(A_229))
      | ~ v1_relat_1(k2_funct_1(A_229))
      | ~ v2_funct_1(A_229)
      | ~ v1_funct_1(A_229)
      | ~ v1_relat_1(A_229) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_62])).

tff(c_1635,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_960,c_1626])).

tff(c_1646,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_76,c_70,c_174,c_1635])).

tff(c_1671,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1646])).

tff(c_1687,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_1671])).

tff(c_1691,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_76,c_1687])).

tff(c_1693,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1646])).

tff(c_351,plain,(
    ! [A_101] :
      ( m1_subset_1(A_101,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_101),k2_relat_1(A_101))))
      | ~ v1_funct_1(A_101)
      | ~ v1_relat_1(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1848,plain,(
    ! [A_244] :
      ( m1_subset_1(k2_funct_1(A_244),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_244),k2_relat_1(k2_funct_1(A_244)))))
      | ~ v1_funct_1(k2_funct_1(A_244))
      | ~ v1_relat_1(k2_funct_1(A_244))
      | ~ v2_funct_1(A_244)
      | ~ v1_funct_1(A_244)
      | ~ v1_relat_1(A_244) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_351])).

tff(c_1875,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5')))))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_496,c_1848])).

tff(c_1891,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_76,c_70,c_1693,c_174,c_1875])).

tff(c_1918,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_5'))))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1891])).

tff(c_1936,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_76,c_70,c_960,c_1918])).

tff(c_1938,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_175,c_1936])).

tff(c_1939,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_1940,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_1955,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1939,c_1940])).

tff(c_2300,plain,(
    ! [A_298,B_299,C_300] :
      ( k2_relset_1(A_298,B_299,C_300) = k2_relat_1(C_300)
      | ~ m1_subset_1(C_300,k1_zfmisc_1(k2_zfmisc_1(A_298,B_299))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2313,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_2300])).

tff(c_2319,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1955,c_68,c_2313])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1948,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1939,c_12])).

tff(c_2339,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2319,c_1948])).

tff(c_2338,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2319,c_2319,c_1955])).

tff(c_2341,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2319,c_209])).

tff(c_2350,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2319,c_76])).

tff(c_2349,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2319,c_70])).

tff(c_2344,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2319,c_174])).

tff(c_2095,plain,(
    ! [A_272] :
      ( k1_relat_1(k2_funct_1(A_272)) = k2_relat_1(A_272)
      | ~ v2_funct_1(A_272)
      | ~ v1_funct_1(A_272)
      | ~ v1_relat_1(A_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_3031,plain,(
    ! [A_375] :
      ( v1_funct_2(k2_funct_1(A_375),k2_relat_1(A_375),k2_relat_1(k2_funct_1(A_375)))
      | ~ v1_funct_1(k2_funct_1(A_375))
      | ~ v1_relat_1(k2_funct_1(A_375))
      | ~ v2_funct_1(A_375)
      | ~ v1_funct_1(A_375)
      | ~ v1_relat_1(A_375) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2095,c_62])).

tff(c_3034,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_4',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2338,c_3031])).

tff(c_3042,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_4',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2341,c_2350,c_2349,c_2344,c_3034])).

tff(c_3043,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3042])).

tff(c_3046,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_3043])).

tff(c_3050,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2341,c_2350,c_3046])).

tff(c_3052,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3042])).

tff(c_20,plain,(
    ! [A_12] :
      ( k1_relat_1(A_12) != k1_xboole_0
      | k1_xboole_0 = A_12
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1943,plain,(
    ! [A_12] :
      ( k1_relat_1(A_12) != '#skF_5'
      | A_12 = '#skF_5'
      | ~ v1_relat_1(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1939,c_1939,c_20])).

tff(c_2334,plain,(
    ! [A_12] :
      ( k1_relat_1(A_12) != '#skF_4'
      | A_12 = '#skF_4'
      | ~ v1_relat_1(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2319,c_2319,c_1943])).

tff(c_3059,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3052,c_2334])).

tff(c_3073,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3059])).

tff(c_3083,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_3073])).

tff(c_3086,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2341,c_2350,c_2349,c_2338,c_3083])).

tff(c_3087,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3059])).

tff(c_1944,plain,(
    ! [A_12] :
      ( k2_relat_1(A_12) != '#skF_5'
      | A_12 = '#skF_5'
      | ~ v1_relat_1(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1939,c_1939,c_18])).

tff(c_2335,plain,(
    ! [A_12] :
      ( k2_relat_1(A_12) != '#skF_4'
      | A_12 = '#skF_4'
      | ~ v1_relat_1(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2319,c_2319,c_1944])).

tff(c_3060,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3052,c_2335])).

tff(c_3067,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3060])).

tff(c_3089,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3087,c_3067])).

tff(c_3099,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2338,c_3089])).

tff(c_3100,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3060])).

tff(c_2006,plain,(
    ! [A_250,B_251] :
      ( r2_hidden('#skF_2'(A_250,B_251),A_250)
      | r1_tarski(A_250,B_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2031,plain,(
    ! [A_255,B_256] :
      ( ~ v1_xboole_0(A_255)
      | r1_tarski(A_255,B_256) ) ),
    inference(resolution,[status(thm)],[c_2006,c_2])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_188,plain,(
    ~ r1_tarski(k2_funct_1('#skF_5'),k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_175])).

tff(c_2040,plain,(
    ~ v1_xboole_0(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2031,c_188])).

tff(c_2333,plain,(
    ~ v1_xboole_0(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2319,c_2040])).

tff(c_3107,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3100,c_2333])).

tff(c_3113,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2339,c_3107])).

tff(c_3114,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_3166,plain,
    ( k2_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3158,c_18])).

tff(c_3176,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3166])).

tff(c_3442,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3441,c_3176])).

tff(c_3373,plain,(
    ! [A_430,B_431,C_432] :
      ( k1_relset_1(A_430,B_431,C_432) = k1_relat_1(C_432)
      | ~ m1_subset_1(C_432,k1_zfmisc_1(k2_zfmisc_1(A_430,B_431))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3386,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_3373])).

tff(c_3911,plain,(
    ! [B_494,A_495,C_496] :
      ( k1_xboole_0 = B_494
      | k1_relset_1(A_495,B_494,C_496) = A_495
      | ~ v1_funct_2(C_496,A_495,B_494)
      | ~ m1_subset_1(C_496,k1_zfmisc_1(k2_zfmisc_1(A_495,B_494))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_3927,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_3911])).

tff(c_3938,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3386,c_3927])).

tff(c_3939,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_3442,c_3938])).

tff(c_3165,plain,
    ( k1_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3158,c_20])).

tff(c_3167,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3165])).

tff(c_3949,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3939,c_3167])).

tff(c_3115,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_3384,plain,(
    k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) = k1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_3115,c_3373])).

tff(c_4049,plain,(
    ! [B_502,C_503,A_504] :
      ( k1_xboole_0 = B_502
      | v1_funct_2(C_503,A_504,B_502)
      | k1_relset_1(A_504,B_502,C_503) != A_504
      | ~ m1_subset_1(C_503,k1_zfmisc_1(k2_zfmisc_1(A_504,B_502))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_4055,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_3115,c_4049])).

tff(c_4065,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3384,c_4055])).

tff(c_4066,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_3114,c_3949,c_4065])).

tff(c_4074,plain,
    ( k2_relat_1('#skF_5') != '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_4066])).

tff(c_4077,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3158,c_76,c_70,c_3441,c_4074])).

tff(c_4078,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3166])).

tff(c_4080,plain,(
    k1_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4078,c_3167])).

tff(c_4079,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3166])).

tff(c_4095,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4078,c_4079])).

tff(c_4301,plain,(
    ! [A_541] :
      ( k1_relat_1(k2_funct_1(A_541)) = k2_relat_1(A_541)
      | ~ v2_funct_1(A_541)
      | ~ v1_funct_1(A_541)
      | ~ v1_relat_1(A_541) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_3156,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_3115,c_3145])).

tff(c_3174,plain,
    ( k1_relat_1(k2_funct_1('#skF_5')) != k1_xboole_0
    | k2_funct_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3156,c_20])).

tff(c_4132,plain,
    ( k1_relat_1(k2_funct_1('#skF_5')) != '#skF_5'
    | k2_funct_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4078,c_4078,c_3174])).

tff(c_4133,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_4132])).

tff(c_4310,plain,
    ( k2_relat_1('#skF_5') != '#skF_5'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4301,c_4133])).

tff(c_4317,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3158,c_76,c_70,c_4095,c_4310])).

tff(c_4318,plain,(
    k2_funct_1('#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_4132])).

tff(c_4319,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_4132])).

tff(c_4341,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4318,c_4319])).

tff(c_4342,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4080,c_4341])).

tff(c_4343,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3165])).

tff(c_4344,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3165])).

tff(c_4370,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4343,c_4344])).

tff(c_4528,plain,(
    ! [A_568] :
      ( k2_relat_1(k2_funct_1(A_568)) = k1_relat_1(A_568)
      | ~ v2_funct_1(A_568)
      | ~ v1_funct_1(A_568)
      | ~ v1_relat_1(A_568) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4446,plain,(
    ! [A_556] :
      ( k2_relat_1(A_556) != '#skF_5'
      | A_556 = '#skF_5'
      | ~ v1_relat_1(A_556) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4343,c_4343,c_18])).

tff(c_4463,plain,
    ( k2_relat_1(k2_funct_1('#skF_5')) != '#skF_5'
    | k2_funct_1('#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3156,c_4446])).

tff(c_4481,plain,(
    k2_relat_1(k2_funct_1('#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_4463])).

tff(c_4534,plain,
    ( k1_relat_1('#skF_5') != '#skF_5'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4528,c_4481])).

tff(c_4544,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3158,c_76,c_70,c_4370,c_4534])).

tff(c_4545,plain,(
    k2_funct_1('#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_4463])).

tff(c_4417,plain,(
    ! [A_554] :
      ( k1_relat_1(A_554) != '#skF_5'
      | A_554 = '#skF_5'
      | ~ v1_relat_1(A_554) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4343,c_4343,c_20])).

tff(c_4434,plain,
    ( k1_relat_1(k2_funct_1('#skF_5')) != '#skF_5'
    | k2_funct_1('#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3156,c_4417])).

tff(c_4474,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_4434])).

tff(c_4547,plain,(
    k1_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4545,c_4474])).

tff(c_4555,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4370,c_4547])).

tff(c_4556,plain,(
    k2_funct_1('#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_4434])).

tff(c_4631,plain,(
    ! [A_578] :
      ( k1_relat_1(k2_funct_1(A_578)) = k2_relat_1(A_578)
      | ~ v2_funct_1(A_578)
      | ~ v1_funct_1(A_578)
      | ~ v1_relat_1(A_578) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4643,plain,
    ( k2_relat_1('#skF_5') = k1_relat_1('#skF_5')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4556,c_4631])).

tff(c_4647,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3158,c_76,c_70,c_4370,c_4643])).

tff(c_4792,plain,(
    ! [A_597,B_598,C_599] :
      ( k2_relset_1(A_597,B_598,C_599) = k2_relat_1(C_599)
      | ~ m1_subset_1(C_599,k1_zfmisc_1(k2_zfmisc_1(A_597,B_598))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4802,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_4792])).

tff(c_4807,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_4647,c_4802])).

tff(c_4824,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4807,c_4807,c_4370])).

tff(c_4560,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4556,c_3115])).

tff(c_4677,plain,(
    ! [C_580,A_581,B_582] :
      ( v1_partfun1(C_580,A_581)
      | ~ m1_subset_1(C_580,k1_zfmisc_1(k2_zfmisc_1(A_581,B_582)))
      | ~ v1_xboole_0(A_581) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_4688,plain,
    ( v1_partfun1('#skF_5','#skF_4')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4560,c_4677])).

tff(c_4692,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_4688])).

tff(c_4693,plain,(
    ! [A_583,B_584,C_585] :
      ( k2_relset_1(A_583,B_584,C_585) = k2_relat_1(C_585)
      | ~ m1_subset_1(C_585,k1_zfmisc_1(k2_zfmisc_1(A_583,B_584))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4703,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_4693])).

tff(c_4708,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4647,c_68,c_4703])).

tff(c_4352,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4343,c_12])).

tff(c_4723,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4708,c_4352])).

tff(c_4733,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4692,c_4723])).

tff(c_4735,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_4688])).

tff(c_3139,plain,(
    ! [A_380,B_381] :
      ( r2_hidden('#skF_2'(A_380,B_381),A_380)
      | r1_tarski(A_380,B_381) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3143,plain,(
    ! [A_380,B_381] :
      ( ~ v1_xboole_0(A_380)
      | r1_tarski(A_380,B_381) ) ),
    inference(resolution,[status(thm)],[c_3139,c_2])).

tff(c_4375,plain,(
    ! [A_542,A_543,B_544] :
      ( v1_relat_1(A_542)
      | ~ r1_tarski(A_542,k2_zfmisc_1(A_543,B_544)) ) ),
    inference(resolution,[status(thm)],[c_16,c_3145])).

tff(c_4386,plain,(
    ! [A_380] :
      ( v1_relat_1(A_380)
      | ~ v1_xboole_0(A_380) ) ),
    inference(resolution,[status(thm)],[c_3143,c_4375])).

tff(c_4739,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4735,c_4386])).

tff(c_4347,plain,(
    ! [A_12] :
      ( k1_relat_1(A_12) != '#skF_5'
      | A_12 = '#skF_5'
      | ~ v1_relat_1(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4343,c_4343,c_20])).

tff(c_4747,plain,
    ( k1_relat_1('#skF_4') != '#skF_5'
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4739,c_4347])).

tff(c_4748,plain,(
    k1_relat_1('#skF_4') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_4747])).

tff(c_4810,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4807,c_4748])).

tff(c_4931,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4824,c_4810])).

tff(c_4932,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4747])).

tff(c_4561,plain,(
    ~ v1_funct_2('#skF_5','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4556,c_3114])).

tff(c_4941,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4932,c_4561])).

tff(c_4957,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4932,c_76])).

tff(c_4734,plain,(
    v1_partfun1('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_4688])).

tff(c_4934,plain,(
    v1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4932,c_4734])).

tff(c_4939,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4932,c_4560])).

tff(c_5325,plain,(
    ! [C_622,A_623,B_624] :
      ( v1_funct_2(C_622,A_623,B_624)
      | ~ v1_partfun1(C_622,A_623)
      | ~ v1_funct_1(C_622)
      | ~ m1_subset_1(C_622,k1_zfmisc_1(k2_zfmisc_1(A_623,B_624))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_5334,plain,
    ( v1_funct_2('#skF_4','#skF_4','#skF_3')
    | ~ v1_partfun1('#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4939,c_5325])).

tff(c_5348,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4957,c_4934,c_5334])).

tff(c_5350,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4941,c_5348])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:02:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.10/2.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.10/2.17  
% 6.10/2.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.10/2.17  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 6.10/2.17  
% 6.10/2.17  %Foreground sorts:
% 6.10/2.17  
% 6.10/2.17  
% 6.10/2.17  %Background operators:
% 6.10/2.17  
% 6.10/2.17  
% 6.10/2.17  %Foreground operators:
% 6.10/2.17  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.10/2.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.10/2.17  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.10/2.17  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.10/2.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.10/2.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.10/2.17  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.10/2.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.10/2.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.10/2.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.10/2.17  tff('#skF_5', type, '#skF_5': $i).
% 6.10/2.17  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.10/2.17  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.10/2.17  tff('#skF_3', type, '#skF_3': $i).
% 6.10/2.17  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.10/2.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.10/2.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.10/2.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.10/2.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.10/2.17  tff('#skF_4', type, '#skF_4': $i).
% 6.10/2.17  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.10/2.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.10/2.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.10/2.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.10/2.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.10/2.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.10/2.17  
% 6.10/2.20  tff(f_148, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 6.10/2.20  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.10/2.20  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.10/2.20  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 6.10/2.20  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 6.10/2.20  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 6.10/2.20  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.10/2.20  tff(f_121, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 6.10/2.20  tff(f_131, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 6.10/2.20  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.10/2.20  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.10/2.20  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.10/2.20  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.10/2.20  tff(f_103, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_partfun1)).
% 6.10/2.20  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 6.10/2.20  tff(c_68, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.10/2.20  tff(c_72, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.10/2.20  tff(c_3145, plain, (![C_384, A_385, B_386]: (v1_relat_1(C_384) | ~m1_subset_1(C_384, k1_zfmisc_1(k2_zfmisc_1(A_385, B_386))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.10/2.20  tff(c_3158, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_3145])).
% 6.10/2.20  tff(c_76, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.10/2.20  tff(c_70, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.10/2.20  tff(c_3427, plain, (![A_441, B_442, C_443]: (k2_relset_1(A_441, B_442, C_443)=k2_relat_1(C_443) | ~m1_subset_1(C_443, k1_zfmisc_1(k2_zfmisc_1(A_441, B_442))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.10/2.20  tff(c_3437, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_3427])).
% 6.10/2.20  tff(c_3441, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_3437])).
% 6.10/2.20  tff(c_34, plain, (![A_15]: (k1_relat_1(k2_funct_1(A_15))=k2_relat_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.10/2.20  tff(c_24, plain, (![A_13]: (v1_funct_1(k2_funct_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.10/2.20  tff(c_66, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.10/2.20  tff(c_128, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_66])).
% 6.10/2.20  tff(c_131, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_24, c_128])).
% 6.10/2.20  tff(c_134, plain, (~v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_131])).
% 6.10/2.20  tff(c_160, plain, (![C_55, A_56, B_57]: (v1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.10/2.20  tff(c_167, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_160])).
% 6.10/2.20  tff(c_172, plain, $false, inference(negUnitSimplification, [status(thm)], [c_134, c_167])).
% 6.10/2.20  tff(c_173, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_66])).
% 6.10/2.20  tff(c_175, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_173])).
% 6.10/2.20  tff(c_200, plain, (![C_63, A_64, B_65]: (v1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.10/2.20  tff(c_209, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_200])).
% 6.10/2.20  tff(c_482, plain, (![A_124, B_125, C_126]: (k2_relset_1(A_124, B_125, C_126)=k2_relat_1(C_126) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.10/2.20  tff(c_492, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_482])).
% 6.10/2.20  tff(c_496, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_492])).
% 6.10/2.20  tff(c_18, plain, (![A_12]: (k2_relat_1(A_12)!=k1_xboole_0 | k1_xboole_0=A_12 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.10/2.20  tff(c_217, plain, (k2_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_209, c_18])).
% 6.10/2.20  tff(c_219, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_217])).
% 6.10/2.20  tff(c_497, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_496, c_219])).
% 6.10/2.20  tff(c_74, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.10/2.20  tff(c_440, plain, (![A_115, B_116, C_117]: (k1_relset_1(A_115, B_116, C_117)=k1_relat_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.10/2.20  tff(c_453, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_440])).
% 6.10/2.20  tff(c_937, plain, (![B_182, A_183, C_184]: (k1_xboole_0=B_182 | k1_relset_1(A_183, B_182, C_184)=A_183 | ~v1_funct_2(C_184, A_183, B_182) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_183, B_182))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.10/2.20  tff(c_950, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_72, c_937])).
% 6.10/2.20  tff(c_959, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_453, c_950])).
% 6.10/2.20  tff(c_960, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_497, c_959])).
% 6.10/2.20  tff(c_32, plain, (![A_15]: (k2_relat_1(k2_funct_1(A_15))=k1_relat_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.10/2.20  tff(c_26, plain, (![A_13]: (v1_relat_1(k2_funct_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.10/2.20  tff(c_174, plain, (v1_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_66])).
% 6.10/2.20  tff(c_311, plain, (![A_90]: (k2_relat_1(k2_funct_1(A_90))=k1_relat_1(A_90) | ~v2_funct_1(A_90) | ~v1_funct_1(A_90) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.10/2.20  tff(c_62, plain, (![A_35]: (v1_funct_2(A_35, k1_relat_1(A_35), k2_relat_1(A_35)) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.10/2.20  tff(c_1626, plain, (![A_229]: (v1_funct_2(k2_funct_1(A_229), k1_relat_1(k2_funct_1(A_229)), k1_relat_1(A_229)) | ~v1_funct_1(k2_funct_1(A_229)) | ~v1_relat_1(k2_funct_1(A_229)) | ~v2_funct_1(A_229) | ~v1_funct_1(A_229) | ~v1_relat_1(A_229))), inference(superposition, [status(thm), theory('equality')], [c_311, c_62])).
% 6.10/2.20  tff(c_1635, plain, (v1_funct_2(k2_funct_1('#skF_5'), k1_relat_1(k2_funct_1('#skF_5')), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_960, c_1626])).
% 6.10/2.20  tff(c_1646, plain, (v1_funct_2(k2_funct_1('#skF_5'), k1_relat_1(k2_funct_1('#skF_5')), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_209, c_76, c_70, c_174, c_1635])).
% 6.10/2.20  tff(c_1671, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_1646])).
% 6.10/2.20  tff(c_1687, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_26, c_1671])).
% 6.10/2.20  tff(c_1691, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_209, c_76, c_1687])).
% 6.10/2.20  tff(c_1693, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_1646])).
% 6.10/2.20  tff(c_351, plain, (![A_101]: (m1_subset_1(A_101, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_101), k2_relat_1(A_101)))) | ~v1_funct_1(A_101) | ~v1_relat_1(A_101))), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.10/2.20  tff(c_1848, plain, (![A_244]: (m1_subset_1(k2_funct_1(A_244), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_244), k2_relat_1(k2_funct_1(A_244))))) | ~v1_funct_1(k2_funct_1(A_244)) | ~v1_relat_1(k2_funct_1(A_244)) | ~v2_funct_1(A_244) | ~v1_funct_1(A_244) | ~v1_relat_1(A_244))), inference(superposition, [status(thm), theory('equality')], [c_34, c_351])).
% 6.10/2.20  tff(c_1875, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5'))))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_496, c_1848])).
% 6.10/2.20  tff(c_1891, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5')))))), inference(demodulation, [status(thm), theory('equality')], [c_209, c_76, c_70, c_1693, c_174, c_1875])).
% 6.10/2.20  tff(c_1918, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_5')))) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_32, c_1891])).
% 6.10/2.20  tff(c_1936, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_209, c_76, c_70, c_960, c_1918])).
% 6.10/2.20  tff(c_1938, plain, $false, inference(negUnitSimplification, [status(thm)], [c_175, c_1936])).
% 6.10/2.20  tff(c_1939, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_217])).
% 6.10/2.20  tff(c_1940, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_217])).
% 6.10/2.20  tff(c_1955, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1939, c_1940])).
% 6.10/2.20  tff(c_2300, plain, (![A_298, B_299, C_300]: (k2_relset_1(A_298, B_299, C_300)=k2_relat_1(C_300) | ~m1_subset_1(C_300, k1_zfmisc_1(k2_zfmisc_1(A_298, B_299))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.10/2.20  tff(c_2313, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_2300])).
% 6.10/2.20  tff(c_2319, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1955, c_68, c_2313])).
% 6.10/2.20  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.10/2.20  tff(c_1948, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1939, c_12])).
% 6.10/2.20  tff(c_2339, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2319, c_1948])).
% 6.10/2.20  tff(c_2338, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2319, c_2319, c_1955])).
% 6.10/2.20  tff(c_2341, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2319, c_209])).
% 6.10/2.20  tff(c_2350, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2319, c_76])).
% 6.10/2.20  tff(c_2349, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2319, c_70])).
% 6.10/2.20  tff(c_2344, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2319, c_174])).
% 6.10/2.20  tff(c_2095, plain, (![A_272]: (k1_relat_1(k2_funct_1(A_272))=k2_relat_1(A_272) | ~v2_funct_1(A_272) | ~v1_funct_1(A_272) | ~v1_relat_1(A_272))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.10/2.20  tff(c_3031, plain, (![A_375]: (v1_funct_2(k2_funct_1(A_375), k2_relat_1(A_375), k2_relat_1(k2_funct_1(A_375))) | ~v1_funct_1(k2_funct_1(A_375)) | ~v1_relat_1(k2_funct_1(A_375)) | ~v2_funct_1(A_375) | ~v1_funct_1(A_375) | ~v1_relat_1(A_375))), inference(superposition, [status(thm), theory('equality')], [c_2095, c_62])).
% 6.10/2.20  tff(c_3034, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2338, c_3031])).
% 6.10/2.20  tff(c_3042, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2341, c_2350, c_2349, c_2344, c_3034])).
% 6.10/2.20  tff(c_3043, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_3042])).
% 6.10/2.20  tff(c_3046, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_3043])).
% 6.10/2.20  tff(c_3050, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2341, c_2350, c_3046])).
% 6.10/2.20  tff(c_3052, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_3042])).
% 6.10/2.20  tff(c_20, plain, (![A_12]: (k1_relat_1(A_12)!=k1_xboole_0 | k1_xboole_0=A_12 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.10/2.20  tff(c_1943, plain, (![A_12]: (k1_relat_1(A_12)!='#skF_5' | A_12='#skF_5' | ~v1_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_1939, c_1939, c_20])).
% 6.10/2.20  tff(c_2334, plain, (![A_12]: (k1_relat_1(A_12)!='#skF_4' | A_12='#skF_4' | ~v1_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_2319, c_2319, c_1943])).
% 6.10/2.20  tff(c_3059, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4' | k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_3052, c_2334])).
% 6.10/2.20  tff(c_3073, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_3059])).
% 6.10/2.20  tff(c_3083, plain, (k2_relat_1('#skF_4')!='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_34, c_3073])).
% 6.10/2.20  tff(c_3086, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2341, c_2350, c_2349, c_2338, c_3083])).
% 6.10/2.20  tff(c_3087, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_3059])).
% 6.10/2.20  tff(c_1944, plain, (![A_12]: (k2_relat_1(A_12)!='#skF_5' | A_12='#skF_5' | ~v1_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_1939, c_1939, c_18])).
% 6.10/2.20  tff(c_2335, plain, (![A_12]: (k2_relat_1(A_12)!='#skF_4' | A_12='#skF_4' | ~v1_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_2319, c_2319, c_1944])).
% 6.10/2.20  tff(c_3060, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4' | k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_3052, c_2335])).
% 6.10/2.20  tff(c_3067, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_3060])).
% 6.10/2.20  tff(c_3089, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3087, c_3067])).
% 6.10/2.20  tff(c_3099, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2338, c_3089])).
% 6.10/2.20  tff(c_3100, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_3060])).
% 6.10/2.20  tff(c_2006, plain, (![A_250, B_251]: (r2_hidden('#skF_2'(A_250, B_251), A_250) | r1_tarski(A_250, B_251))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.10/2.20  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.10/2.20  tff(c_2031, plain, (![A_255, B_256]: (~v1_xboole_0(A_255) | r1_tarski(A_255, B_256))), inference(resolution, [status(thm)], [c_2006, c_2])).
% 6.10/2.20  tff(c_16, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.10/2.20  tff(c_188, plain, (~r1_tarski(k2_funct_1('#skF_5'), k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_175])).
% 6.10/2.20  tff(c_2040, plain, (~v1_xboole_0(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_2031, c_188])).
% 6.10/2.20  tff(c_2333, plain, (~v1_xboole_0(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2319, c_2040])).
% 6.10/2.20  tff(c_3107, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3100, c_2333])).
% 6.10/2.20  tff(c_3113, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2339, c_3107])).
% 6.10/2.20  tff(c_3114, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_173])).
% 6.10/2.20  tff(c_3166, plain, (k2_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_3158, c_18])).
% 6.10/2.20  tff(c_3176, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3166])).
% 6.10/2.20  tff(c_3442, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3441, c_3176])).
% 6.10/2.20  tff(c_3373, plain, (![A_430, B_431, C_432]: (k1_relset_1(A_430, B_431, C_432)=k1_relat_1(C_432) | ~m1_subset_1(C_432, k1_zfmisc_1(k2_zfmisc_1(A_430, B_431))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.10/2.20  tff(c_3386, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_3373])).
% 6.10/2.20  tff(c_3911, plain, (![B_494, A_495, C_496]: (k1_xboole_0=B_494 | k1_relset_1(A_495, B_494, C_496)=A_495 | ~v1_funct_2(C_496, A_495, B_494) | ~m1_subset_1(C_496, k1_zfmisc_1(k2_zfmisc_1(A_495, B_494))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.10/2.20  tff(c_3927, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_72, c_3911])).
% 6.10/2.20  tff(c_3938, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_3386, c_3927])).
% 6.10/2.20  tff(c_3939, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_3442, c_3938])).
% 6.10/2.20  tff(c_3165, plain, (k1_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_3158, c_20])).
% 6.10/2.20  tff(c_3167, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3165])).
% 6.10/2.20  tff(c_3949, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3939, c_3167])).
% 6.10/2.20  tff(c_3115, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_173])).
% 6.10/2.20  tff(c_3384, plain, (k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))=k1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_3115, c_3373])).
% 6.10/2.20  tff(c_4049, plain, (![B_502, C_503, A_504]: (k1_xboole_0=B_502 | v1_funct_2(C_503, A_504, B_502) | k1_relset_1(A_504, B_502, C_503)!=A_504 | ~m1_subset_1(C_503, k1_zfmisc_1(k2_zfmisc_1(A_504, B_502))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.10/2.20  tff(c_4055, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))!='#skF_4'), inference(resolution, [status(thm)], [c_3115, c_4049])).
% 6.10/2.20  tff(c_4065, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3384, c_4055])).
% 6.10/2.20  tff(c_4066, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_3114, c_3949, c_4065])).
% 6.10/2.20  tff(c_4074, plain, (k2_relat_1('#skF_5')!='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_34, c_4066])).
% 6.10/2.20  tff(c_4077, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3158, c_76, c_70, c_3441, c_4074])).
% 6.10/2.20  tff(c_4078, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_3166])).
% 6.10/2.20  tff(c_4080, plain, (k1_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4078, c_3167])).
% 6.10/2.20  tff(c_4079, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_3166])).
% 6.10/2.20  tff(c_4095, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4078, c_4079])).
% 6.10/2.20  tff(c_4301, plain, (![A_541]: (k1_relat_1(k2_funct_1(A_541))=k2_relat_1(A_541) | ~v2_funct_1(A_541) | ~v1_funct_1(A_541) | ~v1_relat_1(A_541))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.10/2.20  tff(c_3156, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_3115, c_3145])).
% 6.10/2.20  tff(c_3174, plain, (k1_relat_1(k2_funct_1('#skF_5'))!=k1_xboole_0 | k2_funct_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_3156, c_20])).
% 6.10/2.20  tff(c_4132, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_5' | k2_funct_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4078, c_4078, c_3174])).
% 6.10/2.20  tff(c_4133, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_4132])).
% 6.10/2.20  tff(c_4310, plain, (k2_relat_1('#skF_5')!='#skF_5' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4301, c_4133])).
% 6.10/2.20  tff(c_4317, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3158, c_76, c_70, c_4095, c_4310])).
% 6.10/2.20  tff(c_4318, plain, (k2_funct_1('#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_4132])).
% 6.10/2.20  tff(c_4319, plain, (k1_relat_1(k2_funct_1('#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_4132])).
% 6.10/2.20  tff(c_4341, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4318, c_4319])).
% 6.10/2.20  tff(c_4342, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4080, c_4341])).
% 6.10/2.20  tff(c_4343, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_3165])).
% 6.10/2.20  tff(c_4344, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_3165])).
% 6.10/2.20  tff(c_4370, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4343, c_4344])).
% 6.10/2.20  tff(c_4528, plain, (![A_568]: (k2_relat_1(k2_funct_1(A_568))=k1_relat_1(A_568) | ~v2_funct_1(A_568) | ~v1_funct_1(A_568) | ~v1_relat_1(A_568))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.10/2.20  tff(c_4446, plain, (![A_556]: (k2_relat_1(A_556)!='#skF_5' | A_556='#skF_5' | ~v1_relat_1(A_556))), inference(demodulation, [status(thm), theory('equality')], [c_4343, c_4343, c_18])).
% 6.10/2.20  tff(c_4463, plain, (k2_relat_1(k2_funct_1('#skF_5'))!='#skF_5' | k2_funct_1('#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_3156, c_4446])).
% 6.10/2.20  tff(c_4481, plain, (k2_relat_1(k2_funct_1('#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_4463])).
% 6.10/2.20  tff(c_4534, plain, (k1_relat_1('#skF_5')!='#skF_5' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4528, c_4481])).
% 6.10/2.20  tff(c_4544, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3158, c_76, c_70, c_4370, c_4534])).
% 6.10/2.20  tff(c_4545, plain, (k2_funct_1('#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_4463])).
% 6.10/2.20  tff(c_4417, plain, (![A_554]: (k1_relat_1(A_554)!='#skF_5' | A_554='#skF_5' | ~v1_relat_1(A_554))), inference(demodulation, [status(thm), theory('equality')], [c_4343, c_4343, c_20])).
% 6.10/2.20  tff(c_4434, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_5' | k2_funct_1('#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_3156, c_4417])).
% 6.10/2.20  tff(c_4474, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_4434])).
% 6.10/2.20  tff(c_4547, plain, (k1_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4545, c_4474])).
% 6.10/2.20  tff(c_4555, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4370, c_4547])).
% 6.10/2.20  tff(c_4556, plain, (k2_funct_1('#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_4434])).
% 6.10/2.20  tff(c_4631, plain, (![A_578]: (k1_relat_1(k2_funct_1(A_578))=k2_relat_1(A_578) | ~v2_funct_1(A_578) | ~v1_funct_1(A_578) | ~v1_relat_1(A_578))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.10/2.20  tff(c_4643, plain, (k2_relat_1('#skF_5')=k1_relat_1('#skF_5') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4556, c_4631])).
% 6.10/2.20  tff(c_4647, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3158, c_76, c_70, c_4370, c_4643])).
% 6.10/2.20  tff(c_4792, plain, (![A_597, B_598, C_599]: (k2_relset_1(A_597, B_598, C_599)=k2_relat_1(C_599) | ~m1_subset_1(C_599, k1_zfmisc_1(k2_zfmisc_1(A_597, B_598))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.10/2.20  tff(c_4802, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_4792])).
% 6.10/2.20  tff(c_4807, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_4647, c_4802])).
% 6.10/2.20  tff(c_4824, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4807, c_4807, c_4370])).
% 6.10/2.20  tff(c_4560, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_4556, c_3115])).
% 6.10/2.20  tff(c_4677, plain, (![C_580, A_581, B_582]: (v1_partfun1(C_580, A_581) | ~m1_subset_1(C_580, k1_zfmisc_1(k2_zfmisc_1(A_581, B_582))) | ~v1_xboole_0(A_581))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.10/2.20  tff(c_4688, plain, (v1_partfun1('#skF_5', '#skF_4') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4560, c_4677])).
% 6.10/2.20  tff(c_4692, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_4688])).
% 6.10/2.20  tff(c_4693, plain, (![A_583, B_584, C_585]: (k2_relset_1(A_583, B_584, C_585)=k2_relat_1(C_585) | ~m1_subset_1(C_585, k1_zfmisc_1(k2_zfmisc_1(A_583, B_584))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.10/2.20  tff(c_4703, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_4693])).
% 6.10/2.20  tff(c_4708, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4647, c_68, c_4703])).
% 6.10/2.20  tff(c_4352, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4343, c_12])).
% 6.10/2.20  tff(c_4723, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4708, c_4352])).
% 6.10/2.20  tff(c_4733, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4692, c_4723])).
% 6.10/2.20  tff(c_4735, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_4688])).
% 6.10/2.20  tff(c_3139, plain, (![A_380, B_381]: (r2_hidden('#skF_2'(A_380, B_381), A_380) | r1_tarski(A_380, B_381))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.10/2.20  tff(c_3143, plain, (![A_380, B_381]: (~v1_xboole_0(A_380) | r1_tarski(A_380, B_381))), inference(resolution, [status(thm)], [c_3139, c_2])).
% 6.10/2.20  tff(c_4375, plain, (![A_542, A_543, B_544]: (v1_relat_1(A_542) | ~r1_tarski(A_542, k2_zfmisc_1(A_543, B_544)))), inference(resolution, [status(thm)], [c_16, c_3145])).
% 6.10/2.20  tff(c_4386, plain, (![A_380]: (v1_relat_1(A_380) | ~v1_xboole_0(A_380))), inference(resolution, [status(thm)], [c_3143, c_4375])).
% 6.10/2.20  tff(c_4739, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4735, c_4386])).
% 6.10/2.20  tff(c_4347, plain, (![A_12]: (k1_relat_1(A_12)!='#skF_5' | A_12='#skF_5' | ~v1_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_4343, c_4343, c_20])).
% 6.10/2.20  tff(c_4747, plain, (k1_relat_1('#skF_4')!='#skF_5' | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_4739, c_4347])).
% 6.10/2.20  tff(c_4748, plain, (k1_relat_1('#skF_4')!='#skF_5'), inference(splitLeft, [status(thm)], [c_4747])).
% 6.10/2.20  tff(c_4810, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4807, c_4748])).
% 6.10/2.20  tff(c_4931, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4824, c_4810])).
% 6.10/2.20  tff(c_4932, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_4747])).
% 6.10/2.20  tff(c_4561, plain, (~v1_funct_2('#skF_5', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4556, c_3114])).
% 6.10/2.20  tff(c_4941, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4932, c_4561])).
% 6.10/2.20  tff(c_4957, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4932, c_76])).
% 6.10/2.20  tff(c_4734, plain, (v1_partfun1('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_4688])).
% 6.10/2.20  tff(c_4934, plain, (v1_partfun1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4932, c_4734])).
% 6.10/2.20  tff(c_4939, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_4932, c_4560])).
% 6.10/2.20  tff(c_5325, plain, (![C_622, A_623, B_624]: (v1_funct_2(C_622, A_623, B_624) | ~v1_partfun1(C_622, A_623) | ~v1_funct_1(C_622) | ~m1_subset_1(C_622, k1_zfmisc_1(k2_zfmisc_1(A_623, B_624))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.10/2.20  tff(c_5334, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_3') | ~v1_partfun1('#skF_4', '#skF_4') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_4939, c_5325])).
% 6.10/2.20  tff(c_5348, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4957, c_4934, c_5334])).
% 6.10/2.20  tff(c_5350, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4941, c_5348])).
% 6.10/2.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.10/2.20  
% 6.10/2.20  Inference rules
% 6.10/2.20  ----------------------
% 6.10/2.20  #Ref     : 0
% 6.10/2.20  #Sup     : 1097
% 6.10/2.20  #Fact    : 0
% 6.10/2.20  #Define  : 0
% 6.10/2.20  #Split   : 49
% 6.10/2.20  #Chain   : 0
% 6.10/2.20  #Close   : 0
% 6.10/2.20  
% 6.10/2.20  Ordering : KBO
% 6.10/2.20  
% 6.10/2.20  Simplification rules
% 6.10/2.20  ----------------------
% 6.10/2.20  #Subsume      : 179
% 6.10/2.20  #Demod        : 1035
% 6.10/2.20  #Tautology    : 497
% 6.10/2.20  #SimpNegUnit  : 35
% 6.10/2.20  #BackRed      : 185
% 6.10/2.20  
% 6.10/2.20  #Partial instantiations: 0
% 6.10/2.20  #Strategies tried      : 1
% 6.10/2.20  
% 6.10/2.20  Timing (in seconds)
% 6.10/2.20  ----------------------
% 6.10/2.20  Preprocessing        : 0.34
% 6.10/2.20  Parsing              : 0.18
% 6.10/2.20  CNF conversion       : 0.02
% 6.10/2.20  Main loop            : 1.06
% 6.10/2.20  Inferencing          : 0.40
% 6.10/2.20  Reduction            : 0.34
% 6.10/2.20  Demodulation         : 0.23
% 6.10/2.20  BG Simplification    : 0.04
% 6.10/2.20  Subsumption          : 0.19
% 6.10/2.20  Abstraction          : 0.05
% 6.10/2.20  MUC search           : 0.00
% 6.10/2.20  Cooper               : 0.00
% 6.10/2.20  Total                : 1.46
% 6.10/2.20  Index Insertion      : 0.00
% 6.10/2.20  Index Deletion       : 0.00
% 6.10/2.20  Index Matching       : 0.00
% 6.10/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
