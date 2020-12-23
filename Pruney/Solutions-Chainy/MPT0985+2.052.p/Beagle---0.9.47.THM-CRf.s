%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:34 EST 2020

% Result     : Theorem 10.30s
% Output     : CNFRefutation 10.65s
% Verified   : 
% Statistics : Number of formulae       :  256 (2153 expanded)
%              Number of leaves         :   53 ( 744 expanded)
%              Depth                    :   14
%              Number of atoms          :  514 (5044 expanded)
%              Number of equality atoms :  148 (1856 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_200,negated_conjecture,(
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

tff(f_134,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_128,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_107,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_138,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_164,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_183,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(B,C)
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | ( v1_funct_1(D)
            & v1_funct_2(D,A,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_154,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_72,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

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

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_97,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( ? [B] :
            ( v1_relat_1(B)
            & v1_funct_1(B)
            & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
       => v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).

tff(f_124,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(A) = k1_relat_1(B)
              & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

tff(f_152,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_148,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_92,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_96,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_8927,plain,(
    ! [C_638,A_639,B_640] :
      ( v4_relat_1(C_638,A_639)
      | ~ m1_subset_1(C_638,k1_zfmisc_1(k2_zfmisc_1(A_639,B_640))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_8950,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_8927])).

tff(c_8696,plain,(
    ! [C_603,A_604,B_605] :
      ( v1_relat_1(C_603)
      | ~ m1_subset_1(C_603,k1_zfmisc_1(k2_zfmisc_1(A_604,B_605))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_8719,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_96,c_8696])).

tff(c_24,plain,(
    ! [A_14] :
      ( k1_relat_1(A_14) != k1_xboole_0
      | k1_xboole_0 = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8734,plain,
    ( k1_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_8719,c_24])).

tff(c_8754,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_8734])).

tff(c_100,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_280,plain,(
    ! [A_66] :
      ( v1_funct_1(k2_funct_1(A_66))
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_90,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_241,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_283,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_280,c_241])).

tff(c_286,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_283])).

tff(c_291,plain,(
    ! [C_70,A_71,B_72] :
      ( v1_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_304,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_96,c_291])).

tff(c_313,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_286,c_304])).

tff(c_315,plain,(
    v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_94,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_48,plain,(
    ! [A_23] :
      ( k2_relat_1(k2_funct_1(A_23)) = k1_relat_1(A_23)
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_657,plain,(
    ! [C_116,A_117,B_118] :
      ( v4_relat_1(C_116,A_117)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_676,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_657])).

tff(c_447,plain,(
    ! [C_87,A_88,B_89] :
      ( v1_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_466,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_96,c_447])).

tff(c_481,plain,
    ( k1_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_466,c_24])).

tff(c_511,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_481])).

tff(c_40,plain,(
    ! [A_18] :
      ( v1_relat_1(k2_funct_1(A_18))
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_864,plain,(
    ! [A_142,B_143,C_144] :
      ( k2_relset_1(A_142,B_143,C_144) = k2_relat_1(C_144)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_877,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_96,c_864])).

tff(c_884,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_877])).

tff(c_789,plain,(
    ! [A_131] :
      ( k1_relat_1(k2_funct_1(A_131)) = k2_relat_1(A_131)
      | ~ v2_funct_1(A_131)
      | ~ v1_funct_1(A_131)
      | ~ v1_relat_1(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_74,plain,(
    ! [A_41] :
      ( v1_funct_2(A_41,k1_relat_1(A_41),k2_relat_1(A_41))
      | ~ v1_funct_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_4702,plain,(
    ! [A_352] :
      ( v1_funct_2(k2_funct_1(A_352),k2_relat_1(A_352),k2_relat_1(k2_funct_1(A_352)))
      | ~ v1_funct_1(k2_funct_1(A_352))
      | ~ v1_relat_1(k2_funct_1(A_352))
      | ~ v2_funct_1(A_352)
      | ~ v1_funct_1(A_352)
      | ~ v1_relat_1(A_352) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_789,c_74])).

tff(c_4732,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_884,c_4702])).

tff(c_4756,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_100,c_94,c_315,c_4732])).

tff(c_4761,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_4756])).

tff(c_4770,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_4761])).

tff(c_4776,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_100,c_4770])).

tff(c_4777,plain,(
    v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_4756])).

tff(c_4856,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k1_relat_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_4777])).

tff(c_4860,plain,(
    v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_100,c_94,c_4856])).

tff(c_4778,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_4756])).

tff(c_50,plain,(
    ! [A_23] :
      ( k1_relat_1(k2_funct_1(A_23)) = k2_relat_1(A_23)
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_926,plain,(
    ! [A_146] :
      ( m1_subset_1(A_146,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_146),k2_relat_1(A_146))))
      | ~ v1_funct_1(A_146)
      | ~ v1_relat_1(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_5288,plain,(
    ! [A_383] :
      ( m1_subset_1(k2_funct_1(A_383),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_383),k2_relat_1(k2_funct_1(A_383)))))
      | ~ v1_funct_1(k2_funct_1(A_383))
      | ~ v1_relat_1(k2_funct_1(A_383))
      | ~ v2_funct_1(A_383)
      | ~ v1_funct_1(A_383)
      | ~ v1_relat_1(A_383) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_926])).

tff(c_5336,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5')))))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_884,c_5288])).

tff(c_5366,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_100,c_94,c_4778,c_315,c_5336])).

tff(c_5397,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_5'))))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_5366])).

tff(c_5410,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_100,c_94,c_5397])).

tff(c_20,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k1_relat_1(B_13),A_12)
      | ~ v4_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1926,plain,(
    ! [B_214,D_215,A_216,C_217] :
      ( k1_xboole_0 = B_214
      | m1_subset_1(D_215,k1_zfmisc_1(k2_zfmisc_1(A_216,C_217)))
      | ~ r1_tarski(B_214,C_217)
      | ~ m1_subset_1(D_215,k1_zfmisc_1(k2_zfmisc_1(A_216,B_214)))
      | ~ v1_funct_2(D_215,A_216,B_214)
      | ~ v1_funct_1(D_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_6664,plain,(
    ! [B_458,D_459,A_460,A_461] :
      ( k1_relat_1(B_458) = k1_xboole_0
      | m1_subset_1(D_459,k1_zfmisc_1(k2_zfmisc_1(A_460,A_461)))
      | ~ m1_subset_1(D_459,k1_zfmisc_1(k2_zfmisc_1(A_460,k1_relat_1(B_458))))
      | ~ v1_funct_2(D_459,A_460,k1_relat_1(B_458))
      | ~ v1_funct_1(D_459)
      | ~ v4_relat_1(B_458,A_461)
      | ~ v1_relat_1(B_458) ) ),
    inference(resolution,[status(thm)],[c_20,c_1926])).

tff(c_6666,plain,(
    ! [A_461] :
      ( k1_relat_1('#skF_5') = k1_xboole_0
      | m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_461)))
      | ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k1_relat_1('#skF_5'))
      | ~ v1_funct_1(k2_funct_1('#skF_5'))
      | ~ v4_relat_1('#skF_5',A_461)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5410,c_6664])).

tff(c_6686,plain,(
    ! [A_461] :
      ( k1_relat_1('#skF_5') = k1_xboole_0
      | m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_461)))
      | ~ v4_relat_1('#skF_5',A_461) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_315,c_4860,c_6666])).

tff(c_6700,plain,(
    ! [A_462] :
      ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_462)))
      | ~ v4_relat_1('#skF_5',A_462) ) ),
    inference(negUnitSimplification,[status(thm)],[c_511,c_6686])).

tff(c_314,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_358,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_314])).

tff(c_6740,plain,(
    ~ v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_6700,c_358])).

tff(c_6777,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_676,c_6740])).

tff(c_6778,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_481])).

tff(c_124,plain,(
    ! [A_50] : k6_relat_1(A_50) = k6_partfun1(A_50) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_36,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_130,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_36])).

tff(c_70,plain,(
    ! [A_40] : k6_relat_1(A_40) = k6_partfun1(A_40) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_32,plain,(
    ! [A_16] : k2_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_106,plain,(
    ! [A_16] : k2_relat_1(k6_partfun1(A_16)) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_32])).

tff(c_145,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_106])).

tff(c_6791,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6778,c_6778,c_145])).

tff(c_26,plain,(
    ! [A_15] :
      ( k1_relat_1(A_15) = k1_xboole_0
      | k2_relat_1(A_15) != k1_xboole_0
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_479,plain,
    ( k1_relat_1('#skF_5') = k1_xboole_0
    | k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_466,c_26])).

tff(c_6802,plain,
    ( k1_relat_1('#skF_5') = '#skF_5'
    | k2_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6778,c_6778,c_479])).

tff(c_6803,plain,(
    k2_relat_1('#skF_5') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_6802])).

tff(c_6835,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6791,c_6803])).

tff(c_6837,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_6802])).

tff(c_22,plain,(
    ! [A_14] :
      ( k2_relat_1(A_14) != k1_xboole_0
      | k1_xboole_0 = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_482,plain,
    ( k2_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_466,c_22])).

tff(c_489,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_482])).

tff(c_6780,plain,(
    k2_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6778,c_489])).

tff(c_6888,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6837,c_6780])).

tff(c_6889,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_482])).

tff(c_6901,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6889,c_6889,c_145])).

tff(c_7438,plain,(
    ! [A_514,B_515,C_516] :
      ( k2_relset_1(A_514,B_515,C_516) = k2_relat_1(C_516)
      | ~ m1_subset_1(C_516,k1_zfmisc_1(k2_zfmisc_1(A_514,B_515))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_7454,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_96,c_7438])).

tff(c_7462,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6901,c_92,c_7454])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6905,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6889,c_12])).

tff(c_7482,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7462,c_6905])).

tff(c_42,plain,(
    ! [A_19] : v1_relat_1(k6_relat_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_104,plain,(
    ! [A_19] : v1_relat_1(k6_partfun1(A_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_42])).

tff(c_188,plain,(
    ! [A_56] :
      ( k2_relat_1(A_56) != k1_xboole_0
      | k1_xboole_0 = A_56
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_194,plain,(
    ! [A_19] :
      ( k2_relat_1(k6_partfun1(A_19)) != k1_xboole_0
      | k6_partfun1(A_19) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_104,c_188])).

tff(c_200,plain,(
    ! [A_19] :
      ( k1_xboole_0 != A_19
      | k6_partfun1(A_19) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_194])).

tff(c_6897,plain,(
    ! [A_19] :
      ( A_19 != '#skF_5'
      | k6_partfun1(A_19) = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6889,c_6889,c_200])).

tff(c_7476,plain,(
    ! [A_19] :
      ( A_19 != '#skF_4'
      | k6_partfun1(A_19) = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7462,c_7462,c_6897])).

tff(c_437,plain,(
    ! [A_85,B_86] :
      ( r2_hidden('#skF_2'(A_85,B_86),A_85)
      | r1_tarski(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_446,plain,(
    ! [A_85,B_86] :
      ( ~ v1_xboole_0(A_85)
      | r1_tarski(A_85,B_86) ) ),
    inference(resolution,[status(thm)],[c_437,c_2])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_7147,plain,(
    ! [C_484,A_485,B_486] :
      ( v4_relat_1(C_484,A_485)
      | ~ m1_subset_1(C_484,k1_zfmisc_1(k2_zfmisc_1(A_485,B_486))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_8241,plain,(
    ! [A_556,A_557,B_558] :
      ( v4_relat_1(A_556,A_557)
      | ~ r1_tarski(A_556,k2_zfmisc_1(A_557,B_558)) ) ),
    inference(resolution,[status(thm)],[c_16,c_7147])).

tff(c_8277,plain,(
    ! [A_559,A_560] :
      ( v4_relat_1(A_559,A_560)
      | ~ v1_xboole_0(A_559) ) ),
    inference(resolution,[status(thm)],[c_446,c_8241])).

tff(c_30,plain,(
    ! [A_16] : k1_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_107,plain,(
    ! [A_16] : k1_relat_1(k6_partfun1(A_16)) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_30])).

tff(c_7069,plain,(
    ! [B_473,A_474] :
      ( r1_tarski(k1_relat_1(B_473),A_474)
      | ~ v4_relat_1(B_473,A_474)
      | ~ v1_relat_1(B_473) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_7078,plain,(
    ! [A_16,A_474] :
      ( r1_tarski(A_16,A_474)
      | ~ v4_relat_1(k6_partfun1(A_16),A_474)
      | ~ v1_relat_1(k6_partfun1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_7069])).

tff(c_7083,plain,(
    ! [A_16,A_474] :
      ( r1_tarski(A_16,A_474)
      | ~ v4_relat_1(k6_partfun1(A_16),A_474) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_7078])).

tff(c_8368,plain,(
    ! [A_568,A_569] :
      ( r1_tarski(A_568,A_569)
      | ~ v1_xboole_0(k6_partfun1(A_568)) ) ),
    inference(resolution,[status(thm)],[c_8277,c_7083])).

tff(c_8372,plain,(
    ! [A_19,A_569] :
      ( r1_tarski(A_19,A_569)
      | ~ v1_xboole_0('#skF_4')
      | A_19 != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7476,c_8368])).

tff(c_8377,plain,(
    ! [A_570,A_571] :
      ( r1_tarski(A_570,A_571)
      | A_570 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7482,c_8372])).

tff(c_362,plain,(
    ~ r1_tarski(k2_funct_1('#skF_5'),k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_358])).

tff(c_7486,plain,(
    ~ r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7462,c_362])).

tff(c_8408,plain,(
    k2_funct_1('#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_8377,c_7486])).

tff(c_44,plain,(
    ! [A_19] : v1_funct_1(k6_relat_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_103,plain,(
    ! [A_19] : v1_funct_1(k6_partfun1(A_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_44])).

tff(c_34,plain,(
    ! [A_17] :
      ( k5_relat_1(A_17,k6_relat_1(k2_relat_1(A_17))) = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_396,plain,(
    ! [A_83] :
      ( k5_relat_1(A_83,k6_partfun1(k2_relat_1(A_83))) = A_83
      | ~ v1_relat_1(A_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_34])).

tff(c_411,plain,(
    ! [A_16] :
      ( k5_relat_1(k6_partfun1(A_16),k6_partfun1(A_16)) = k6_partfun1(A_16)
      | ~ v1_relat_1(k6_partfun1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_396])).

tff(c_417,plain,(
    ! [A_16] : k5_relat_1(k6_partfun1(A_16),k6_partfun1(A_16)) = k6_partfun1(A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_411])).

tff(c_46,plain,(
    ! [A_20,B_22] :
      ( v2_funct_1(A_20)
      | k6_relat_1(k1_relat_1(A_20)) != k5_relat_1(A_20,B_22)
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_7635,plain,(
    ! [A_520,B_521] :
      ( v2_funct_1(A_520)
      | k6_partfun1(k1_relat_1(A_520)) != k5_relat_1(A_520,B_521)
      | ~ v1_funct_1(B_521)
      | ~ v1_relat_1(B_521)
      | ~ v1_funct_1(A_520)
      | ~ v1_relat_1(A_520) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_46])).

tff(c_7641,plain,(
    ! [A_16] :
      ( v2_funct_1(k6_partfun1(A_16))
      | k6_partfun1(k1_relat_1(k6_partfun1(A_16))) != k6_partfun1(A_16)
      | ~ v1_funct_1(k6_partfun1(A_16))
      | ~ v1_relat_1(k6_partfun1(A_16))
      | ~ v1_funct_1(k6_partfun1(A_16))
      | ~ v1_relat_1(k6_partfun1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_7635])).

tff(c_7649,plain,(
    ! [A_16] : v2_funct_1(k6_partfun1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_103,c_104,c_103,c_107,c_7641])).

tff(c_52,plain,(
    ! [A_24,B_26] :
      ( k2_funct_1(A_24) = B_26
      | k6_relat_1(k1_relat_1(A_24)) != k5_relat_1(A_24,B_26)
      | k2_relat_1(A_24) != k1_relat_1(B_26)
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_7991,plain,(
    ! [A_543,B_544] :
      ( k2_funct_1(A_543) = B_544
      | k6_partfun1(k1_relat_1(A_543)) != k5_relat_1(A_543,B_544)
      | k2_relat_1(A_543) != k1_relat_1(B_544)
      | ~ v2_funct_1(A_543)
      | ~ v1_funct_1(B_544)
      | ~ v1_relat_1(B_544)
      | ~ v1_funct_1(A_543)
      | ~ v1_relat_1(A_543) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_52])).

tff(c_8000,plain,(
    ! [A_16] :
      ( k2_funct_1(k6_partfun1(A_16)) = k6_partfun1(A_16)
      | k6_partfun1(k1_relat_1(k6_partfun1(A_16))) != k6_partfun1(A_16)
      | k2_relat_1(k6_partfun1(A_16)) != k1_relat_1(k6_partfun1(A_16))
      | ~ v2_funct_1(k6_partfun1(A_16))
      | ~ v1_funct_1(k6_partfun1(A_16))
      | ~ v1_relat_1(k6_partfun1(A_16))
      | ~ v1_funct_1(k6_partfun1(A_16))
      | ~ v1_relat_1(k6_partfun1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_7991])).

tff(c_8013,plain,(
    ! [A_545] : k2_funct_1(k6_partfun1(A_545)) = k6_partfun1(A_545) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_103,c_104,c_103,c_7649,c_106,c_107,c_107,c_8000])).

tff(c_8046,plain,(
    ! [A_546] :
      ( k6_partfun1(A_546) = k2_funct_1('#skF_4')
      | A_546 != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7476,c_8013])).

tff(c_8207,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_8046,c_107])).

tff(c_8107,plain,(
    ! [A_546] :
      ( v1_relat_1(k2_funct_1('#skF_4'))
      | A_546 != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8046,c_104])).

tff(c_8157,plain,(
    ! [A_546] : A_546 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_8107])).

tff(c_184,plain,(
    ! [A_55] : m1_subset_1(k6_partfun1(A_55),k1_zfmisc_1(k2_zfmisc_1(A_55,A_55))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_187,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_184])).

tff(c_6899,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6889,c_6889,c_6889,c_187])).

tff(c_7444,plain,(
    k2_relset_1('#skF_5','#skF_5','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_6899,c_7438])).

tff(c_7457,plain,(
    k2_relset_1('#skF_5','#skF_5','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6901,c_7444])).

tff(c_7797,plain,(
    k2_relset_1('#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7462,c_7462,c_7462,c_7462,c_7457])).

tff(c_8168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8157,c_7797])).

tff(c_8169,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_8107])).

tff(c_6895,plain,(
    ! [A_14] :
      ( k1_relat_1(A_14) != '#skF_5'
      | A_14 = '#skF_5'
      | ~ v1_relat_1(A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6889,c_6889,c_24])).

tff(c_8580,plain,(
    ! [A_594] :
      ( k1_relat_1(A_594) != '#skF_4'
      | A_594 = '#skF_4'
      | ~ v1_relat_1(A_594) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7462,c_7462,c_6895])).

tff(c_8589,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8169,c_8580])).

tff(c_8603,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8207,c_8589])).

tff(c_8605,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8408,c_8603])).

tff(c_8607,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_314])).

tff(c_8713,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_8607,c_8696])).

tff(c_9385,plain,(
    ! [A_685,B_686,C_687] :
      ( k2_relset_1(A_685,B_686,C_687) = k2_relat_1(C_687)
      | ~ m1_subset_1(C_687,k1_zfmisc_1(k2_zfmisc_1(A_685,B_686))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_9401,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_96,c_9385])).

tff(c_9409,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_9401])).

tff(c_9305,plain,(
    ! [A_676] :
      ( k1_relat_1(k2_funct_1(A_676)) = k2_relat_1(A_676)
      | ~ v2_funct_1(A_676)
      | ~ v1_funct_1(A_676)
      | ~ v1_relat_1(A_676) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_13529,plain,(
    ! [A_947] :
      ( v1_funct_2(k2_funct_1(A_947),k2_relat_1(A_947),k2_relat_1(k2_funct_1(A_947)))
      | ~ v1_funct_1(k2_funct_1(A_947))
      | ~ v1_relat_1(k2_funct_1(A_947))
      | ~ v2_funct_1(A_947)
      | ~ v1_funct_1(A_947)
      | ~ v1_relat_1(A_947) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9305,c_74])).

tff(c_13559,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_9409,c_13529])).

tff(c_13583,plain,(
    v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8719,c_100,c_94,c_8713,c_315,c_13559])).

tff(c_13596,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k1_relat_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_13583])).

tff(c_13600,plain,(
    v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8719,c_100,c_94,c_13596])).

tff(c_9475,plain,(
    ! [A_693] :
      ( m1_subset_1(A_693,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_693),k2_relat_1(A_693))))
      | ~ v1_funct_1(A_693)
      | ~ v1_relat_1(A_693) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_14298,plain,(
    ! [A_980] :
      ( m1_subset_1(k2_funct_1(A_980),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_980),k2_relat_1(k2_funct_1(A_980)))))
      | ~ v1_funct_1(k2_funct_1(A_980))
      | ~ v1_relat_1(k2_funct_1(A_980))
      | ~ v2_funct_1(A_980)
      | ~ v1_funct_1(A_980)
      | ~ v1_relat_1(A_980) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_9475])).

tff(c_14346,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5')))))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_9409,c_14298])).

tff(c_14376,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8719,c_100,c_94,c_8713,c_315,c_14346])).

tff(c_14407,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_5'))))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_14376])).

tff(c_14421,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8719,c_100,c_94,c_14407])).

tff(c_9898,plain,(
    ! [B_718,D_719,A_720,C_721] :
      ( k1_xboole_0 = B_718
      | v1_funct_2(D_719,A_720,C_721)
      | ~ r1_tarski(B_718,C_721)
      | ~ m1_subset_1(D_719,k1_zfmisc_1(k2_zfmisc_1(A_720,B_718)))
      | ~ v1_funct_2(D_719,A_720,B_718)
      | ~ v1_funct_1(D_719) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_15071,plain,(
    ! [B_1012,D_1013,A_1014,A_1015] :
      ( k1_relat_1(B_1012) = k1_xboole_0
      | v1_funct_2(D_1013,A_1014,A_1015)
      | ~ m1_subset_1(D_1013,k1_zfmisc_1(k2_zfmisc_1(A_1014,k1_relat_1(B_1012))))
      | ~ v1_funct_2(D_1013,A_1014,k1_relat_1(B_1012))
      | ~ v1_funct_1(D_1013)
      | ~ v4_relat_1(B_1012,A_1015)
      | ~ v1_relat_1(B_1012) ) ),
    inference(resolution,[status(thm)],[c_20,c_9898])).

tff(c_15073,plain,(
    ! [A_1015] :
      ( k1_relat_1('#skF_5') = k1_xboole_0
      | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',A_1015)
      | ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k1_relat_1('#skF_5'))
      | ~ v1_funct_1(k2_funct_1('#skF_5'))
      | ~ v4_relat_1('#skF_5',A_1015)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_14421,c_15071])).

tff(c_15093,plain,(
    ! [A_1015] :
      ( k1_relat_1('#skF_5') = k1_xboole_0
      | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',A_1015)
      | ~ v4_relat_1('#skF_5',A_1015) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8719,c_315,c_13600,c_15073])).

tff(c_15107,plain,(
    ! [A_1016] :
      ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',A_1016)
      | ~ v4_relat_1('#skF_5',A_1016) ) ),
    inference(negUnitSimplification,[status(thm)],[c_8754,c_15093])).

tff(c_8606,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_314])).

tff(c_15110,plain,(
    ~ v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_15107,c_8606])).

tff(c_15114,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8950,c_15110])).

tff(c_15115,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_8734])).

tff(c_15127,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15115,c_15115,c_145])).

tff(c_16185,plain,(
    ! [A_1122,B_1123,C_1124] :
      ( k2_relset_1(A_1122,B_1123,C_1124) = k2_relat_1(C_1124)
      | ~ m1_subset_1(C_1124,k1_zfmisc_1(k2_zfmisc_1(A_1122,B_1123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_16201,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_96,c_16185])).

tff(c_16210,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_15127,c_16201])).

tff(c_15116,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8734])).

tff(c_15139,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15115,c_15116])).

tff(c_15653,plain,(
    ! [A_1066] :
      ( k2_relat_1(k2_funct_1(A_1066)) = k1_relat_1(A_1066)
      | ~ v2_funct_1(A_1066)
      | ~ v1_funct_1(A_1066)
      | ~ v1_relat_1(A_1066) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_8752,plain,
    ( k2_relat_1(k2_funct_1('#skF_5')) != k1_xboole_0
    | k2_funct_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8713,c_22])).

tff(c_15349,plain,
    ( k2_relat_1(k2_funct_1('#skF_5')) != '#skF_5'
    | k2_funct_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15115,c_15115,c_8752])).

tff(c_15350,plain,(
    k2_relat_1(k2_funct_1('#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_15349])).

tff(c_15662,plain,
    ( k1_relat_1('#skF_5') != '#skF_5'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_15653,c_15350])).

tff(c_15672,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8719,c_100,c_94,c_15139,c_15662])).

tff(c_15673,plain,(
    k2_funct_1('#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_15349])).

tff(c_8751,plain,
    ( k1_relat_1(k2_funct_1('#skF_5')) != k1_xboole_0
    | k2_funct_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8713,c_24])).

tff(c_15295,plain,
    ( k1_relat_1(k2_funct_1('#skF_5')) != '#skF_5'
    | k2_funct_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15115,c_15115,c_8751])).

tff(c_15296,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_15295])).

tff(c_15675,plain,(
    k1_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15673,c_15296])).

tff(c_15683,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15139,c_15675])).

tff(c_15684,plain,(
    k2_funct_1('#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_15295])).

tff(c_15689,plain,(
    ~ v1_funct_2('#skF_5','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15684,c_8606])).

tff(c_16223,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16210,c_15689])).

tff(c_16238,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16210,c_100])).

tff(c_208,plain,(
    ! [A_58] :
      ( k1_xboole_0 != A_58
      | k6_partfun1(A_58) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_194])).

tff(c_66,plain,(
    ! [A_39] : v1_partfun1(k6_partfun1(A_39),A_39) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_220,plain,(
    ! [A_58] :
      ( v1_partfun1(k1_xboole_0,A_58)
      | k1_xboole_0 != A_58 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_66])).

tff(c_15122,plain,(
    ! [A_58] :
      ( v1_partfun1('#skF_5',A_58)
      | A_58 != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15115,c_15115,c_220])).

tff(c_16600,plain,(
    v1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16210,c_16210,c_15122])).

tff(c_15688,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15684,c_8607])).

tff(c_16222,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16210,c_15688])).

tff(c_62,plain,(
    ! [C_38,A_36,B_37] :
      ( v1_funct_2(C_38,A_36,B_37)
      | ~ v1_partfun1(C_38,A_36)
      | ~ v1_funct_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_16636,plain,
    ( v1_funct_2('#skF_4','#skF_4','#skF_3')
    | ~ v1_partfun1('#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16222,c_62])).

tff(c_16654,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16238,c_16600,c_16636])).

tff(c_16656,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16223,c_16654])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:21:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.30/3.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.59/3.87  
% 10.59/3.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.59/3.87  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 10.59/3.87  
% 10.59/3.87  %Foreground sorts:
% 10.59/3.87  
% 10.59/3.87  
% 10.59/3.87  %Background operators:
% 10.59/3.87  
% 10.59/3.87  
% 10.59/3.87  %Foreground operators:
% 10.59/3.87  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.59/3.87  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.59/3.87  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 10.59/3.87  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.59/3.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.59/3.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.59/3.87  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.59/3.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.59/3.87  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 10.59/3.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.59/3.87  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.59/3.87  tff('#skF_5', type, '#skF_5': $i).
% 10.59/3.87  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.59/3.87  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 10.59/3.87  tff('#skF_3', type, '#skF_3': $i).
% 10.59/3.87  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.59/3.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.59/3.87  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 10.59/3.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.59/3.87  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.59/3.87  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.59/3.87  tff('#skF_4', type, '#skF_4': $i).
% 10.59/3.87  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 10.59/3.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.59/3.87  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.59/3.87  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.59/3.87  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.59/3.87  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.59/3.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.59/3.87  
% 10.65/3.90  tff(f_200, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 10.65/3.90  tff(f_134, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.65/3.90  tff(f_128, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.65/3.90  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 10.65/3.90  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 10.65/3.90  tff(f_107, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 10.65/3.90  tff(f_138, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.65/3.90  tff(f_164, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 10.65/3.90  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 10.65/3.90  tff(f_183, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_2)).
% 10.65/3.90  tff(f_154, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 10.65/3.90  tff(f_72, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 10.65/3.90  tff(f_67, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 10.65/3.90  tff(f_63, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 10.65/3.90  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 10.65/3.90  tff(f_84, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 10.65/3.90  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 10.65/3.90  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 10.65/3.90  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.65/3.90  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 10.65/3.90  tff(f_97, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((?[B]: ((v1_relat_1(B) & v1_funct_1(B)) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A))))) => v2_funct_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_funct_1)).
% 10.65/3.90  tff(f_124, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_funct_1)).
% 10.65/3.90  tff(f_152, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 10.65/3.90  tff(f_148, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 10.65/3.90  tff(c_92, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_200])).
% 10.65/3.90  tff(c_96, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_200])).
% 10.65/3.90  tff(c_8927, plain, (![C_638, A_639, B_640]: (v4_relat_1(C_638, A_639) | ~m1_subset_1(C_638, k1_zfmisc_1(k2_zfmisc_1(A_639, B_640))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.65/3.90  tff(c_8950, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_96, c_8927])).
% 10.65/3.90  tff(c_8696, plain, (![C_603, A_604, B_605]: (v1_relat_1(C_603) | ~m1_subset_1(C_603, k1_zfmisc_1(k2_zfmisc_1(A_604, B_605))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 10.65/3.90  tff(c_8719, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_96, c_8696])).
% 10.65/3.90  tff(c_24, plain, (![A_14]: (k1_relat_1(A_14)!=k1_xboole_0 | k1_xboole_0=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.65/3.90  tff(c_8734, plain, (k1_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_8719, c_24])).
% 10.65/3.90  tff(c_8754, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_8734])).
% 10.65/3.90  tff(c_100, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_200])).
% 10.65/3.90  tff(c_280, plain, (![A_66]: (v1_funct_1(k2_funct_1(A_66)) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.65/3.90  tff(c_90, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_200])).
% 10.65/3.90  tff(c_241, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_90])).
% 10.65/3.90  tff(c_283, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_280, c_241])).
% 10.65/3.90  tff(c_286, plain, (~v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_283])).
% 10.65/3.90  tff(c_291, plain, (![C_70, A_71, B_72]: (v1_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 10.65/3.90  tff(c_304, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_96, c_291])).
% 10.65/3.90  tff(c_313, plain, $false, inference(negUnitSimplification, [status(thm)], [c_286, c_304])).
% 10.65/3.90  tff(c_315, plain, (v1_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_90])).
% 10.65/3.90  tff(c_94, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_200])).
% 10.65/3.90  tff(c_48, plain, (![A_23]: (k2_relat_1(k2_funct_1(A_23))=k1_relat_1(A_23) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_107])).
% 10.65/3.90  tff(c_657, plain, (![C_116, A_117, B_118]: (v4_relat_1(C_116, A_117) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.65/3.90  tff(c_676, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_96, c_657])).
% 10.65/3.90  tff(c_447, plain, (![C_87, A_88, B_89]: (v1_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 10.65/3.90  tff(c_466, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_96, c_447])).
% 10.65/3.90  tff(c_481, plain, (k1_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_466, c_24])).
% 10.65/3.90  tff(c_511, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_481])).
% 10.65/3.90  tff(c_40, plain, (![A_18]: (v1_relat_1(k2_funct_1(A_18)) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.65/3.90  tff(c_864, plain, (![A_142, B_143, C_144]: (k2_relset_1(A_142, B_143, C_144)=k2_relat_1(C_144) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 10.65/3.90  tff(c_877, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_96, c_864])).
% 10.65/3.90  tff(c_884, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_877])).
% 10.65/3.90  tff(c_789, plain, (![A_131]: (k1_relat_1(k2_funct_1(A_131))=k2_relat_1(A_131) | ~v2_funct_1(A_131) | ~v1_funct_1(A_131) | ~v1_relat_1(A_131))), inference(cnfTransformation, [status(thm)], [f_107])).
% 10.65/3.90  tff(c_74, plain, (![A_41]: (v1_funct_2(A_41, k1_relat_1(A_41), k2_relat_1(A_41)) | ~v1_funct_1(A_41) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_164])).
% 10.65/3.90  tff(c_4702, plain, (![A_352]: (v1_funct_2(k2_funct_1(A_352), k2_relat_1(A_352), k2_relat_1(k2_funct_1(A_352))) | ~v1_funct_1(k2_funct_1(A_352)) | ~v1_relat_1(k2_funct_1(A_352)) | ~v2_funct_1(A_352) | ~v1_funct_1(A_352) | ~v1_relat_1(A_352))), inference(superposition, [status(thm), theory('equality')], [c_789, c_74])).
% 10.65/3.90  tff(c_4732, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_884, c_4702])).
% 10.65/3.90  tff(c_4756, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_466, c_100, c_94, c_315, c_4732])).
% 10.65/3.90  tff(c_4761, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_4756])).
% 10.65/3.90  tff(c_4770, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_4761])).
% 10.65/3.90  tff(c_4776, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_466, c_100, c_4770])).
% 10.65/3.90  tff(c_4777, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5')))), inference(splitRight, [status(thm)], [c_4756])).
% 10.65/3.90  tff(c_4856, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k1_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_48, c_4777])).
% 10.65/3.90  tff(c_4860, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_466, c_100, c_94, c_4856])).
% 10.65/3.90  tff(c_4778, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_4756])).
% 10.65/3.90  tff(c_50, plain, (![A_23]: (k1_relat_1(k2_funct_1(A_23))=k2_relat_1(A_23) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_107])).
% 10.65/3.90  tff(c_926, plain, (![A_146]: (m1_subset_1(A_146, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_146), k2_relat_1(A_146)))) | ~v1_funct_1(A_146) | ~v1_relat_1(A_146))), inference(cnfTransformation, [status(thm)], [f_164])).
% 10.65/3.90  tff(c_5288, plain, (![A_383]: (m1_subset_1(k2_funct_1(A_383), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_383), k2_relat_1(k2_funct_1(A_383))))) | ~v1_funct_1(k2_funct_1(A_383)) | ~v1_relat_1(k2_funct_1(A_383)) | ~v2_funct_1(A_383) | ~v1_funct_1(A_383) | ~v1_relat_1(A_383))), inference(superposition, [status(thm), theory('equality')], [c_50, c_926])).
% 10.65/3.90  tff(c_5336, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5'))))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_884, c_5288])).
% 10.65/3.90  tff(c_5366, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5')))))), inference(demodulation, [status(thm), theory('equality')], [c_466, c_100, c_94, c_4778, c_315, c_5336])).
% 10.65/3.90  tff(c_5397, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_5')))) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_48, c_5366])).
% 10.65/3.90  tff(c_5410, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_466, c_100, c_94, c_5397])).
% 10.65/3.90  tff(c_20, plain, (![B_13, A_12]: (r1_tarski(k1_relat_1(B_13), A_12) | ~v4_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.65/3.90  tff(c_1926, plain, (![B_214, D_215, A_216, C_217]: (k1_xboole_0=B_214 | m1_subset_1(D_215, k1_zfmisc_1(k2_zfmisc_1(A_216, C_217))) | ~r1_tarski(B_214, C_217) | ~m1_subset_1(D_215, k1_zfmisc_1(k2_zfmisc_1(A_216, B_214))) | ~v1_funct_2(D_215, A_216, B_214) | ~v1_funct_1(D_215))), inference(cnfTransformation, [status(thm)], [f_183])).
% 10.65/3.90  tff(c_6664, plain, (![B_458, D_459, A_460, A_461]: (k1_relat_1(B_458)=k1_xboole_0 | m1_subset_1(D_459, k1_zfmisc_1(k2_zfmisc_1(A_460, A_461))) | ~m1_subset_1(D_459, k1_zfmisc_1(k2_zfmisc_1(A_460, k1_relat_1(B_458)))) | ~v1_funct_2(D_459, A_460, k1_relat_1(B_458)) | ~v1_funct_1(D_459) | ~v4_relat_1(B_458, A_461) | ~v1_relat_1(B_458))), inference(resolution, [status(thm)], [c_20, c_1926])).
% 10.65/3.90  tff(c_6666, plain, (![A_461]: (k1_relat_1('#skF_5')=k1_xboole_0 | m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_461))) | ~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k1_relat_1('#skF_5')) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v4_relat_1('#skF_5', A_461) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_5410, c_6664])).
% 10.65/3.90  tff(c_6686, plain, (![A_461]: (k1_relat_1('#skF_5')=k1_xboole_0 | m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_461))) | ~v4_relat_1('#skF_5', A_461))), inference(demodulation, [status(thm), theory('equality')], [c_466, c_315, c_4860, c_6666])).
% 10.65/3.90  tff(c_6700, plain, (![A_462]: (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_462))) | ~v4_relat_1('#skF_5', A_462))), inference(negUnitSimplification, [status(thm)], [c_511, c_6686])).
% 10.65/3.90  tff(c_314, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_90])).
% 10.65/3.90  tff(c_358, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_314])).
% 10.65/3.90  tff(c_6740, plain, (~v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_6700, c_358])).
% 10.65/3.90  tff(c_6777, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_676, c_6740])).
% 10.65/3.90  tff(c_6778, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_481])).
% 10.65/3.90  tff(c_124, plain, (![A_50]: (k6_relat_1(A_50)=k6_partfun1(A_50))), inference(cnfTransformation, [status(thm)], [f_154])).
% 10.65/3.90  tff(c_36, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.65/3.90  tff(c_130, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_124, c_36])).
% 10.65/3.90  tff(c_70, plain, (![A_40]: (k6_relat_1(A_40)=k6_partfun1(A_40))), inference(cnfTransformation, [status(thm)], [f_154])).
% 10.65/3.90  tff(c_32, plain, (![A_16]: (k2_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.65/3.90  tff(c_106, plain, (![A_16]: (k2_relat_1(k6_partfun1(A_16))=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_70, c_32])).
% 10.65/3.90  tff(c_145, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_130, c_106])).
% 10.65/3.90  tff(c_6791, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_6778, c_6778, c_145])).
% 10.65/3.90  tff(c_26, plain, (![A_15]: (k1_relat_1(A_15)=k1_xboole_0 | k2_relat_1(A_15)!=k1_xboole_0 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.65/3.90  tff(c_479, plain, (k1_relat_1('#skF_5')=k1_xboole_0 | k2_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_466, c_26])).
% 10.65/3.90  tff(c_6802, plain, (k1_relat_1('#skF_5')='#skF_5' | k2_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_6778, c_6778, c_479])).
% 10.65/3.90  tff(c_6803, plain, (k2_relat_1('#skF_5')!='#skF_5'), inference(splitLeft, [status(thm)], [c_6802])).
% 10.65/3.90  tff(c_6835, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6791, c_6803])).
% 10.65/3.90  tff(c_6837, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_6802])).
% 10.65/3.90  tff(c_22, plain, (![A_14]: (k2_relat_1(A_14)!=k1_xboole_0 | k1_xboole_0=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.65/3.90  tff(c_482, plain, (k2_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_466, c_22])).
% 10.65/3.90  tff(c_489, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_482])).
% 10.65/3.90  tff(c_6780, plain, (k2_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_6778, c_489])).
% 10.65/3.90  tff(c_6888, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6837, c_6780])).
% 10.65/3.90  tff(c_6889, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_482])).
% 10.65/3.90  tff(c_6901, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_6889, c_6889, c_145])).
% 10.65/3.90  tff(c_7438, plain, (![A_514, B_515, C_516]: (k2_relset_1(A_514, B_515, C_516)=k2_relat_1(C_516) | ~m1_subset_1(C_516, k1_zfmisc_1(k2_zfmisc_1(A_514, B_515))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 10.65/3.90  tff(c_7454, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_96, c_7438])).
% 10.65/3.90  tff(c_7462, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6901, c_92, c_7454])).
% 10.65/3.90  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.65/3.90  tff(c_6905, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6889, c_12])).
% 10.65/3.90  tff(c_7482, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7462, c_6905])).
% 10.65/3.90  tff(c_42, plain, (![A_19]: (v1_relat_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.65/3.90  tff(c_104, plain, (![A_19]: (v1_relat_1(k6_partfun1(A_19)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_42])).
% 10.65/3.90  tff(c_188, plain, (![A_56]: (k2_relat_1(A_56)!=k1_xboole_0 | k1_xboole_0=A_56 | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.65/3.90  tff(c_194, plain, (![A_19]: (k2_relat_1(k6_partfun1(A_19))!=k1_xboole_0 | k6_partfun1(A_19)=k1_xboole_0)), inference(resolution, [status(thm)], [c_104, c_188])).
% 10.65/3.90  tff(c_200, plain, (![A_19]: (k1_xboole_0!=A_19 | k6_partfun1(A_19)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_106, c_194])).
% 10.65/3.90  tff(c_6897, plain, (![A_19]: (A_19!='#skF_5' | k6_partfun1(A_19)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6889, c_6889, c_200])).
% 10.65/3.90  tff(c_7476, plain, (![A_19]: (A_19!='#skF_4' | k6_partfun1(A_19)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7462, c_7462, c_6897])).
% 10.65/3.90  tff(c_437, plain, (![A_85, B_86]: (r2_hidden('#skF_2'(A_85, B_86), A_85) | r1_tarski(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.65/3.90  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.65/3.90  tff(c_446, plain, (![A_85, B_86]: (~v1_xboole_0(A_85) | r1_tarski(A_85, B_86))), inference(resolution, [status(thm)], [c_437, c_2])).
% 10.65/3.90  tff(c_16, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.65/3.90  tff(c_7147, plain, (![C_484, A_485, B_486]: (v4_relat_1(C_484, A_485) | ~m1_subset_1(C_484, k1_zfmisc_1(k2_zfmisc_1(A_485, B_486))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.65/3.90  tff(c_8241, plain, (![A_556, A_557, B_558]: (v4_relat_1(A_556, A_557) | ~r1_tarski(A_556, k2_zfmisc_1(A_557, B_558)))), inference(resolution, [status(thm)], [c_16, c_7147])).
% 10.65/3.90  tff(c_8277, plain, (![A_559, A_560]: (v4_relat_1(A_559, A_560) | ~v1_xboole_0(A_559))), inference(resolution, [status(thm)], [c_446, c_8241])).
% 10.65/3.90  tff(c_30, plain, (![A_16]: (k1_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.65/3.90  tff(c_107, plain, (![A_16]: (k1_relat_1(k6_partfun1(A_16))=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_70, c_30])).
% 10.65/3.90  tff(c_7069, plain, (![B_473, A_474]: (r1_tarski(k1_relat_1(B_473), A_474) | ~v4_relat_1(B_473, A_474) | ~v1_relat_1(B_473))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.65/3.90  tff(c_7078, plain, (![A_16, A_474]: (r1_tarski(A_16, A_474) | ~v4_relat_1(k6_partfun1(A_16), A_474) | ~v1_relat_1(k6_partfun1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_107, c_7069])).
% 10.65/3.90  tff(c_7083, plain, (![A_16, A_474]: (r1_tarski(A_16, A_474) | ~v4_relat_1(k6_partfun1(A_16), A_474))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_7078])).
% 10.65/3.90  tff(c_8368, plain, (![A_568, A_569]: (r1_tarski(A_568, A_569) | ~v1_xboole_0(k6_partfun1(A_568)))), inference(resolution, [status(thm)], [c_8277, c_7083])).
% 10.65/3.90  tff(c_8372, plain, (![A_19, A_569]: (r1_tarski(A_19, A_569) | ~v1_xboole_0('#skF_4') | A_19!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7476, c_8368])).
% 10.65/3.90  tff(c_8377, plain, (![A_570, A_571]: (r1_tarski(A_570, A_571) | A_570!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7482, c_8372])).
% 10.65/3.90  tff(c_362, plain, (~r1_tarski(k2_funct_1('#skF_5'), k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_358])).
% 10.65/3.90  tff(c_7486, plain, (~r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7462, c_362])).
% 10.65/3.90  tff(c_8408, plain, (k2_funct_1('#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_8377, c_7486])).
% 10.65/3.90  tff(c_44, plain, (![A_19]: (v1_funct_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.65/3.90  tff(c_103, plain, (![A_19]: (v1_funct_1(k6_partfun1(A_19)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_44])).
% 10.65/3.90  tff(c_34, plain, (![A_17]: (k5_relat_1(A_17, k6_relat_1(k2_relat_1(A_17)))=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.65/3.90  tff(c_396, plain, (![A_83]: (k5_relat_1(A_83, k6_partfun1(k2_relat_1(A_83)))=A_83 | ~v1_relat_1(A_83))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_34])).
% 10.65/3.90  tff(c_411, plain, (![A_16]: (k5_relat_1(k6_partfun1(A_16), k6_partfun1(A_16))=k6_partfun1(A_16) | ~v1_relat_1(k6_partfun1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_106, c_396])).
% 10.65/3.90  tff(c_417, plain, (![A_16]: (k5_relat_1(k6_partfun1(A_16), k6_partfun1(A_16))=k6_partfun1(A_16))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_411])).
% 10.65/3.90  tff(c_46, plain, (![A_20, B_22]: (v2_funct_1(A_20) | k6_relat_1(k1_relat_1(A_20))!=k5_relat_1(A_20, B_22) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.65/3.90  tff(c_7635, plain, (![A_520, B_521]: (v2_funct_1(A_520) | k6_partfun1(k1_relat_1(A_520))!=k5_relat_1(A_520, B_521) | ~v1_funct_1(B_521) | ~v1_relat_1(B_521) | ~v1_funct_1(A_520) | ~v1_relat_1(A_520))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_46])).
% 10.65/3.90  tff(c_7641, plain, (![A_16]: (v2_funct_1(k6_partfun1(A_16)) | k6_partfun1(k1_relat_1(k6_partfun1(A_16)))!=k6_partfun1(A_16) | ~v1_funct_1(k6_partfun1(A_16)) | ~v1_relat_1(k6_partfun1(A_16)) | ~v1_funct_1(k6_partfun1(A_16)) | ~v1_relat_1(k6_partfun1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_417, c_7635])).
% 10.65/3.90  tff(c_7649, plain, (![A_16]: (v2_funct_1(k6_partfun1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_103, c_104, c_103, c_107, c_7641])).
% 10.65/3.90  tff(c_52, plain, (![A_24, B_26]: (k2_funct_1(A_24)=B_26 | k6_relat_1(k1_relat_1(A_24))!=k5_relat_1(A_24, B_26) | k2_relat_1(A_24)!=k1_relat_1(B_26) | ~v2_funct_1(A_24) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_124])).
% 10.65/3.90  tff(c_7991, plain, (![A_543, B_544]: (k2_funct_1(A_543)=B_544 | k6_partfun1(k1_relat_1(A_543))!=k5_relat_1(A_543, B_544) | k2_relat_1(A_543)!=k1_relat_1(B_544) | ~v2_funct_1(A_543) | ~v1_funct_1(B_544) | ~v1_relat_1(B_544) | ~v1_funct_1(A_543) | ~v1_relat_1(A_543))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_52])).
% 10.65/3.90  tff(c_8000, plain, (![A_16]: (k2_funct_1(k6_partfun1(A_16))=k6_partfun1(A_16) | k6_partfun1(k1_relat_1(k6_partfun1(A_16)))!=k6_partfun1(A_16) | k2_relat_1(k6_partfun1(A_16))!=k1_relat_1(k6_partfun1(A_16)) | ~v2_funct_1(k6_partfun1(A_16)) | ~v1_funct_1(k6_partfun1(A_16)) | ~v1_relat_1(k6_partfun1(A_16)) | ~v1_funct_1(k6_partfun1(A_16)) | ~v1_relat_1(k6_partfun1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_417, c_7991])).
% 10.65/3.90  tff(c_8013, plain, (![A_545]: (k2_funct_1(k6_partfun1(A_545))=k6_partfun1(A_545))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_103, c_104, c_103, c_7649, c_106, c_107, c_107, c_8000])).
% 10.65/3.90  tff(c_8046, plain, (![A_546]: (k6_partfun1(A_546)=k2_funct_1('#skF_4') | A_546!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7476, c_8013])).
% 10.65/3.90  tff(c_8207, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_8046, c_107])).
% 10.65/3.90  tff(c_8107, plain, (![A_546]: (v1_relat_1(k2_funct_1('#skF_4')) | A_546!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8046, c_104])).
% 10.65/3.90  tff(c_8157, plain, (![A_546]: (A_546!='#skF_4')), inference(splitLeft, [status(thm)], [c_8107])).
% 10.65/3.90  tff(c_184, plain, (![A_55]: (m1_subset_1(k6_partfun1(A_55), k1_zfmisc_1(k2_zfmisc_1(A_55, A_55))))), inference(cnfTransformation, [status(thm)], [f_152])).
% 10.65/3.90  tff(c_187, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_130, c_184])).
% 10.65/3.90  tff(c_6899, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_6889, c_6889, c_6889, c_187])).
% 10.65/3.90  tff(c_7444, plain, (k2_relset_1('#skF_5', '#skF_5', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_6899, c_7438])).
% 10.65/3.90  tff(c_7457, plain, (k2_relset_1('#skF_5', '#skF_5', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_6901, c_7444])).
% 10.65/3.90  tff(c_7797, plain, (k2_relset_1('#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7462, c_7462, c_7462, c_7462, c_7457])).
% 10.65/3.90  tff(c_8168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8157, c_7797])).
% 10.65/3.90  tff(c_8169, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_8107])).
% 10.65/3.90  tff(c_6895, plain, (![A_14]: (k1_relat_1(A_14)!='#skF_5' | A_14='#skF_5' | ~v1_relat_1(A_14))), inference(demodulation, [status(thm), theory('equality')], [c_6889, c_6889, c_24])).
% 10.65/3.90  tff(c_8580, plain, (![A_594]: (k1_relat_1(A_594)!='#skF_4' | A_594='#skF_4' | ~v1_relat_1(A_594))), inference(demodulation, [status(thm), theory('equality')], [c_7462, c_7462, c_6895])).
% 10.65/3.90  tff(c_8589, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4' | k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_8169, c_8580])).
% 10.65/3.90  tff(c_8603, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8207, c_8589])).
% 10.65/3.90  tff(c_8605, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8408, c_8603])).
% 10.65/3.90  tff(c_8607, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_314])).
% 10.65/3.90  tff(c_8713, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_8607, c_8696])).
% 10.65/3.90  tff(c_9385, plain, (![A_685, B_686, C_687]: (k2_relset_1(A_685, B_686, C_687)=k2_relat_1(C_687) | ~m1_subset_1(C_687, k1_zfmisc_1(k2_zfmisc_1(A_685, B_686))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 10.65/3.90  tff(c_9401, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_96, c_9385])).
% 10.65/3.90  tff(c_9409, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_9401])).
% 10.65/3.90  tff(c_9305, plain, (![A_676]: (k1_relat_1(k2_funct_1(A_676))=k2_relat_1(A_676) | ~v2_funct_1(A_676) | ~v1_funct_1(A_676) | ~v1_relat_1(A_676))), inference(cnfTransformation, [status(thm)], [f_107])).
% 10.65/3.90  tff(c_13529, plain, (![A_947]: (v1_funct_2(k2_funct_1(A_947), k2_relat_1(A_947), k2_relat_1(k2_funct_1(A_947))) | ~v1_funct_1(k2_funct_1(A_947)) | ~v1_relat_1(k2_funct_1(A_947)) | ~v2_funct_1(A_947) | ~v1_funct_1(A_947) | ~v1_relat_1(A_947))), inference(superposition, [status(thm), theory('equality')], [c_9305, c_74])).
% 10.65/3.90  tff(c_13559, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_9409, c_13529])).
% 10.65/3.90  tff(c_13583, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_8719, c_100, c_94, c_8713, c_315, c_13559])).
% 10.65/3.90  tff(c_13596, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k1_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_48, c_13583])).
% 10.65/3.90  tff(c_13600, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_8719, c_100, c_94, c_13596])).
% 10.65/3.90  tff(c_9475, plain, (![A_693]: (m1_subset_1(A_693, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_693), k2_relat_1(A_693)))) | ~v1_funct_1(A_693) | ~v1_relat_1(A_693))), inference(cnfTransformation, [status(thm)], [f_164])).
% 10.65/3.90  tff(c_14298, plain, (![A_980]: (m1_subset_1(k2_funct_1(A_980), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_980), k2_relat_1(k2_funct_1(A_980))))) | ~v1_funct_1(k2_funct_1(A_980)) | ~v1_relat_1(k2_funct_1(A_980)) | ~v2_funct_1(A_980) | ~v1_funct_1(A_980) | ~v1_relat_1(A_980))), inference(superposition, [status(thm), theory('equality')], [c_50, c_9475])).
% 10.65/3.90  tff(c_14346, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5'))))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_9409, c_14298])).
% 10.65/3.90  tff(c_14376, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5')))))), inference(demodulation, [status(thm), theory('equality')], [c_8719, c_100, c_94, c_8713, c_315, c_14346])).
% 10.65/3.90  tff(c_14407, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_5')))) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_48, c_14376])).
% 10.65/3.90  tff(c_14421, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_8719, c_100, c_94, c_14407])).
% 10.65/3.90  tff(c_9898, plain, (![B_718, D_719, A_720, C_721]: (k1_xboole_0=B_718 | v1_funct_2(D_719, A_720, C_721) | ~r1_tarski(B_718, C_721) | ~m1_subset_1(D_719, k1_zfmisc_1(k2_zfmisc_1(A_720, B_718))) | ~v1_funct_2(D_719, A_720, B_718) | ~v1_funct_1(D_719))), inference(cnfTransformation, [status(thm)], [f_183])).
% 10.65/3.90  tff(c_15071, plain, (![B_1012, D_1013, A_1014, A_1015]: (k1_relat_1(B_1012)=k1_xboole_0 | v1_funct_2(D_1013, A_1014, A_1015) | ~m1_subset_1(D_1013, k1_zfmisc_1(k2_zfmisc_1(A_1014, k1_relat_1(B_1012)))) | ~v1_funct_2(D_1013, A_1014, k1_relat_1(B_1012)) | ~v1_funct_1(D_1013) | ~v4_relat_1(B_1012, A_1015) | ~v1_relat_1(B_1012))), inference(resolution, [status(thm)], [c_20, c_9898])).
% 10.65/3.90  tff(c_15073, plain, (![A_1015]: (k1_relat_1('#skF_5')=k1_xboole_0 | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', A_1015) | ~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k1_relat_1('#skF_5')) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v4_relat_1('#skF_5', A_1015) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_14421, c_15071])).
% 10.65/3.90  tff(c_15093, plain, (![A_1015]: (k1_relat_1('#skF_5')=k1_xboole_0 | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', A_1015) | ~v4_relat_1('#skF_5', A_1015))), inference(demodulation, [status(thm), theory('equality')], [c_8719, c_315, c_13600, c_15073])).
% 10.65/3.90  tff(c_15107, plain, (![A_1016]: (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', A_1016) | ~v4_relat_1('#skF_5', A_1016))), inference(negUnitSimplification, [status(thm)], [c_8754, c_15093])).
% 10.65/3.90  tff(c_8606, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_314])).
% 10.65/3.90  tff(c_15110, plain, (~v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_15107, c_8606])).
% 10.65/3.90  tff(c_15114, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8950, c_15110])).
% 10.65/3.90  tff(c_15115, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_8734])).
% 10.65/3.90  tff(c_15127, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_15115, c_15115, c_145])).
% 10.65/3.90  tff(c_16185, plain, (![A_1122, B_1123, C_1124]: (k2_relset_1(A_1122, B_1123, C_1124)=k2_relat_1(C_1124) | ~m1_subset_1(C_1124, k1_zfmisc_1(k2_zfmisc_1(A_1122, B_1123))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 10.65/3.90  tff(c_16201, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_96, c_16185])).
% 10.65/3.90  tff(c_16210, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_15127, c_16201])).
% 10.65/3.90  tff(c_15116, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_8734])).
% 10.65/3.90  tff(c_15139, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_15115, c_15116])).
% 10.65/3.90  tff(c_15653, plain, (![A_1066]: (k2_relat_1(k2_funct_1(A_1066))=k1_relat_1(A_1066) | ~v2_funct_1(A_1066) | ~v1_funct_1(A_1066) | ~v1_relat_1(A_1066))), inference(cnfTransformation, [status(thm)], [f_107])).
% 10.65/3.90  tff(c_8752, plain, (k2_relat_1(k2_funct_1('#skF_5'))!=k1_xboole_0 | k2_funct_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_8713, c_22])).
% 10.65/3.90  tff(c_15349, plain, (k2_relat_1(k2_funct_1('#skF_5'))!='#skF_5' | k2_funct_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_15115, c_15115, c_8752])).
% 10.65/3.90  tff(c_15350, plain, (k2_relat_1(k2_funct_1('#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_15349])).
% 10.65/3.90  tff(c_15662, plain, (k1_relat_1('#skF_5')!='#skF_5' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_15653, c_15350])).
% 10.65/3.90  tff(c_15672, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8719, c_100, c_94, c_15139, c_15662])).
% 10.65/3.90  tff(c_15673, plain, (k2_funct_1('#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_15349])).
% 10.65/3.90  tff(c_8751, plain, (k1_relat_1(k2_funct_1('#skF_5'))!=k1_xboole_0 | k2_funct_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_8713, c_24])).
% 10.65/3.90  tff(c_15295, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_5' | k2_funct_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_15115, c_15115, c_8751])).
% 10.65/3.90  tff(c_15296, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_15295])).
% 10.65/3.90  tff(c_15675, plain, (k1_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_15673, c_15296])).
% 10.65/3.90  tff(c_15683, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15139, c_15675])).
% 10.65/3.90  tff(c_15684, plain, (k2_funct_1('#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_15295])).
% 10.65/3.90  tff(c_15689, plain, (~v1_funct_2('#skF_5', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15684, c_8606])).
% 10.65/3.90  tff(c_16223, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16210, c_15689])).
% 10.65/3.90  tff(c_16238, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16210, c_100])).
% 10.65/3.90  tff(c_208, plain, (![A_58]: (k1_xboole_0!=A_58 | k6_partfun1(A_58)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_106, c_194])).
% 10.65/3.90  tff(c_66, plain, (![A_39]: (v1_partfun1(k6_partfun1(A_39), A_39))), inference(cnfTransformation, [status(thm)], [f_152])).
% 10.65/3.90  tff(c_220, plain, (![A_58]: (v1_partfun1(k1_xboole_0, A_58) | k1_xboole_0!=A_58)), inference(superposition, [status(thm), theory('equality')], [c_208, c_66])).
% 10.65/3.90  tff(c_15122, plain, (![A_58]: (v1_partfun1('#skF_5', A_58) | A_58!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_15115, c_15115, c_220])).
% 10.65/3.90  tff(c_16600, plain, (v1_partfun1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16210, c_16210, c_15122])).
% 10.65/3.90  tff(c_15688, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_15684, c_8607])).
% 10.65/3.90  tff(c_16222, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_16210, c_15688])).
% 10.65/3.90  tff(c_62, plain, (![C_38, A_36, B_37]: (v1_funct_2(C_38, A_36, B_37) | ~v1_partfun1(C_38, A_36) | ~v1_funct_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 10.65/3.90  tff(c_16636, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_3') | ~v1_partfun1('#skF_4', '#skF_4') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_16222, c_62])).
% 10.65/3.90  tff(c_16654, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16238, c_16600, c_16636])).
% 10.65/3.90  tff(c_16656, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16223, c_16654])).
% 10.65/3.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.65/3.90  
% 10.65/3.90  Inference rules
% 10.65/3.90  ----------------------
% 10.65/3.90  #Ref     : 9
% 10.65/3.90  #Sup     : 3573
% 10.65/3.90  #Fact    : 0
% 10.65/3.90  #Define  : 0
% 10.65/3.90  #Split   : 64
% 10.65/3.90  #Chain   : 0
% 10.65/3.90  #Close   : 0
% 10.65/3.90  
% 10.65/3.90  Ordering : KBO
% 10.65/3.90  
% 10.65/3.90  Simplification rules
% 10.65/3.90  ----------------------
% 10.65/3.90  #Subsume      : 2393
% 10.65/3.90  #Demod        : 3704
% 10.65/3.90  #Tautology    : 1229
% 10.65/3.90  #SimpNegUnit  : 733
% 10.65/3.90  #BackRed      : 535
% 10.65/3.90  
% 10.65/3.90  #Partial instantiations: 0
% 10.65/3.90  #Strategies tried      : 1
% 10.65/3.90  
% 10.65/3.90  Timing (in seconds)
% 10.65/3.90  ----------------------
% 10.65/3.91  Preprocessing        : 0.38
% 10.65/3.91  Parsing              : 0.21
% 10.65/3.91  CNF conversion       : 0.03
% 10.65/3.91  Main loop            : 2.66
% 10.65/3.91  Inferencing          : 0.76
% 10.65/3.91  Reduction            : 1.02
% 10.65/3.91  Demodulation         : 0.74
% 10.65/3.91  BG Simplification    : 0.08
% 10.65/3.91  Subsumption          : 0.60
% 10.65/3.91  Abstraction          : 0.09
% 10.65/3.91  MUC search           : 0.00
% 10.65/3.91  Cooper               : 0.00
% 10.65/3.91  Total                : 3.12
% 10.65/3.91  Index Insertion      : 0.00
% 10.65/3.91  Index Deletion       : 0.00
% 10.65/3.91  Index Matching       : 0.00
% 10.65/3.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
