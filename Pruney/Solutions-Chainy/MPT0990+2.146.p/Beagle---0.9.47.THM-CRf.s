%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:17 EST 2020

% Result     : Theorem 11.24s
% Output     : CNFRefutation 11.51s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 925 expanded)
%              Number of leaves         :   46 ( 346 expanded)
%              Depth                    :   17
%              Number of atoms          :  421 (3717 expanded)
%              Number of equality atoms :  134 (1220 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_281,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( ( k2_relset_1(A,B,C) = B
                & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
                & v2_funct_1(C) )
             => ( A = k1_xboole_0
                | B = k1_xboole_0
                | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_148,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_178,axiom,(
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

tff(f_107,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_206,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_204,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_194,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_160,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_190,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_255,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_152,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_97,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & k2_relat_1(B) = k1_relat_1(A) )
           => ( v2_funct_1(B)
              & v2_funct_1(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_239,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_223,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
           => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

tff(c_96,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_108,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_210,plain,(
    ! [B_83,A_84] :
      ( v1_relat_1(B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_84))
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_219,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_108,c_210])).

tff(c_228,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_219])).

tff(c_114,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_216,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_114,c_210])).

tff(c_225,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_216])).

tff(c_118,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_16,plain,(
    ! [A_15] :
      ( v1_relat_1(k2_funct_1(A_15))
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_102,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_98,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_116,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_277,plain,(
    ! [A_92,B_93,C_94] :
      ( k1_relset_1(A_92,B_93,C_94) = k1_relat_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_289,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_277])).

tff(c_746,plain,(
    ! [B_125,A_126,C_127] :
      ( k1_xboole_0 = B_125
      | k1_relset_1(A_126,B_125,C_127) = A_126
      | ~ v1_funct_2(C_127,A_126,B_125)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_126,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_752,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_114,c_746])).

tff(c_760,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_289,c_752])).

tff(c_761,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_760])).

tff(c_235,plain,(
    ! [A_86] :
      ( k2_relat_1(k2_funct_1(A_86)) = k1_relat_1(A_86)
      | ~ v2_funct_1(A_86)
      | ~ v1_funct_1(A_86)
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_82,plain,(
    ! [A_55] : k6_relat_1(A_55) = k6_partfun1(A_55) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_12,plain,(
    ! [A_14] :
      ( k5_relat_1(A_14,k6_relat_1(k2_relat_1(A_14))) = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_126,plain,(
    ! [A_14] :
      ( k5_relat_1(A_14,k6_partfun1(k2_relat_1(A_14))) = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_12])).

tff(c_831,plain,(
    ! [A_130] :
      ( k5_relat_1(k2_funct_1(A_130),k6_partfun1(k1_relat_1(A_130))) = k2_funct_1(A_130)
      | ~ v1_relat_1(k2_funct_1(A_130))
      | ~ v2_funct_1(A_130)
      | ~ v1_funct_1(A_130)
      | ~ v1_relat_1(A_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_126])).

tff(c_849,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_761,c_831])).

tff(c_871,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_118,c_102,c_849])).

tff(c_876,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_871])).

tff(c_880,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_876])).

tff(c_884,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_118,c_880])).

tff(c_885,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_871])).

tff(c_112,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_11339,plain,(
    ! [E_577,C_576,F_579,D_581,A_580,B_578] :
      ( k1_partfun1(A_580,B_578,C_576,D_581,E_577,F_579) = k5_relat_1(E_577,F_579)
      | ~ m1_subset_1(F_579,k1_zfmisc_1(k2_zfmisc_1(C_576,D_581)))
      | ~ v1_funct_1(F_579)
      | ~ m1_subset_1(E_577,k1_zfmisc_1(k2_zfmisc_1(A_580,B_578)))
      | ~ v1_funct_1(E_577) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_11345,plain,(
    ! [A_580,B_578,E_577] :
      ( k1_partfun1(A_580,B_578,'#skF_2','#skF_1',E_577,'#skF_4') = k5_relat_1(E_577,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_577,k1_zfmisc_1(k2_zfmisc_1(A_580,B_578)))
      | ~ v1_funct_1(E_577) ) ),
    inference(resolution,[status(thm)],[c_108,c_11339])).

tff(c_11591,plain,(
    ! [A_595,B_596,E_597] :
      ( k1_partfun1(A_595,B_596,'#skF_2','#skF_1',E_597,'#skF_4') = k5_relat_1(E_597,'#skF_4')
      | ~ m1_subset_1(E_597,k1_zfmisc_1(k2_zfmisc_1(A_595,B_596)))
      | ~ v1_funct_1(E_597) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_11345])).

tff(c_11600,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_11591])).

tff(c_11610,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_11600])).

tff(c_78,plain,(
    ! [A_48] : m1_subset_1(k6_partfun1(A_48),k1_zfmisc_1(k2_zfmisc_1(A_48,A_48))) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_104,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_8820,plain,(
    ! [D_468,C_469,A_470,B_471] :
      ( D_468 = C_469
      | ~ r2_relset_1(A_470,B_471,C_469,D_468)
      | ~ m1_subset_1(D_468,k1_zfmisc_1(k2_zfmisc_1(A_470,B_471)))
      | ~ m1_subset_1(C_469,k1_zfmisc_1(k2_zfmisc_1(A_470,B_471))) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_8828,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_104,c_8820])).

tff(c_8843,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_8828])).

tff(c_9204,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_8843])).

tff(c_11615,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11610,c_9204])).

tff(c_11995,plain,(
    ! [F_617,A_616,B_615,D_614,C_618,E_613] :
      ( m1_subset_1(k1_partfun1(A_616,B_615,C_618,D_614,E_613,F_617),k1_zfmisc_1(k2_zfmisc_1(A_616,D_614)))
      | ~ m1_subset_1(F_617,k1_zfmisc_1(k2_zfmisc_1(C_618,D_614)))
      | ~ v1_funct_1(F_617)
      | ~ m1_subset_1(E_613,k1_zfmisc_1(k2_zfmisc_1(A_616,B_615)))
      | ~ v1_funct_1(E_613) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_12065,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_11610,c_11995])).

tff(c_12096,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_114,c_112,c_108,c_12065])).

tff(c_12098,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11615,c_12096])).

tff(c_12099,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_8843])).

tff(c_18300,plain,(
    ! [D_889,F_887,E_885,A_888,C_884,B_886] :
      ( k1_partfun1(A_888,B_886,C_884,D_889,E_885,F_887) = k5_relat_1(E_885,F_887)
      | ~ m1_subset_1(F_887,k1_zfmisc_1(k2_zfmisc_1(C_884,D_889)))
      | ~ v1_funct_1(F_887)
      | ~ m1_subset_1(E_885,k1_zfmisc_1(k2_zfmisc_1(A_888,B_886)))
      | ~ v1_funct_1(E_885) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_18308,plain,(
    ! [A_888,B_886,E_885] :
      ( k1_partfun1(A_888,B_886,'#skF_2','#skF_1',E_885,'#skF_4') = k5_relat_1(E_885,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_885,k1_zfmisc_1(k2_zfmisc_1(A_888,B_886)))
      | ~ v1_funct_1(E_885) ) ),
    inference(resolution,[status(thm)],[c_108,c_18300])).

tff(c_18363,plain,(
    ! [A_895,B_896,E_897] :
      ( k1_partfun1(A_895,B_896,'#skF_2','#skF_1',E_897,'#skF_4') = k5_relat_1(E_897,'#skF_4')
      | ~ m1_subset_1(E_897,k1_zfmisc_1(k2_zfmisc_1(A_895,B_896)))
      | ~ v1_funct_1(E_897) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_18308])).

tff(c_18372,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_18363])).

tff(c_18382,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_12099,c_18372])).

tff(c_886,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_871])).

tff(c_106,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_18964,plain,(
    ! [B_906,C_907,A_908] :
      ( k6_partfun1(B_906) = k5_relat_1(k2_funct_1(C_907),C_907)
      | k1_xboole_0 = B_906
      | ~ v2_funct_1(C_907)
      | k2_relset_1(A_908,B_906,C_907) != B_906
      | ~ m1_subset_1(C_907,k1_zfmisc_1(k2_zfmisc_1(A_908,B_906)))
      | ~ v1_funct_2(C_907,A_908,B_906)
      | ~ v1_funct_1(C_907) ) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_18970,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_18964])).

tff(c_18979,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_116,c_106,c_102,c_18970])).

tff(c_18980,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_18979])).

tff(c_6,plain,(
    ! [A_6,B_10,C_12] :
      ( k5_relat_1(k5_relat_1(A_6,B_10),C_12) = k5_relat_1(A_6,k5_relat_1(B_10,C_12))
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_19055,plain,(
    ! [C_12] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_12)) = k5_relat_1(k6_partfun1('#skF_2'),C_12)
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18980,c_6])).

tff(c_19113,plain,(
    ! [C_909] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_909)) = k5_relat_1(k6_partfun1('#skF_2'),C_909)
      | ~ v1_relat_1(C_909) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_886,c_225,c_19055])).

tff(c_19147,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_18382,c_19113])).

tff(c_19192,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_885,c_19147])).

tff(c_110,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_100,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_290,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_108,c_277])).

tff(c_755,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_108,c_746])).

tff(c_764,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_290,c_755])).

tff(c_765,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_764])).

tff(c_846,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),k6_partfun1('#skF_2')) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_765,c_831])).

tff(c_869,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),k6_partfun1('#skF_2')) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_112,c_846])).

tff(c_901,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_869])).

tff(c_24,plain,(
    ! [A_17] : v2_funct_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_122,plain,(
    ! [A_17] : v2_funct_1(k6_partfun1(A_17)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_24])).

tff(c_309,plain,(
    ! [A_97,B_98,C_99] :
      ( k2_relset_1(A_97,B_98,C_99) = k2_relat_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_315,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_309])).

tff(c_322,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_315])).

tff(c_5434,plain,(
    ! [E_339,A_342,C_338,D_343,F_341,B_340] :
      ( k1_partfun1(A_342,B_340,C_338,D_343,E_339,F_341) = k5_relat_1(E_339,F_341)
      | ~ m1_subset_1(F_341,k1_zfmisc_1(k2_zfmisc_1(C_338,D_343)))
      | ~ v1_funct_1(F_341)
      | ~ m1_subset_1(E_339,k1_zfmisc_1(k2_zfmisc_1(A_342,B_340)))
      | ~ v1_funct_1(E_339) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_5440,plain,(
    ! [A_342,B_340,E_339] :
      ( k1_partfun1(A_342,B_340,'#skF_2','#skF_1',E_339,'#skF_4') = k5_relat_1(E_339,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_339,k1_zfmisc_1(k2_zfmisc_1(A_342,B_340)))
      | ~ v1_funct_1(E_339) ) ),
    inference(resolution,[status(thm)],[c_108,c_5434])).

tff(c_5618,plain,(
    ! [A_364,B_365,E_366] :
      ( k1_partfun1(A_364,B_365,'#skF_2','#skF_1',E_366,'#skF_4') = k5_relat_1(E_366,'#skF_4')
      | ~ m1_subset_1(E_366,k1_zfmisc_1(k2_zfmisc_1(A_364,B_365)))
      | ~ v1_funct_1(E_366) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_5440])).

tff(c_5627,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_5618])).

tff(c_5637,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_5627])).

tff(c_1012,plain,(
    ! [D_134,C_135,A_136,B_137] :
      ( D_134 = C_135
      | ~ r2_relset_1(A_136,B_137,C_135,D_134)
      | ~ m1_subset_1(D_134,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137)))
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1020,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_104,c_1012])).

tff(c_1035,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1020])).

tff(c_1036,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1035])).

tff(c_5642,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5637,c_1036])).

tff(c_6282,plain,(
    ! [B_380,D_379,A_381,C_383,E_378,F_382] :
      ( m1_subset_1(k1_partfun1(A_381,B_380,C_383,D_379,E_378,F_382),k1_zfmisc_1(k2_zfmisc_1(A_381,D_379)))
      | ~ m1_subset_1(F_382,k1_zfmisc_1(k2_zfmisc_1(C_383,D_379)))
      | ~ v1_funct_1(F_382)
      | ~ m1_subset_1(E_378,k1_zfmisc_1(k2_zfmisc_1(A_381,B_380)))
      | ~ v1_funct_1(E_378) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_6348,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5637,c_6282])).

tff(c_6385,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_114,c_112,c_108,c_6348])).

tff(c_6387,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5642,c_6385])).

tff(c_6388,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1035])).

tff(c_8509,plain,(
    ! [F_453,A_454,C_450,D_455,E_451,B_452] :
      ( k1_partfun1(A_454,B_452,C_450,D_455,E_451,F_453) = k5_relat_1(E_451,F_453)
      | ~ m1_subset_1(F_453,k1_zfmisc_1(k2_zfmisc_1(C_450,D_455)))
      | ~ v1_funct_1(F_453)
      | ~ m1_subset_1(E_451,k1_zfmisc_1(k2_zfmisc_1(A_454,B_452)))
      | ~ v1_funct_1(E_451) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_8517,plain,(
    ! [A_454,B_452,E_451] :
      ( k1_partfun1(A_454,B_452,'#skF_2','#skF_1',E_451,'#skF_4') = k5_relat_1(E_451,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_451,k1_zfmisc_1(k2_zfmisc_1(A_454,B_452)))
      | ~ v1_funct_1(E_451) ) ),
    inference(resolution,[status(thm)],[c_108,c_8509])).

tff(c_8572,plain,(
    ! [A_461,B_462,E_463] :
      ( k1_partfun1(A_461,B_462,'#skF_2','#skF_1',E_463,'#skF_4') = k5_relat_1(E_463,'#skF_4')
      | ~ m1_subset_1(E_463,k1_zfmisc_1(k2_zfmisc_1(A_461,B_462)))
      | ~ v1_funct_1(E_463) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_8517])).

tff(c_8581,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_8572])).

tff(c_8591,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_6388,c_8581])).

tff(c_32,plain,(
    ! [A_19,B_21] :
      ( v2_funct_1(A_19)
      | k2_relat_1(B_21) != k1_relat_1(A_19)
      | ~ v2_funct_1(k5_relat_1(B_21,A_19))
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_8607,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8591,c_32])).

tff(c_8623,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_112,c_225,c_118,c_122,c_322,c_765,c_8607])).

tff(c_8625,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_901,c_8623])).

tff(c_8627,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_869])).

tff(c_323,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_108,c_309])).

tff(c_12526,plain,(
    ! [C_623,A_624,B_625] :
      ( v1_funct_1(k2_funct_1(C_623))
      | k2_relset_1(A_624,B_625,C_623) != B_625
      | ~ v2_funct_1(C_623)
      | ~ m1_subset_1(C_623,k1_zfmisc_1(k2_zfmisc_1(A_624,B_625)))
      | ~ v1_funct_2(C_623,A_624,B_625)
      | ~ v1_funct_1(C_623) ) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_12535,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_108,c_12526])).

tff(c_12544,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_110,c_8627,c_323,c_12535])).

tff(c_12545,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_12544])).

tff(c_252,plain,(
    ! [A_87,B_88,D_89] :
      ( r2_relset_1(A_87,B_88,D_89,D_89)
      | ~ m1_subset_1(D_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_259,plain,(
    ! [A_48] : r2_relset_1(A_48,A_48,k6_partfun1(A_48),k6_partfun1(A_48)) ),
    inference(resolution,[status(thm)],[c_78,c_252])).

tff(c_17489,plain,(
    ! [A_839,B_840,C_841,D_842] :
      ( k2_relset_1(A_839,B_840,C_841) = B_840
      | ~ r2_relset_1(B_840,B_840,k1_partfun1(B_840,A_839,A_839,B_840,D_842,C_841),k6_partfun1(B_840))
      | ~ m1_subset_1(D_842,k1_zfmisc_1(k2_zfmisc_1(B_840,A_839)))
      | ~ v1_funct_2(D_842,B_840,A_839)
      | ~ v1_funct_1(D_842)
      | ~ m1_subset_1(C_841,k1_zfmisc_1(k2_zfmisc_1(A_839,B_840)))
      | ~ v1_funct_2(C_841,A_839,B_840)
      | ~ v1_funct_1(C_841) ) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_17495,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12099,c_17489])).

tff(c_17499,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_110,c_108,c_118,c_116,c_114,c_259,c_323,c_17495])).

tff(c_17501,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12545,c_17499])).

tff(c_17503,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_12544])).

tff(c_17511,plain,
    ( k5_relat_1('#skF_4',k6_partfun1('#skF_1')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_17503,c_126])).

tff(c_17517,plain,(
    k5_relat_1('#skF_4',k6_partfun1('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_17511])).

tff(c_17504,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17503,c_323])).

tff(c_18972,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_108,c_18964])).

tff(c_18983,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_110,c_17504,c_8627,c_18972])).

tff(c_18984,plain,(
    k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_18983])).

tff(c_8626,plain,
    ( ~ v1_relat_1(k2_funct_1('#skF_4'))
    | k5_relat_1(k2_funct_1('#skF_4'),k6_partfun1('#skF_2')) = k2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_869])).

tff(c_8685,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_8626])).

tff(c_8688,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_8685])).

tff(c_8692,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_112,c_8688])).

tff(c_8694,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_8626])).

tff(c_18410,plain,(
    ! [A_898,C_899,B_900] :
      ( k6_partfun1(A_898) = k5_relat_1(C_899,k2_funct_1(C_899))
      | k1_xboole_0 = B_900
      | ~ v2_funct_1(C_899)
      | k2_relset_1(A_898,B_900,C_899) != B_900
      | ~ m1_subset_1(C_899,k1_zfmisc_1(k2_zfmisc_1(A_898,B_900)))
      | ~ v1_funct_2(C_899,A_898,B_900)
      | ~ v1_funct_1(C_899) ) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_18418,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_108,c_18410])).

tff(c_18429,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_110,c_17504,c_8627,c_18418])).

tff(c_18430,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_18429])).

tff(c_18487,plain,(
    ! [C_12] :
      ( k5_relat_1('#skF_4',k5_relat_1(k2_funct_1('#skF_4'),C_12)) = k5_relat_1(k6_partfun1('#skF_2'),C_12)
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1(k2_funct_1('#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18430,c_6])).

tff(c_19603,plain,(
    ! [C_916] :
      ( k5_relat_1('#skF_4',k5_relat_1(k2_funct_1('#skF_4'),C_916)) = k5_relat_1(k6_partfun1('#skF_2'),C_916)
      | ~ v1_relat_1(C_916) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_8694,c_18487])).

tff(c_19628,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = k5_relat_1('#skF_4',k6_partfun1('#skF_1'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_18984,c_19603])).

tff(c_19684,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_19192,c_17517,c_19628])).

tff(c_19686,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_19684])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:54:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.24/4.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.46/4.47  
% 11.46/4.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.46/4.47  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.46/4.47  
% 11.46/4.47  %Foreground sorts:
% 11.46/4.47  
% 11.46/4.47  
% 11.46/4.47  %Background operators:
% 11.46/4.47  
% 11.46/4.47  
% 11.46/4.47  %Foreground operators:
% 11.46/4.47  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.46/4.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.46/4.47  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 11.46/4.47  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 11.46/4.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.46/4.47  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 11.46/4.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.46/4.47  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 11.46/4.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.46/4.47  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.46/4.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.46/4.47  tff('#skF_2', type, '#skF_2': $i).
% 11.46/4.47  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 11.46/4.47  tff('#skF_3', type, '#skF_3': $i).
% 11.46/4.47  tff('#skF_1', type, '#skF_1': $i).
% 11.46/4.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.46/4.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.46/4.47  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 11.46/4.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.46/4.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.46/4.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.46/4.47  tff('#skF_4', type, '#skF_4': $i).
% 11.46/4.47  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 11.46/4.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.46/4.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.46/4.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.46/4.47  
% 11.51/4.50  tff(f_281, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 11.51/4.50  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 11.51/4.50  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 11.51/4.50  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 11.51/4.50  tff(f_148, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.51/4.50  tff(f_178, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 11.51/4.50  tff(f_107, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 11.51/4.50  tff(f_206, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 11.51/4.50  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 11.51/4.50  tff(f_204, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 11.51/4.50  tff(f_194, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 11.51/4.50  tff(f_160, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 11.51/4.50  tff(f_190, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 11.51/4.50  tff(f_255, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 11.51/4.50  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 11.51/4.50  tff(f_68, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 11.51/4.50  tff(f_152, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 11.51/4.50  tff(f_97, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 11.51/4.50  tff(f_239, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 11.51/4.50  tff(f_223, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 11.51/4.50  tff(c_96, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_281])).
% 11.51/4.50  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.51/4.50  tff(c_108, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_281])).
% 11.51/4.50  tff(c_210, plain, (![B_83, A_84]: (v1_relat_1(B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(A_84)) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.51/4.50  tff(c_219, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_108, c_210])).
% 11.51/4.50  tff(c_228, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_219])).
% 11.51/4.50  tff(c_114, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_281])).
% 11.51/4.50  tff(c_216, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_114, c_210])).
% 11.51/4.50  tff(c_225, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_216])).
% 11.51/4.50  tff(c_118, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_281])).
% 11.51/4.50  tff(c_16, plain, (![A_15]: (v1_relat_1(k2_funct_1(A_15)) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.51/4.50  tff(c_102, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_281])).
% 11.51/4.50  tff(c_98, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_281])).
% 11.51/4.50  tff(c_116, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_281])).
% 11.51/4.50  tff(c_277, plain, (![A_92, B_93, C_94]: (k1_relset_1(A_92, B_93, C_94)=k1_relat_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 11.51/4.50  tff(c_289, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_114, c_277])).
% 11.51/4.50  tff(c_746, plain, (![B_125, A_126, C_127]: (k1_xboole_0=B_125 | k1_relset_1(A_126, B_125, C_127)=A_126 | ~v1_funct_2(C_127, A_126, B_125) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_126, B_125))))), inference(cnfTransformation, [status(thm)], [f_178])).
% 11.51/4.50  tff(c_752, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_114, c_746])).
% 11.51/4.50  tff(c_760, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_289, c_752])).
% 11.51/4.50  tff(c_761, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_98, c_760])).
% 11.51/4.50  tff(c_235, plain, (![A_86]: (k2_relat_1(k2_funct_1(A_86))=k1_relat_1(A_86) | ~v2_funct_1(A_86) | ~v1_funct_1(A_86) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_107])).
% 11.51/4.50  tff(c_82, plain, (![A_55]: (k6_relat_1(A_55)=k6_partfun1(A_55))), inference(cnfTransformation, [status(thm)], [f_206])).
% 11.51/4.50  tff(c_12, plain, (![A_14]: (k5_relat_1(A_14, k6_relat_1(k2_relat_1(A_14)))=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.51/4.50  tff(c_126, plain, (![A_14]: (k5_relat_1(A_14, k6_partfun1(k2_relat_1(A_14)))=A_14 | ~v1_relat_1(A_14))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_12])).
% 11.51/4.50  tff(c_831, plain, (![A_130]: (k5_relat_1(k2_funct_1(A_130), k6_partfun1(k1_relat_1(A_130)))=k2_funct_1(A_130) | ~v1_relat_1(k2_funct_1(A_130)) | ~v2_funct_1(A_130) | ~v1_funct_1(A_130) | ~v1_relat_1(A_130))), inference(superposition, [status(thm), theory('equality')], [c_235, c_126])).
% 11.51/4.50  tff(c_849, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_761, c_831])).
% 11.51/4.50  tff(c_871, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_225, c_118, c_102, c_849])).
% 11.51/4.50  tff(c_876, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_871])).
% 11.51/4.50  tff(c_880, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_876])).
% 11.51/4.50  tff(c_884, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_225, c_118, c_880])).
% 11.51/4.50  tff(c_885, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_871])).
% 11.51/4.50  tff(c_112, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_281])).
% 11.51/4.50  tff(c_11339, plain, (![E_577, C_576, F_579, D_581, A_580, B_578]: (k1_partfun1(A_580, B_578, C_576, D_581, E_577, F_579)=k5_relat_1(E_577, F_579) | ~m1_subset_1(F_579, k1_zfmisc_1(k2_zfmisc_1(C_576, D_581))) | ~v1_funct_1(F_579) | ~m1_subset_1(E_577, k1_zfmisc_1(k2_zfmisc_1(A_580, B_578))) | ~v1_funct_1(E_577))), inference(cnfTransformation, [status(thm)], [f_204])).
% 11.51/4.50  tff(c_11345, plain, (![A_580, B_578, E_577]: (k1_partfun1(A_580, B_578, '#skF_2', '#skF_1', E_577, '#skF_4')=k5_relat_1(E_577, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_577, k1_zfmisc_1(k2_zfmisc_1(A_580, B_578))) | ~v1_funct_1(E_577))), inference(resolution, [status(thm)], [c_108, c_11339])).
% 11.51/4.50  tff(c_11591, plain, (![A_595, B_596, E_597]: (k1_partfun1(A_595, B_596, '#skF_2', '#skF_1', E_597, '#skF_4')=k5_relat_1(E_597, '#skF_4') | ~m1_subset_1(E_597, k1_zfmisc_1(k2_zfmisc_1(A_595, B_596))) | ~v1_funct_1(E_597))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_11345])).
% 11.51/4.50  tff(c_11600, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_114, c_11591])).
% 11.51/4.50  tff(c_11610, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_11600])).
% 11.51/4.50  tff(c_78, plain, (![A_48]: (m1_subset_1(k6_partfun1(A_48), k1_zfmisc_1(k2_zfmisc_1(A_48, A_48))))), inference(cnfTransformation, [status(thm)], [f_194])).
% 11.51/4.50  tff(c_104, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_281])).
% 11.51/4.50  tff(c_8820, plain, (![D_468, C_469, A_470, B_471]: (D_468=C_469 | ~r2_relset_1(A_470, B_471, C_469, D_468) | ~m1_subset_1(D_468, k1_zfmisc_1(k2_zfmisc_1(A_470, B_471))) | ~m1_subset_1(C_469, k1_zfmisc_1(k2_zfmisc_1(A_470, B_471))))), inference(cnfTransformation, [status(thm)], [f_160])).
% 11.51/4.50  tff(c_8828, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_104, c_8820])).
% 11.51/4.50  tff(c_8843, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_8828])).
% 11.51/4.50  tff(c_9204, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_8843])).
% 11.51/4.50  tff(c_11615, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_11610, c_9204])).
% 11.51/4.50  tff(c_11995, plain, (![F_617, A_616, B_615, D_614, C_618, E_613]: (m1_subset_1(k1_partfun1(A_616, B_615, C_618, D_614, E_613, F_617), k1_zfmisc_1(k2_zfmisc_1(A_616, D_614))) | ~m1_subset_1(F_617, k1_zfmisc_1(k2_zfmisc_1(C_618, D_614))) | ~v1_funct_1(F_617) | ~m1_subset_1(E_613, k1_zfmisc_1(k2_zfmisc_1(A_616, B_615))) | ~v1_funct_1(E_613))), inference(cnfTransformation, [status(thm)], [f_190])).
% 11.51/4.50  tff(c_12065, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_11610, c_11995])).
% 11.51/4.50  tff(c_12096, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_114, c_112, c_108, c_12065])).
% 11.51/4.50  tff(c_12098, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11615, c_12096])).
% 11.51/4.50  tff(c_12099, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_8843])).
% 11.51/4.50  tff(c_18300, plain, (![D_889, F_887, E_885, A_888, C_884, B_886]: (k1_partfun1(A_888, B_886, C_884, D_889, E_885, F_887)=k5_relat_1(E_885, F_887) | ~m1_subset_1(F_887, k1_zfmisc_1(k2_zfmisc_1(C_884, D_889))) | ~v1_funct_1(F_887) | ~m1_subset_1(E_885, k1_zfmisc_1(k2_zfmisc_1(A_888, B_886))) | ~v1_funct_1(E_885))), inference(cnfTransformation, [status(thm)], [f_204])).
% 11.51/4.50  tff(c_18308, plain, (![A_888, B_886, E_885]: (k1_partfun1(A_888, B_886, '#skF_2', '#skF_1', E_885, '#skF_4')=k5_relat_1(E_885, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_885, k1_zfmisc_1(k2_zfmisc_1(A_888, B_886))) | ~v1_funct_1(E_885))), inference(resolution, [status(thm)], [c_108, c_18300])).
% 11.51/4.50  tff(c_18363, plain, (![A_895, B_896, E_897]: (k1_partfun1(A_895, B_896, '#skF_2', '#skF_1', E_897, '#skF_4')=k5_relat_1(E_897, '#skF_4') | ~m1_subset_1(E_897, k1_zfmisc_1(k2_zfmisc_1(A_895, B_896))) | ~v1_funct_1(E_897))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_18308])).
% 11.51/4.50  tff(c_18372, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_114, c_18363])).
% 11.51/4.50  tff(c_18382, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_12099, c_18372])).
% 11.51/4.50  tff(c_886, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_871])).
% 11.51/4.50  tff(c_106, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_281])).
% 11.51/4.50  tff(c_18964, plain, (![B_906, C_907, A_908]: (k6_partfun1(B_906)=k5_relat_1(k2_funct_1(C_907), C_907) | k1_xboole_0=B_906 | ~v2_funct_1(C_907) | k2_relset_1(A_908, B_906, C_907)!=B_906 | ~m1_subset_1(C_907, k1_zfmisc_1(k2_zfmisc_1(A_908, B_906))) | ~v1_funct_2(C_907, A_908, B_906) | ~v1_funct_1(C_907))), inference(cnfTransformation, [status(thm)], [f_255])).
% 11.51/4.50  tff(c_18970, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_114, c_18964])).
% 11.51/4.50  tff(c_18979, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_116, c_106, c_102, c_18970])).
% 11.51/4.50  tff(c_18980, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_98, c_18979])).
% 11.51/4.50  tff(c_6, plain, (![A_6, B_10, C_12]: (k5_relat_1(k5_relat_1(A_6, B_10), C_12)=k5_relat_1(A_6, k5_relat_1(B_10, C_12)) | ~v1_relat_1(C_12) | ~v1_relat_1(B_10) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.51/4.50  tff(c_19055, plain, (![C_12]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_12))=k5_relat_1(k6_partfun1('#skF_2'), C_12) | ~v1_relat_1(C_12) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_18980, c_6])).
% 11.51/4.50  tff(c_19113, plain, (![C_909]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_909))=k5_relat_1(k6_partfun1('#skF_2'), C_909) | ~v1_relat_1(C_909))), inference(demodulation, [status(thm), theory('equality')], [c_886, c_225, c_19055])).
% 11.51/4.50  tff(c_19147, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_18382, c_19113])).
% 11.51/4.50  tff(c_19192, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_228, c_885, c_19147])).
% 11.51/4.50  tff(c_110, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_281])).
% 11.51/4.50  tff(c_100, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_281])).
% 11.51/4.50  tff(c_290, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_108, c_277])).
% 11.51/4.50  tff(c_755, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_108, c_746])).
% 11.51/4.50  tff(c_764, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_290, c_755])).
% 11.51/4.50  tff(c_765, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_100, c_764])).
% 11.51/4.50  tff(c_846, plain, (k5_relat_1(k2_funct_1('#skF_4'), k6_partfun1('#skF_2'))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_765, c_831])).
% 11.51/4.50  tff(c_869, plain, (k5_relat_1(k2_funct_1('#skF_4'), k6_partfun1('#skF_2'))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_228, c_112, c_846])).
% 11.51/4.50  tff(c_901, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_869])).
% 11.51/4.50  tff(c_24, plain, (![A_17]: (v2_funct_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.51/4.50  tff(c_122, plain, (![A_17]: (v2_funct_1(k6_partfun1(A_17)))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_24])).
% 11.51/4.50  tff(c_309, plain, (![A_97, B_98, C_99]: (k2_relset_1(A_97, B_98, C_99)=k2_relat_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_152])).
% 11.51/4.50  tff(c_315, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_114, c_309])).
% 11.51/4.50  tff(c_322, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_315])).
% 11.51/4.50  tff(c_5434, plain, (![E_339, A_342, C_338, D_343, F_341, B_340]: (k1_partfun1(A_342, B_340, C_338, D_343, E_339, F_341)=k5_relat_1(E_339, F_341) | ~m1_subset_1(F_341, k1_zfmisc_1(k2_zfmisc_1(C_338, D_343))) | ~v1_funct_1(F_341) | ~m1_subset_1(E_339, k1_zfmisc_1(k2_zfmisc_1(A_342, B_340))) | ~v1_funct_1(E_339))), inference(cnfTransformation, [status(thm)], [f_204])).
% 11.51/4.50  tff(c_5440, plain, (![A_342, B_340, E_339]: (k1_partfun1(A_342, B_340, '#skF_2', '#skF_1', E_339, '#skF_4')=k5_relat_1(E_339, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_339, k1_zfmisc_1(k2_zfmisc_1(A_342, B_340))) | ~v1_funct_1(E_339))), inference(resolution, [status(thm)], [c_108, c_5434])).
% 11.51/4.50  tff(c_5618, plain, (![A_364, B_365, E_366]: (k1_partfun1(A_364, B_365, '#skF_2', '#skF_1', E_366, '#skF_4')=k5_relat_1(E_366, '#skF_4') | ~m1_subset_1(E_366, k1_zfmisc_1(k2_zfmisc_1(A_364, B_365))) | ~v1_funct_1(E_366))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_5440])).
% 11.51/4.50  tff(c_5627, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_114, c_5618])).
% 11.51/4.50  tff(c_5637, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_5627])).
% 11.51/4.50  tff(c_1012, plain, (![D_134, C_135, A_136, B_137]: (D_134=C_135 | ~r2_relset_1(A_136, B_137, C_135, D_134) | ~m1_subset_1(D_134, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))))), inference(cnfTransformation, [status(thm)], [f_160])).
% 11.51/4.50  tff(c_1020, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_104, c_1012])).
% 11.51/4.50  tff(c_1035, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1020])).
% 11.51/4.50  tff(c_1036, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1035])).
% 11.51/4.50  tff(c_5642, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_5637, c_1036])).
% 11.51/4.50  tff(c_6282, plain, (![B_380, D_379, A_381, C_383, E_378, F_382]: (m1_subset_1(k1_partfun1(A_381, B_380, C_383, D_379, E_378, F_382), k1_zfmisc_1(k2_zfmisc_1(A_381, D_379))) | ~m1_subset_1(F_382, k1_zfmisc_1(k2_zfmisc_1(C_383, D_379))) | ~v1_funct_1(F_382) | ~m1_subset_1(E_378, k1_zfmisc_1(k2_zfmisc_1(A_381, B_380))) | ~v1_funct_1(E_378))), inference(cnfTransformation, [status(thm)], [f_190])).
% 11.51/4.50  tff(c_6348, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5637, c_6282])).
% 11.51/4.50  tff(c_6385, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_114, c_112, c_108, c_6348])).
% 11.51/4.50  tff(c_6387, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5642, c_6385])).
% 11.51/4.50  tff(c_6388, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1035])).
% 11.51/4.50  tff(c_8509, plain, (![F_453, A_454, C_450, D_455, E_451, B_452]: (k1_partfun1(A_454, B_452, C_450, D_455, E_451, F_453)=k5_relat_1(E_451, F_453) | ~m1_subset_1(F_453, k1_zfmisc_1(k2_zfmisc_1(C_450, D_455))) | ~v1_funct_1(F_453) | ~m1_subset_1(E_451, k1_zfmisc_1(k2_zfmisc_1(A_454, B_452))) | ~v1_funct_1(E_451))), inference(cnfTransformation, [status(thm)], [f_204])).
% 11.51/4.50  tff(c_8517, plain, (![A_454, B_452, E_451]: (k1_partfun1(A_454, B_452, '#skF_2', '#skF_1', E_451, '#skF_4')=k5_relat_1(E_451, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_451, k1_zfmisc_1(k2_zfmisc_1(A_454, B_452))) | ~v1_funct_1(E_451))), inference(resolution, [status(thm)], [c_108, c_8509])).
% 11.51/4.50  tff(c_8572, plain, (![A_461, B_462, E_463]: (k1_partfun1(A_461, B_462, '#skF_2', '#skF_1', E_463, '#skF_4')=k5_relat_1(E_463, '#skF_4') | ~m1_subset_1(E_463, k1_zfmisc_1(k2_zfmisc_1(A_461, B_462))) | ~v1_funct_1(E_463))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_8517])).
% 11.51/4.50  tff(c_8581, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_114, c_8572])).
% 11.51/4.50  tff(c_8591, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_6388, c_8581])).
% 11.51/4.50  tff(c_32, plain, (![A_19, B_21]: (v2_funct_1(A_19) | k2_relat_1(B_21)!=k1_relat_1(A_19) | ~v2_funct_1(k5_relat_1(B_21, A_19)) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.51/4.50  tff(c_8607, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8591, c_32])).
% 11.51/4.50  tff(c_8623, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_228, c_112, c_225, c_118, c_122, c_322, c_765, c_8607])).
% 11.51/4.50  tff(c_8625, plain, $false, inference(negUnitSimplification, [status(thm)], [c_901, c_8623])).
% 11.51/4.50  tff(c_8627, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_869])).
% 11.51/4.50  tff(c_323, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_108, c_309])).
% 11.51/4.50  tff(c_12526, plain, (![C_623, A_624, B_625]: (v1_funct_1(k2_funct_1(C_623)) | k2_relset_1(A_624, B_625, C_623)!=B_625 | ~v2_funct_1(C_623) | ~m1_subset_1(C_623, k1_zfmisc_1(k2_zfmisc_1(A_624, B_625))) | ~v1_funct_2(C_623, A_624, B_625) | ~v1_funct_1(C_623))), inference(cnfTransformation, [status(thm)], [f_239])).
% 11.51/4.50  tff(c_12535, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_108, c_12526])).
% 11.51/4.50  tff(c_12544, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_110, c_8627, c_323, c_12535])).
% 11.51/4.50  tff(c_12545, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_12544])).
% 11.51/4.50  tff(c_252, plain, (![A_87, B_88, D_89]: (r2_relset_1(A_87, B_88, D_89, D_89) | ~m1_subset_1(D_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_160])).
% 11.51/4.50  tff(c_259, plain, (![A_48]: (r2_relset_1(A_48, A_48, k6_partfun1(A_48), k6_partfun1(A_48)))), inference(resolution, [status(thm)], [c_78, c_252])).
% 11.51/4.50  tff(c_17489, plain, (![A_839, B_840, C_841, D_842]: (k2_relset_1(A_839, B_840, C_841)=B_840 | ~r2_relset_1(B_840, B_840, k1_partfun1(B_840, A_839, A_839, B_840, D_842, C_841), k6_partfun1(B_840)) | ~m1_subset_1(D_842, k1_zfmisc_1(k2_zfmisc_1(B_840, A_839))) | ~v1_funct_2(D_842, B_840, A_839) | ~v1_funct_1(D_842) | ~m1_subset_1(C_841, k1_zfmisc_1(k2_zfmisc_1(A_839, B_840))) | ~v1_funct_2(C_841, A_839, B_840) | ~v1_funct_1(C_841))), inference(cnfTransformation, [status(thm)], [f_223])).
% 11.51/4.50  tff(c_17495, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12099, c_17489])).
% 11.51/4.50  tff(c_17499, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_110, c_108, c_118, c_116, c_114, c_259, c_323, c_17495])).
% 11.51/4.50  tff(c_17501, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12545, c_17499])).
% 11.51/4.50  tff(c_17503, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_12544])).
% 11.51/4.50  tff(c_17511, plain, (k5_relat_1('#skF_4', k6_partfun1('#skF_1'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_17503, c_126])).
% 11.51/4.50  tff(c_17517, plain, (k5_relat_1('#skF_4', k6_partfun1('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_228, c_17511])).
% 11.51/4.50  tff(c_17504, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_17503, c_323])).
% 11.51/4.50  tff(c_18972, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_108, c_18964])).
% 11.51/4.50  tff(c_18983, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_110, c_17504, c_8627, c_18972])).
% 11.51/4.50  tff(c_18984, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_100, c_18983])).
% 11.51/4.50  tff(c_8626, plain, (~v1_relat_1(k2_funct_1('#skF_4')) | k5_relat_1(k2_funct_1('#skF_4'), k6_partfun1('#skF_2'))=k2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_869])).
% 11.51/4.50  tff(c_8685, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_8626])).
% 11.51/4.50  tff(c_8688, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_8685])).
% 11.51/4.50  tff(c_8692, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_228, c_112, c_8688])).
% 11.51/4.50  tff(c_8694, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_8626])).
% 11.51/4.50  tff(c_18410, plain, (![A_898, C_899, B_900]: (k6_partfun1(A_898)=k5_relat_1(C_899, k2_funct_1(C_899)) | k1_xboole_0=B_900 | ~v2_funct_1(C_899) | k2_relset_1(A_898, B_900, C_899)!=B_900 | ~m1_subset_1(C_899, k1_zfmisc_1(k2_zfmisc_1(A_898, B_900))) | ~v1_funct_2(C_899, A_898, B_900) | ~v1_funct_1(C_899))), inference(cnfTransformation, [status(thm)], [f_255])).
% 11.51/4.50  tff(c_18418, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_108, c_18410])).
% 11.51/4.50  tff(c_18429, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_110, c_17504, c_8627, c_18418])).
% 11.51/4.50  tff(c_18430, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_100, c_18429])).
% 11.51/4.50  tff(c_18487, plain, (![C_12]: (k5_relat_1('#skF_4', k5_relat_1(k2_funct_1('#skF_4'), C_12))=k5_relat_1(k6_partfun1('#skF_2'), C_12) | ~v1_relat_1(C_12) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_18430, c_6])).
% 11.51/4.50  tff(c_19603, plain, (![C_916]: (k5_relat_1('#skF_4', k5_relat_1(k2_funct_1('#skF_4'), C_916))=k5_relat_1(k6_partfun1('#skF_2'), C_916) | ~v1_relat_1(C_916))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_8694, c_18487])).
% 11.51/4.50  tff(c_19628, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')=k5_relat_1('#skF_4', k6_partfun1('#skF_1')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_18984, c_19603])).
% 11.51/4.50  tff(c_19684, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_228, c_19192, c_17517, c_19628])).
% 11.51/4.50  tff(c_19686, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_19684])).
% 11.51/4.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.51/4.50  
% 11.51/4.50  Inference rules
% 11.51/4.50  ----------------------
% 11.51/4.50  #Ref     : 0
% 11.51/4.50  #Sup     : 4227
% 11.51/4.50  #Fact    : 0
% 11.51/4.50  #Define  : 0
% 11.51/4.50  #Split   : 43
% 11.51/4.50  #Chain   : 0
% 11.51/4.50  #Close   : 0
% 11.51/4.50  
% 11.51/4.50  Ordering : KBO
% 11.51/4.50  
% 11.51/4.50  Simplification rules
% 11.51/4.50  ----------------------
% 11.51/4.50  #Subsume      : 209
% 11.51/4.50  #Demod        : 9019
% 11.51/4.50  #Tautology    : 1723
% 11.51/4.50  #SimpNegUnit  : 67
% 11.51/4.50  #BackRed      : 122
% 11.51/4.50  
% 11.51/4.50  #Partial instantiations: 0
% 11.51/4.50  #Strategies tried      : 1
% 11.51/4.50  
% 11.51/4.50  Timing (in seconds)
% 11.51/4.50  ----------------------
% 11.51/4.50  Preprocessing        : 0.40
% 11.51/4.50  Parsing              : 0.22
% 11.51/4.50  CNF conversion       : 0.03
% 11.51/4.50  Main loop            : 3.31
% 11.51/4.50  Inferencing          : 0.94
% 11.51/4.50  Reduction            : 1.49
% 11.51/4.50  Demodulation         : 1.21
% 11.51/4.50  BG Simplification    : 0.12
% 11.51/4.50  Subsumption          : 0.58
% 11.51/4.50  Abstraction          : 0.16
% 11.51/4.50  MUC search           : 0.00
% 11.51/4.50  Cooper               : 0.00
% 11.51/4.50  Total                : 3.77
% 11.51/4.50  Index Insertion      : 0.00
% 11.51/4.50  Index Deletion       : 0.00
% 11.51/4.50  Index Matching       : 0.00
% 11.51/4.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
