%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:07 EST 2020

% Result     : Theorem 8.79s
% Output     : CNFRefutation 8.81s
% Verified   : 
% Statistics : Number of formulae       :  182 (2299 expanded)
%              Number of leaves         :   44 ( 837 expanded)
%              Depth                    :   22
%              Number of atoms          :  416 (10164 expanded)
%              Number of equality atoms :  144 (3693 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_216,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_190,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_119,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_131,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_129,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_148,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_57,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_115,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_103,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_174,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
              & k2_relset_1(A,B,D) = B )
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | ( v2_funct_1(D)
                & v2_funct_1(E) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

tff(c_64,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_82,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_130,plain,(
    ! [C_63,A_64,B_65] :
      ( v1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_141,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_130])).

tff(c_86,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_14,plain,(
    ! [A_11] :
      ( v1_relat_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_84,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_74,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_70,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_4422,plain,(
    ! [B_283,C_284,A_285] :
      ( k6_partfun1(B_283) = k5_relat_1(k2_funct_1(C_284),C_284)
      | k1_xboole_0 = B_283
      | ~ v2_funct_1(C_284)
      | k2_relset_1(A_285,B_283,C_284) != B_283
      | ~ m1_subset_1(C_284,k1_zfmisc_1(k2_zfmisc_1(A_285,B_283)))
      | ~ v1_funct_2(C_284,A_285,B_283)
      | ~ v1_funct_1(C_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_4426,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_4422])).

tff(c_4434,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_74,c_70,c_4426])).

tff(c_4435,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_4434])).

tff(c_44,plain,(
    ! [A_32] : m1_subset_1(k6_partfun1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_140,plain,(
    ! [A_32] : v1_relat_1(k6_partfun1(A_32)) ),
    inference(resolution,[status(thm)],[c_44,c_130])).

tff(c_48,plain,(
    ! [A_39] : k6_relat_1(A_39) = k6_partfun1(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_8,plain,(
    ! [A_9] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_9)),A_9) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_91,plain,(
    ! [A_9] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_9)),A_9) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_8])).

tff(c_308,plain,(
    ! [A_84,B_85,C_86] :
      ( k5_relat_1(k5_relat_1(A_84,B_85),C_86) = k5_relat_1(A_84,k5_relat_1(B_85,C_86))
      | ~ v1_relat_1(C_86)
      | ~ v1_relat_1(B_85)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_355,plain,(
    ! [A_9,C_86] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_9)),k5_relat_1(A_9,C_86)) = k5_relat_1(A_9,C_86)
      | ~ v1_relat_1(C_86)
      | ~ v1_relat_1(A_9)
      | ~ v1_relat_1(k6_partfun1(k1_relat_1(A_9)))
      | ~ v1_relat_1(A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_308])).

tff(c_372,plain,(
    ! [A_9,C_86] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_9)),k5_relat_1(A_9,C_86)) = k5_relat_1(A_9,C_86)
      | ~ v1_relat_1(C_86)
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_355])).

tff(c_4443,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1('#skF_3'))),k6_partfun1('#skF_2')) = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4435,c_372])).

tff(c_4456,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1('#skF_3'))),k6_partfun1('#skF_2')) = k6_partfun1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_4435,c_4443])).

tff(c_8200,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_4456])).

tff(c_8203,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_8200])).

tff(c_8207,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_86,c_8203])).

tff(c_8209,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_4456])).

tff(c_76,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_142,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_130])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_80,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_78,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_217,plain,(
    ! [A_76,B_77,C_78] :
      ( k2_relset_1(A_76,B_77,C_78) = k2_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_231,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_217])).

tff(c_4428,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_4422])).

tff(c_4438,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_231,c_4428])).

tff(c_4439,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_4438])).

tff(c_4464,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4439])).

tff(c_4201,plain,(
    ! [C_273,A_271,F_274,D_275,B_276,E_272] :
      ( k1_partfun1(A_271,B_276,C_273,D_275,E_272,F_274) = k5_relat_1(E_272,F_274)
      | ~ m1_subset_1(F_274,k1_zfmisc_1(k2_zfmisc_1(C_273,D_275)))
      | ~ v1_funct_1(F_274)
      | ~ m1_subset_1(E_272,k1_zfmisc_1(k2_zfmisc_1(A_271,B_276)))
      | ~ v1_funct_1(E_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_4207,plain,(
    ! [A_271,B_276,E_272] :
      ( k1_partfun1(A_271,B_276,'#skF_2','#skF_1',E_272,'#skF_4') = k5_relat_1(E_272,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_272,k1_zfmisc_1(k2_zfmisc_1(A_271,B_276)))
      | ~ v1_funct_1(E_272) ) ),
    inference(resolution,[status(thm)],[c_76,c_4201])).

tff(c_4465,plain,(
    ! [A_286,B_287,E_288] :
      ( k1_partfun1(A_286,B_287,'#skF_2','#skF_1',E_288,'#skF_4') = k5_relat_1(E_288,'#skF_4')
      | ~ m1_subset_1(E_288,k1_zfmisc_1(k2_zfmisc_1(A_286,B_287)))
      | ~ v1_funct_1(E_288) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4207])).

tff(c_4471,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_4465])).

tff(c_4478,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_4471])).

tff(c_72,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_4483,plain,(
    r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4478,c_72])).

tff(c_5073,plain,(
    ! [A_320,B_321,C_322,D_323] :
      ( k2_relset_1(A_320,B_321,C_322) = B_321
      | ~ r2_relset_1(B_321,B_321,k1_partfun1(B_321,A_320,A_320,B_321,D_323,C_322),k6_partfun1(B_321))
      | ~ m1_subset_1(D_323,k1_zfmisc_1(k2_zfmisc_1(B_321,A_320)))
      | ~ v1_funct_2(D_323,B_321,A_320)
      | ~ v1_funct_1(D_323)
      | ~ m1_subset_1(C_322,k1_zfmisc_1(k2_zfmisc_1(A_320,B_321)))
      | ~ v1_funct_2(C_322,A_320,B_321)
      | ~ v1_funct_1(C_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_5079,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_4'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4478,c_5073])).

tff(c_5083,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_86,c_84,c_82,c_4483,c_231,c_5079])).

tff(c_5085,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4464,c_5083])).

tff(c_5087,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4439])).

tff(c_10,plain,(
    ! [A_10] :
      ( k5_relat_1(A_10,k6_relat_1(k2_relat_1(A_10))) = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_90,plain,(
    ! [A_10] :
      ( k5_relat_1(A_10,k6_partfun1(k2_relat_1(A_10))) = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_10])).

tff(c_5092,plain,
    ( k5_relat_1('#skF_4',k6_partfun1('#skF_1')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5087,c_90])).

tff(c_5096,plain,(
    k5_relat_1('#skF_4',k6_partfun1('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_5092])).

tff(c_7679,plain,(
    ! [A_384,C_385,B_386] :
      ( k6_partfun1(A_384) = k5_relat_1(C_385,k2_funct_1(C_385))
      | k1_xboole_0 = B_386
      | ~ v2_funct_1(C_385)
      | k2_relset_1(A_384,B_386,C_385) != B_386
      | ~ m1_subset_1(C_385,k1_zfmisc_1(k2_zfmisc_1(A_384,B_386)))
      | ~ v1_funct_2(C_385,A_384,B_386)
      | ~ v1_funct_1(C_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_7683,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_7679])).

tff(c_7691,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_74,c_70,c_7683])).

tff(c_7692,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_7691])).

tff(c_16,plain,(
    ! [A_12] : v2_funct_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_89,plain,(
    ! [A_12] : v2_funct_1(k6_partfun1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_16])).

tff(c_6623,plain,(
    ! [A_370,B_371,E_372] :
      ( k1_partfun1(A_370,B_371,'#skF_2','#skF_1',E_372,'#skF_4') = k5_relat_1(E_372,'#skF_4')
      | ~ m1_subset_1(E_372,k1_zfmisc_1(k2_zfmisc_1(A_370,B_371)))
      | ~ v1_funct_1(E_372) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4207])).

tff(c_6644,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_6623])).

tff(c_6664,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_6644])).

tff(c_38,plain,(
    ! [B_27,D_29,A_26,E_30,F_31,C_28] :
      ( m1_subset_1(k1_partfun1(A_26,B_27,C_28,D_29,E_30,F_31),k1_zfmisc_1(k2_zfmisc_1(A_26,D_29)))
      | ~ m1_subset_1(F_31,k1_zfmisc_1(k2_zfmisc_1(C_28,D_29)))
      | ~ v1_funct_1(F_31)
      | ~ m1_subset_1(E_30,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ v1_funct_1(E_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_6765,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6664,c_38])).

tff(c_6777,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_80,c_76,c_6765])).

tff(c_6754,plain,(
    r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6664,c_72])).

tff(c_36,plain,(
    ! [D_25,C_24,A_22,B_23] :
      ( D_25 = C_24
      | ~ r2_relset_1(A_22,B_23,C_24,D_25)
      | ~ m1_subset_1(D_25,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6780,plain,
    ( k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_6754,c_36])).

tff(c_6783,plain,
    ( k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_6780])).

tff(c_7551,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6777,c_6783])).

tff(c_5086,plain,
    ( ~ v2_funct_1('#skF_4')
    | k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_4439])).

tff(c_5116,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5086])).

tff(c_54,plain,(
    ! [E_50,D_48,C_47,A_45,B_46] :
      ( k1_xboole_0 = C_47
      | v2_funct_1(E_50)
      | k2_relset_1(A_45,B_46,D_48) != B_46
      | ~ v2_funct_1(k1_partfun1(A_45,B_46,B_46,C_47,D_48,E_50))
      | ~ m1_subset_1(E_50,k1_zfmisc_1(k2_zfmisc_1(B_46,C_47)))
      | ~ v1_funct_2(E_50,B_46,C_47)
      | ~ v1_funct_1(E_50)
      | ~ m1_subset_1(D_48,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46)))
      | ~ v1_funct_2(D_48,A_45,B_46)
      | ~ v1_funct_1(D_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_6759,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6664,c_54])).

tff(c_6772,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_80,c_78,c_76,c_74,c_6759])).

tff(c_6773,plain,(
    ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_5116,c_68,c_6772])).

tff(c_7559,plain,(
    ~ v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7551,c_6773])).

tff(c_7569,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_7559])).

tff(c_7570,plain,(
    k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_5086])).

tff(c_7575,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1('#skF_4'))),k6_partfun1('#skF_1')) = k5_relat_1(k2_funct_1('#skF_4'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7570,c_372])).

tff(c_7588,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1('#skF_4'))),k6_partfun1('#skF_1')) = k6_partfun1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_7570,c_7575])).

tff(c_8236,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_7588])).

tff(c_8239,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_8236])).

tff(c_8243,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_80,c_8239])).

tff(c_8245,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_7588])).

tff(c_223,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_217])).

tff(c_230,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_223])).

tff(c_244,plain,
    ( k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_90])).

tff(c_248,plain,(
    k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_244])).

tff(c_5088,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5087,c_231])).

tff(c_7571,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_5086])).

tff(c_7685,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_7679])).

tff(c_7695,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_5088,c_7571,c_7685])).

tff(c_7696,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_7695])).

tff(c_7869,plain,(
    ! [A_393,B_394,E_395] :
      ( k1_partfun1(A_393,B_394,'#skF_2','#skF_1',E_395,'#skF_4') = k5_relat_1(E_395,'#skF_4')
      | ~ m1_subset_1(E_395,k1_zfmisc_1(k2_zfmisc_1(A_393,B_394)))
      | ~ v1_funct_1(E_395) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4207])).

tff(c_7878,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_7869])).

tff(c_7886,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_7878])).

tff(c_7923,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7886,c_38])).

tff(c_7927,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_80,c_76,c_7923])).

tff(c_7919,plain,(
    r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7886,c_72])).

tff(c_7931,plain,
    ( k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_7919,c_36])).

tff(c_7934,plain,
    ( k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_7931])).

tff(c_8925,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7927,c_7934])).

tff(c_2,plain,(
    ! [A_1,B_5,C_7] :
      ( k5_relat_1(k5_relat_1(A_1,B_5),C_7) = k5_relat_1(A_1,k5_relat_1(B_5,C_7))
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8950,plain,(
    ! [C_7] :
      ( k5_relat_1(k6_partfun1('#skF_1'),C_7) = k5_relat_1('#skF_3',k5_relat_1('#skF_4',C_7))
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8925,c_2])).

tff(c_8986,plain,(
    ! [C_429] :
      ( k5_relat_1(k6_partfun1('#skF_1'),C_429) = k5_relat_1('#skF_3',k5_relat_1('#skF_4',C_429))
      | ~ v1_relat_1(C_429) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_142,c_8950])).

tff(c_20,plain,(
    ! [A_13] :
      ( k1_relat_1(k2_funct_1(A_13)) = k2_relat_1(A_13)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6,plain,(
    ! [A_8] : k2_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_92,plain,(
    ! [A_8] : k2_relat_1(k6_partfun1(A_8)) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_6])).

tff(c_22,plain,(
    ! [A_14] :
      ( k2_relat_1(k5_relat_1(A_14,k2_funct_1(A_14))) = k1_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_7761,plain,
    ( k2_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7696,c_22])).

tff(c_7778,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_80,c_7571,c_92,c_7761])).

tff(c_193,plain,(
    ! [A_74] :
      ( k2_relat_1(k2_funct_1(A_74)) = k1_relat_1(A_74)
      | ~ v2_funct_1(A_74)
      | ~ v1_funct_1(A_74)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8589,plain,(
    ! [A_426] :
      ( k5_relat_1(k2_funct_1(A_426),k6_partfun1(k1_relat_1(A_426))) = k2_funct_1(A_426)
      | ~ v1_relat_1(k2_funct_1(A_426))
      | ~ v2_funct_1(A_426)
      | ~ v1_funct_1(A_426)
      | ~ v1_relat_1(A_426) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_90])).

tff(c_8608,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),k6_partfun1('#skF_2')) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7778,c_8589])).

tff(c_8630,plain,(
    k5_relat_1(k2_funct_1('#skF_4'),k6_partfun1('#skF_2')) = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_80,c_7571,c_8245,c_8608])).

tff(c_8638,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1('#skF_4'))),k2_funct_1('#skF_4')) = k5_relat_1(k2_funct_1('#skF_4'),k6_partfun1('#skF_2'))
    | ~ v1_relat_1(k6_partfun1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8630,c_372])).

tff(c_8645,plain,(
    k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1('#skF_4'))),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8245,c_140,c_8630,c_8638])).

tff(c_8685,plain,
    ( k5_relat_1(k6_partfun1(k2_relat_1('#skF_4')),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_8645])).

tff(c_8705,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_80,c_7571,c_5087,c_8685])).

tff(c_8992,plain,
    ( k5_relat_1('#skF_3',k5_relat_1('#skF_4',k2_funct_1('#skF_4'))) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8986,c_8705])).

tff(c_9073,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8245,c_248,c_7696,c_8992])).

tff(c_7758,plain,(
    ! [C_7] :
      ( k5_relat_1('#skF_4',k5_relat_1(k2_funct_1('#skF_4'),C_7)) = k5_relat_1(k6_partfun1('#skF_2'),C_7)
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1(k2_funct_1('#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7696,c_2])).

tff(c_7776,plain,(
    ! [C_7] :
      ( k5_relat_1('#skF_4',k5_relat_1(k2_funct_1('#skF_4'),C_7)) = k5_relat_1(k6_partfun1('#skF_2'),C_7)
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1(k2_funct_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_7758])).

tff(c_9633,plain,(
    ! [C_433] :
      ( k5_relat_1(k6_partfun1('#skF_2'),C_433) = k5_relat_1('#skF_4',k5_relat_1('#skF_3',C_433))
      | ~ v1_relat_1(C_433) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_9073,c_9073,c_7776])).

tff(c_7706,plain,
    ( k2_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7692,c_22])).

tff(c_7723,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_86,c_70,c_92,c_7706])).

tff(c_8611,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7723,c_8589])).

tff(c_8632,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_86,c_70,c_8209,c_8611])).

tff(c_8652,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1('#skF_3'))),k2_funct_1('#skF_3')) = k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1'))
    | ~ v1_relat_1(k6_partfun1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8632,c_372])).

tff(c_8659,plain,(
    k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1('#skF_3'))),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8209,c_140,c_8632,c_8652])).

tff(c_8756,plain,
    ( k5_relat_1(k6_partfun1(k2_relat_1('#skF_3')),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_8659])).

tff(c_8776,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_86,c_70,c_230,c_8756])).

tff(c_9650,plain,
    ( k5_relat_1('#skF_4',k5_relat_1('#skF_3',k2_funct_1('#skF_3'))) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9633,c_8776])).

tff(c_9741,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8209,c_5096,c_7692,c_9650])).

tff(c_9743,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_9741])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:34:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.79/2.94  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.81/2.96  
% 8.81/2.96  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.81/2.96  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.81/2.96  
% 8.81/2.96  %Foreground sorts:
% 8.81/2.96  
% 8.81/2.96  
% 8.81/2.96  %Background operators:
% 8.81/2.96  
% 8.81/2.96  
% 8.81/2.96  %Foreground operators:
% 8.81/2.96  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.81/2.96  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.81/2.96  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.81/2.96  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.81/2.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.81/2.96  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 8.81/2.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.81/2.96  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.81/2.96  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.81/2.96  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.81/2.96  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.81/2.96  tff('#skF_2', type, '#skF_2': $i).
% 8.81/2.96  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 8.81/2.96  tff('#skF_3', type, '#skF_3': $i).
% 8.81/2.96  tff('#skF_1', type, '#skF_1': $i).
% 8.81/2.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.81/2.96  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 8.81/2.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.81/2.96  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.81/2.96  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.81/2.96  tff('#skF_4', type, '#skF_4': $i).
% 8.81/2.96  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.81/2.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.81/2.96  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.81/2.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.81/2.96  
% 8.81/2.99  tff(f_216, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 8.81/2.99  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.81/2.99  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 8.81/2.99  tff(f_190, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 8.81/2.99  tff(f_119, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 8.81/2.99  tff(f_131, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 8.81/2.99  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 8.81/2.99  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 8.81/2.99  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.81/2.99  tff(f_129, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 8.81/2.99  tff(f_148, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 8.81/2.99  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 8.81/2.99  tff(f_57, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 8.81/2.99  tff(f_115, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 8.81/2.99  tff(f_103, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 8.81/2.99  tff(f_174, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 8.81/2.99  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 8.81/2.99  tff(f_39, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 8.81/2.99  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_funct_1)).
% 8.81/2.99  tff(c_64, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.81/2.99  tff(c_82, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.81/2.99  tff(c_130, plain, (![C_63, A_64, B_65]: (v1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.81/2.99  tff(c_141, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_130])).
% 8.81/2.99  tff(c_86, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.81/2.99  tff(c_14, plain, (![A_11]: (v1_relat_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.81/2.99  tff(c_66, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.81/2.99  tff(c_84, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.81/2.99  tff(c_74, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.81/2.99  tff(c_70, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.81/2.99  tff(c_4422, plain, (![B_283, C_284, A_285]: (k6_partfun1(B_283)=k5_relat_1(k2_funct_1(C_284), C_284) | k1_xboole_0=B_283 | ~v2_funct_1(C_284) | k2_relset_1(A_285, B_283, C_284)!=B_283 | ~m1_subset_1(C_284, k1_zfmisc_1(k2_zfmisc_1(A_285, B_283))) | ~v1_funct_2(C_284, A_285, B_283) | ~v1_funct_1(C_284))), inference(cnfTransformation, [status(thm)], [f_190])).
% 8.81/2.99  tff(c_4426, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_4422])).
% 8.81/2.99  tff(c_4434, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_74, c_70, c_4426])).
% 8.81/2.99  tff(c_4435, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_66, c_4434])).
% 8.81/2.99  tff(c_44, plain, (![A_32]: (m1_subset_1(k6_partfun1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.81/2.99  tff(c_140, plain, (![A_32]: (v1_relat_1(k6_partfun1(A_32)))), inference(resolution, [status(thm)], [c_44, c_130])).
% 8.81/2.99  tff(c_48, plain, (![A_39]: (k6_relat_1(A_39)=k6_partfun1(A_39))), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.81/2.99  tff(c_8, plain, (![A_9]: (k5_relat_1(k6_relat_1(k1_relat_1(A_9)), A_9)=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.81/2.99  tff(c_91, plain, (![A_9]: (k5_relat_1(k6_partfun1(k1_relat_1(A_9)), A_9)=A_9 | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_8])).
% 8.81/2.99  tff(c_308, plain, (![A_84, B_85, C_86]: (k5_relat_1(k5_relat_1(A_84, B_85), C_86)=k5_relat_1(A_84, k5_relat_1(B_85, C_86)) | ~v1_relat_1(C_86) | ~v1_relat_1(B_85) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.81/2.99  tff(c_355, plain, (![A_9, C_86]: (k5_relat_1(k6_partfun1(k1_relat_1(A_9)), k5_relat_1(A_9, C_86))=k5_relat_1(A_9, C_86) | ~v1_relat_1(C_86) | ~v1_relat_1(A_9) | ~v1_relat_1(k6_partfun1(k1_relat_1(A_9))) | ~v1_relat_1(A_9))), inference(superposition, [status(thm), theory('equality')], [c_91, c_308])).
% 8.81/2.99  tff(c_372, plain, (![A_9, C_86]: (k5_relat_1(k6_partfun1(k1_relat_1(A_9)), k5_relat_1(A_9, C_86))=k5_relat_1(A_9, C_86) | ~v1_relat_1(C_86) | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_355])).
% 8.81/2.99  tff(c_4443, plain, (k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1('#skF_3'))), k6_partfun1('#skF_2'))=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4435, c_372])).
% 8.81/2.99  tff(c_4456, plain, (k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1('#skF_3'))), k6_partfun1('#skF_2'))=k6_partfun1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_4435, c_4443])).
% 8.81/2.99  tff(c_8200, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_4456])).
% 8.81/2.99  tff(c_8203, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_8200])).
% 8.81/2.99  tff(c_8207, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141, c_86, c_8203])).
% 8.81/2.99  tff(c_8209, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_4456])).
% 8.81/2.99  tff(c_76, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.81/2.99  tff(c_142, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_130])).
% 8.81/2.99  tff(c_68, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.81/2.99  tff(c_80, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.81/2.99  tff(c_78, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.81/2.99  tff(c_217, plain, (![A_76, B_77, C_78]: (k2_relset_1(A_76, B_77, C_78)=k2_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.81/2.99  tff(c_231, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_217])).
% 8.81/2.99  tff(c_4428, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_4422])).
% 8.81/2.99  tff(c_4438, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_231, c_4428])).
% 8.81/2.99  tff(c_4439, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_68, c_4438])).
% 8.81/2.99  tff(c_4464, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_4439])).
% 8.81/2.99  tff(c_4201, plain, (![C_273, A_271, F_274, D_275, B_276, E_272]: (k1_partfun1(A_271, B_276, C_273, D_275, E_272, F_274)=k5_relat_1(E_272, F_274) | ~m1_subset_1(F_274, k1_zfmisc_1(k2_zfmisc_1(C_273, D_275))) | ~v1_funct_1(F_274) | ~m1_subset_1(E_272, k1_zfmisc_1(k2_zfmisc_1(A_271, B_276))) | ~v1_funct_1(E_272))), inference(cnfTransformation, [status(thm)], [f_129])).
% 8.81/2.99  tff(c_4207, plain, (![A_271, B_276, E_272]: (k1_partfun1(A_271, B_276, '#skF_2', '#skF_1', E_272, '#skF_4')=k5_relat_1(E_272, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_272, k1_zfmisc_1(k2_zfmisc_1(A_271, B_276))) | ~v1_funct_1(E_272))), inference(resolution, [status(thm)], [c_76, c_4201])).
% 8.81/2.99  tff(c_4465, plain, (![A_286, B_287, E_288]: (k1_partfun1(A_286, B_287, '#skF_2', '#skF_1', E_288, '#skF_4')=k5_relat_1(E_288, '#skF_4') | ~m1_subset_1(E_288, k1_zfmisc_1(k2_zfmisc_1(A_286, B_287))) | ~v1_funct_1(E_288))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4207])).
% 8.81/2.99  tff(c_4471, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_4465])).
% 8.81/2.99  tff(c_4478, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_4471])).
% 8.81/2.99  tff(c_72, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.81/2.99  tff(c_4483, plain, (r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4478, c_72])).
% 8.81/2.99  tff(c_5073, plain, (![A_320, B_321, C_322, D_323]: (k2_relset_1(A_320, B_321, C_322)=B_321 | ~r2_relset_1(B_321, B_321, k1_partfun1(B_321, A_320, A_320, B_321, D_323, C_322), k6_partfun1(B_321)) | ~m1_subset_1(D_323, k1_zfmisc_1(k2_zfmisc_1(B_321, A_320))) | ~v1_funct_2(D_323, B_321, A_320) | ~v1_funct_1(D_323) | ~m1_subset_1(C_322, k1_zfmisc_1(k2_zfmisc_1(A_320, B_321))) | ~v1_funct_2(C_322, A_320, B_321) | ~v1_funct_1(C_322))), inference(cnfTransformation, [status(thm)], [f_148])).
% 8.81/2.99  tff(c_5079, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_4'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4478, c_5073])).
% 8.81/2.99  tff(c_5083, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_86, c_84, c_82, c_4483, c_231, c_5079])).
% 8.81/2.99  tff(c_5085, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4464, c_5083])).
% 8.81/2.99  tff(c_5087, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_4439])).
% 8.81/2.99  tff(c_10, plain, (![A_10]: (k5_relat_1(A_10, k6_relat_1(k2_relat_1(A_10)))=A_10 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.81/2.99  tff(c_90, plain, (![A_10]: (k5_relat_1(A_10, k6_partfun1(k2_relat_1(A_10)))=A_10 | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_10])).
% 8.81/2.99  tff(c_5092, plain, (k5_relat_1('#skF_4', k6_partfun1('#skF_1'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5087, c_90])).
% 8.81/2.99  tff(c_5096, plain, (k5_relat_1('#skF_4', k6_partfun1('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_142, c_5092])).
% 8.81/2.99  tff(c_7679, plain, (![A_384, C_385, B_386]: (k6_partfun1(A_384)=k5_relat_1(C_385, k2_funct_1(C_385)) | k1_xboole_0=B_386 | ~v2_funct_1(C_385) | k2_relset_1(A_384, B_386, C_385)!=B_386 | ~m1_subset_1(C_385, k1_zfmisc_1(k2_zfmisc_1(A_384, B_386))) | ~v1_funct_2(C_385, A_384, B_386) | ~v1_funct_1(C_385))), inference(cnfTransformation, [status(thm)], [f_190])).
% 8.81/2.99  tff(c_7683, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_7679])).
% 8.81/2.99  tff(c_7691, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_74, c_70, c_7683])).
% 8.81/2.99  tff(c_7692, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_66, c_7691])).
% 8.81/2.99  tff(c_16, plain, (![A_12]: (v2_funct_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.81/2.99  tff(c_89, plain, (![A_12]: (v2_funct_1(k6_partfun1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_16])).
% 8.81/2.99  tff(c_6623, plain, (![A_370, B_371, E_372]: (k1_partfun1(A_370, B_371, '#skF_2', '#skF_1', E_372, '#skF_4')=k5_relat_1(E_372, '#skF_4') | ~m1_subset_1(E_372, k1_zfmisc_1(k2_zfmisc_1(A_370, B_371))) | ~v1_funct_1(E_372))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4207])).
% 8.81/2.99  tff(c_6644, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_6623])).
% 8.81/2.99  tff(c_6664, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_6644])).
% 8.81/2.99  tff(c_38, plain, (![B_27, D_29, A_26, E_30, F_31, C_28]: (m1_subset_1(k1_partfun1(A_26, B_27, C_28, D_29, E_30, F_31), k1_zfmisc_1(k2_zfmisc_1(A_26, D_29))) | ~m1_subset_1(F_31, k1_zfmisc_1(k2_zfmisc_1(C_28, D_29))) | ~v1_funct_1(F_31) | ~m1_subset_1(E_30, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~v1_funct_1(E_30))), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.81/2.99  tff(c_6765, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6664, c_38])).
% 8.81/2.99  tff(c_6777, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_80, c_76, c_6765])).
% 8.81/2.99  tff(c_6754, plain, (r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6664, c_72])).
% 8.81/2.99  tff(c_36, plain, (![D_25, C_24, A_22, B_23]: (D_25=C_24 | ~r2_relset_1(A_22, B_23, C_24, D_25) | ~m1_subset_1(D_25, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.81/2.99  tff(c_6780, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_6754, c_36])).
% 8.81/2.99  tff(c_6783, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_6780])).
% 8.81/2.99  tff(c_7551, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6777, c_6783])).
% 8.81/2.99  tff(c_5086, plain, (~v2_funct_1('#skF_4') | k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_4439])).
% 8.81/2.99  tff(c_5116, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_5086])).
% 8.81/2.99  tff(c_54, plain, (![E_50, D_48, C_47, A_45, B_46]: (k1_xboole_0=C_47 | v2_funct_1(E_50) | k2_relset_1(A_45, B_46, D_48)!=B_46 | ~v2_funct_1(k1_partfun1(A_45, B_46, B_46, C_47, D_48, E_50)) | ~m1_subset_1(E_50, k1_zfmisc_1(k2_zfmisc_1(B_46, C_47))) | ~v1_funct_2(E_50, B_46, C_47) | ~v1_funct_1(E_50) | ~m1_subset_1(D_48, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))) | ~v1_funct_2(D_48, A_45, B_46) | ~v1_funct_1(D_48))), inference(cnfTransformation, [status(thm)], [f_174])).
% 8.81/2.99  tff(c_6759, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6664, c_54])).
% 8.81/2.99  tff(c_6772, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_80, c_78, c_76, c_74, c_6759])).
% 8.81/2.99  tff(c_6773, plain, (~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_5116, c_68, c_6772])).
% 8.81/2.99  tff(c_7559, plain, (~v2_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_7551, c_6773])).
% 8.81/2.99  tff(c_7569, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_7559])).
% 8.81/2.99  tff(c_7570, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_5086])).
% 8.81/2.99  tff(c_7575, plain, (k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1('#skF_4'))), k6_partfun1('#skF_1'))=k5_relat_1(k2_funct_1('#skF_4'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7570, c_372])).
% 8.81/2.99  tff(c_7588, plain, (k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1('#skF_4'))), k6_partfun1('#skF_1'))=k6_partfun1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_7570, c_7575])).
% 8.81/2.99  tff(c_8236, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_7588])).
% 8.81/2.99  tff(c_8239, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_8236])).
% 8.81/2.99  tff(c_8243, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_80, c_8239])).
% 8.81/2.99  tff(c_8245, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_7588])).
% 8.81/2.99  tff(c_223, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_217])).
% 8.81/2.99  tff(c_230, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_223])).
% 8.81/2.99  tff(c_244, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_230, c_90])).
% 8.81/2.99  tff(c_248, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_141, c_244])).
% 8.81/2.99  tff(c_5088, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5087, c_231])).
% 8.81/2.99  tff(c_7571, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_5086])).
% 8.81/2.99  tff(c_7685, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_7679])).
% 8.81/2.99  tff(c_7695, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_5088, c_7571, c_7685])).
% 8.81/2.99  tff(c_7696, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_68, c_7695])).
% 8.81/2.99  tff(c_7869, plain, (![A_393, B_394, E_395]: (k1_partfun1(A_393, B_394, '#skF_2', '#skF_1', E_395, '#skF_4')=k5_relat_1(E_395, '#skF_4') | ~m1_subset_1(E_395, k1_zfmisc_1(k2_zfmisc_1(A_393, B_394))) | ~v1_funct_1(E_395))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4207])).
% 8.81/2.99  tff(c_7878, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_7869])).
% 8.81/2.99  tff(c_7886, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_7878])).
% 8.81/2.99  tff(c_7923, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7886, c_38])).
% 8.81/2.99  tff(c_7927, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_80, c_76, c_7923])).
% 8.81/2.99  tff(c_7919, plain, (r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_7886, c_72])).
% 8.81/2.99  tff(c_7931, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_7919, c_36])).
% 8.81/2.99  tff(c_7934, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_7931])).
% 8.81/2.99  tff(c_8925, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7927, c_7934])).
% 8.81/2.99  tff(c_2, plain, (![A_1, B_5, C_7]: (k5_relat_1(k5_relat_1(A_1, B_5), C_7)=k5_relat_1(A_1, k5_relat_1(B_5, C_7)) | ~v1_relat_1(C_7) | ~v1_relat_1(B_5) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.81/2.99  tff(c_8950, plain, (![C_7]: (k5_relat_1(k6_partfun1('#skF_1'), C_7)=k5_relat_1('#skF_3', k5_relat_1('#skF_4', C_7)) | ~v1_relat_1(C_7) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_8925, c_2])).
% 8.81/2.99  tff(c_8986, plain, (![C_429]: (k5_relat_1(k6_partfun1('#skF_1'), C_429)=k5_relat_1('#skF_3', k5_relat_1('#skF_4', C_429)) | ~v1_relat_1(C_429))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_142, c_8950])).
% 8.81/2.99  tff(c_20, plain, (![A_13]: (k1_relat_1(k2_funct_1(A_13))=k2_relat_1(A_13) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.81/2.99  tff(c_6, plain, (![A_8]: (k2_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.81/2.99  tff(c_92, plain, (![A_8]: (k2_relat_1(k6_partfun1(A_8))=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_6])).
% 8.81/2.99  tff(c_22, plain, (![A_14]: (k2_relat_1(k5_relat_1(A_14, k2_funct_1(A_14)))=k1_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.81/2.99  tff(c_7761, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7696, c_22])).
% 8.81/2.99  tff(c_7778, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_142, c_80, c_7571, c_92, c_7761])).
% 8.81/2.99  tff(c_193, plain, (![A_74]: (k2_relat_1(k2_funct_1(A_74))=k1_relat_1(A_74) | ~v2_funct_1(A_74) | ~v1_funct_1(A_74) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.81/2.99  tff(c_8589, plain, (![A_426]: (k5_relat_1(k2_funct_1(A_426), k6_partfun1(k1_relat_1(A_426)))=k2_funct_1(A_426) | ~v1_relat_1(k2_funct_1(A_426)) | ~v2_funct_1(A_426) | ~v1_funct_1(A_426) | ~v1_relat_1(A_426))), inference(superposition, [status(thm), theory('equality')], [c_193, c_90])).
% 8.81/2.99  tff(c_8608, plain, (k5_relat_1(k2_funct_1('#skF_4'), k6_partfun1('#skF_2'))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7778, c_8589])).
% 8.81/2.99  tff(c_8630, plain, (k5_relat_1(k2_funct_1('#skF_4'), k6_partfun1('#skF_2'))=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_80, c_7571, c_8245, c_8608])).
% 8.81/2.99  tff(c_8638, plain, (k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1('#skF_4'))), k2_funct_1('#skF_4'))=k5_relat_1(k2_funct_1('#skF_4'), k6_partfun1('#skF_2')) | ~v1_relat_1(k6_partfun1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8630, c_372])).
% 8.81/2.99  tff(c_8645, plain, (k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1('#skF_4'))), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8245, c_140, c_8630, c_8638])).
% 8.81/2.99  tff(c_8685, plain, (k5_relat_1(k6_partfun1(k2_relat_1('#skF_4')), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_20, c_8645])).
% 8.81/2.99  tff(c_8705, plain, (k5_relat_1(k6_partfun1('#skF_1'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_80, c_7571, c_5087, c_8685])).
% 8.81/2.99  tff(c_8992, plain, (k5_relat_1('#skF_3', k5_relat_1('#skF_4', k2_funct_1('#skF_4')))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8986, c_8705])).
% 8.81/2.99  tff(c_9073, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8245, c_248, c_7696, c_8992])).
% 8.81/2.99  tff(c_7758, plain, (![C_7]: (k5_relat_1('#skF_4', k5_relat_1(k2_funct_1('#skF_4'), C_7))=k5_relat_1(k6_partfun1('#skF_2'), C_7) | ~v1_relat_1(C_7) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7696, c_2])).
% 8.81/2.99  tff(c_7776, plain, (![C_7]: (k5_relat_1('#skF_4', k5_relat_1(k2_funct_1('#skF_4'), C_7))=k5_relat_1(k6_partfun1('#skF_2'), C_7) | ~v1_relat_1(C_7) | ~v1_relat_1(k2_funct_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_7758])).
% 8.81/2.99  tff(c_9633, plain, (![C_433]: (k5_relat_1(k6_partfun1('#skF_2'), C_433)=k5_relat_1('#skF_4', k5_relat_1('#skF_3', C_433)) | ~v1_relat_1(C_433))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_9073, c_9073, c_7776])).
% 8.81/2.99  tff(c_7706, plain, (k2_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7692, c_22])).
% 8.81/2.99  tff(c_7723, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_141, c_86, c_70, c_92, c_7706])).
% 8.81/2.99  tff(c_8611, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7723, c_8589])).
% 8.81/2.99  tff(c_8632, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_86, c_70, c_8209, c_8611])).
% 8.81/2.99  tff(c_8652, plain, (k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1('#skF_3'))), k2_funct_1('#skF_3'))=k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1')) | ~v1_relat_1(k6_partfun1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_8632, c_372])).
% 8.81/2.99  tff(c_8659, plain, (k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1('#skF_3'))), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8209, c_140, c_8632, c_8652])).
% 8.81/2.99  tff(c_8756, plain, (k5_relat_1(k6_partfun1(k2_relat_1('#skF_3')), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20, c_8659])).
% 8.81/2.99  tff(c_8776, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_86, c_70, c_230, c_8756])).
% 8.81/2.99  tff(c_9650, plain, (k5_relat_1('#skF_4', k5_relat_1('#skF_3', k2_funct_1('#skF_3')))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_9633, c_8776])).
% 8.81/2.99  tff(c_9741, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8209, c_5096, c_7692, c_9650])).
% 8.81/2.99  tff(c_9743, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_9741])).
% 8.81/2.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.81/2.99  
% 8.81/2.99  Inference rules
% 8.81/2.99  ----------------------
% 8.81/2.99  #Ref     : 0
% 8.81/2.99  #Sup     : 2044
% 8.81/2.99  #Fact    : 0
% 8.81/2.99  #Define  : 0
% 8.81/2.99  #Split   : 37
% 8.81/2.99  #Chain   : 0
% 8.81/2.99  #Close   : 0
% 8.81/2.99  
% 8.81/2.99  Ordering : KBO
% 8.81/2.99  
% 8.81/2.99  Simplification rules
% 8.81/2.99  ----------------------
% 8.81/2.99  #Subsume      : 74
% 8.81/2.99  #Demod        : 3858
% 8.81/2.99  #Tautology    : 1090
% 8.81/2.99  #SimpNegUnit  : 88
% 8.81/2.99  #BackRed      : 102
% 8.81/2.99  
% 8.81/2.99  #Partial instantiations: 0
% 8.81/2.99  #Strategies tried      : 1
% 8.81/2.99  
% 8.81/2.99  Timing (in seconds)
% 8.81/2.99  ----------------------
% 8.81/2.99  Preprocessing        : 0.39
% 8.81/2.99  Parsing              : 0.22
% 8.81/2.99  CNF conversion       : 0.03
% 8.81/2.99  Main loop            : 1.74
% 8.81/2.99  Inferencing          : 0.56
% 8.81/2.99  Reduction            : 0.72
% 8.81/2.99  Demodulation         : 0.56
% 8.81/2.99  BG Simplification    : 0.06
% 8.81/2.99  Subsumption          : 0.28
% 8.81/2.99  Abstraction          : 0.08
% 8.81/2.99  MUC search           : 0.00
% 8.81/2.99  Cooper               : 0.00
% 8.81/2.99  Total                : 2.19
% 8.81/2.99  Index Insertion      : 0.00
% 8.81/2.99  Index Deletion       : 0.00
% 8.81/2.99  Index Matching       : 0.00
% 8.81/2.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
