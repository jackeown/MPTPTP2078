%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:02 EST 2020

% Result     : Theorem 4.76s
% Output     : CNFRefutation 4.76s
% Verified   : 
% Statistics : Number of formulae       :  144 (1097 expanded)
%              Number of leaves         :   46 ( 407 expanded)
%              Depth                    :   23
%              Number of atoms          :  334 (4584 expanded)
%              Number of equality atoms :  129 (1729 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_197,negated_conjecture,(
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

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_100,axiom,(
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

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_128,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_48,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(B) = k1_relat_1(A)
              & k5_relat_1(B,A) = k6_relat_1(k2_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_116,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_126,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_112,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_145,axiom,(
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

tff(f_31,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_171,axiom,(
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

tff(f_56,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(c_58,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_99,plain,(
    ! [C_57,A_58,B_59] :
      ( v1_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_110,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_99])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_72,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_191,plain,(
    ! [A_72,B_73,C_74,D_75] :
      ( k8_relset_1(A_72,B_73,C_74,D_75) = k10_relat_1(C_74,D_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_199,plain,(
    ! [D_75] : k8_relset_1('#skF_2','#skF_1','#skF_4',D_75) = k10_relat_1('#skF_4',D_75) ),
    inference(resolution,[status(thm)],[c_70,c_191])).

tff(c_265,plain,(
    ! [A_86,B_87,C_88] :
      ( k8_relset_1(A_86,B_87,C_88,B_87) = k1_relset_1(A_86,B_87,C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_269,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_4','#skF_1') = k1_relset_1('#skF_2','#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_265])).

tff(c_275,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k10_relat_1('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_269])).

tff(c_334,plain,(
    ! [B_98,A_99,C_100] :
      ( k1_xboole_0 = B_98
      | k1_relset_1(A_99,B_98,C_100) = A_99
      | ~ v1_funct_2(C_100,A_99,B_98)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_99,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_340,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_334])).

tff(c_348,plain,
    ( k1_xboole_0 = '#skF_1'
    | k10_relat_1('#skF_4','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_275,c_340])).

tff(c_349,plain,(
    k10_relat_1('#skF_4','#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_348])).

tff(c_76,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_111,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_99])).

tff(c_80,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_64,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_78,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_68,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_149,plain,(
    ! [A_66,B_67,C_68] :
      ( k2_relset_1(A_66,B_67,C_68) = k2_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_158,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_149])).

tff(c_162,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_158])).

tff(c_2,plain,(
    ! [A_1] :
      ( k10_relat_1(A_1,k2_relat_1(A_1)) = k1_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_166,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_2])).

tff(c_170,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_166])).

tff(c_200,plain,(
    ! [D_75] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_75) = k10_relat_1('#skF_3',D_75) ),
    inference(resolution,[status(thm)],[c_76,c_191])).

tff(c_271,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') = k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_265])).

tff(c_277,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_200,c_271])).

tff(c_343,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_334])).

tff(c_352,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_277,c_343])).

tff(c_353,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_352])).

tff(c_46,plain,(
    ! [A_40] : k6_relat_1(A_40) = k6_partfun1(A_40) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_6,plain,(
    ! [A_3,B_5] :
      ( k2_funct_1(A_3) = B_5
      | k6_relat_1(k2_relat_1(A_3)) != k5_relat_1(B_5,A_3)
      | k2_relat_1(B_5) != k1_relat_1(A_3)
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(B_5)
      | ~ v1_relat_1(B_5)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_618,plain,(
    ! [A_140,B_141] :
      ( k2_funct_1(A_140) = B_141
      | k6_partfun1(k2_relat_1(A_140)) != k5_relat_1(B_141,A_140)
      | k2_relat_1(B_141) != k1_relat_1(A_140)
      | ~ v2_funct_1(A_140)
      | ~ v1_funct_1(B_141)
      | ~ v1_relat_1(B_141)
      | ~ v1_funct_1(A_140)
      | ~ v1_relat_1(A_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6])).

tff(c_620,plain,(
    ! [B_141] :
      ( k2_funct_1('#skF_3') = B_141
      | k5_relat_1(B_141,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_141) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_141)
      | ~ v1_relat_1(B_141)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_618])).

tff(c_623,plain,(
    ! [B_142] :
      ( k2_funct_1('#skF_3') = B_142
      | k5_relat_1(B_142,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_142) != '#skF_1'
      | ~ v1_funct_1(B_142)
      | ~ v1_relat_1(B_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_80,c_64,c_353,c_620])).

tff(c_632,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_110,c_623])).

tff(c_639,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_632])).

tff(c_640,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_639])).

tff(c_641,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_640])).

tff(c_42,plain,(
    ! [A_33] : m1_subset_1(k6_partfun1(A_33),k1_zfmisc_1(k2_zfmisc_1(A_33,A_33))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_139,plain,(
    ! [A_63,B_64,D_65] :
      ( r2_relset_1(A_63,B_64,D_65,D_65)
      | ~ m1_subset_1(D_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_146,plain,(
    ! [A_33] : r2_relset_1(A_33,A_33,k6_partfun1(A_33),k6_partfun1(A_33)) ),
    inference(resolution,[status(thm)],[c_42,c_139])).

tff(c_160,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_149])).

tff(c_481,plain,(
    ! [B_126,F_124,A_122,D_123,E_125,C_127] :
      ( k1_partfun1(A_122,B_126,C_127,D_123,E_125,F_124) = k5_relat_1(E_125,F_124)
      | ~ m1_subset_1(F_124,k1_zfmisc_1(k2_zfmisc_1(C_127,D_123)))
      | ~ v1_funct_1(F_124)
      | ~ m1_subset_1(E_125,k1_zfmisc_1(k2_zfmisc_1(A_122,B_126)))
      | ~ v1_funct_1(E_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_485,plain,(
    ! [A_122,B_126,E_125] :
      ( k1_partfun1(A_122,B_126,'#skF_2','#skF_1',E_125,'#skF_4') = k5_relat_1(E_125,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_125,k1_zfmisc_1(k2_zfmisc_1(A_122,B_126)))
      | ~ v1_funct_1(E_125) ) ),
    inference(resolution,[status(thm)],[c_70,c_481])).

tff(c_497,plain,(
    ! [A_130,B_131,E_132] :
      ( k1_partfun1(A_130,B_131,'#skF_2','#skF_1',E_132,'#skF_4') = k5_relat_1(E_132,'#skF_4')
      | ~ m1_subset_1(E_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131)))
      | ~ v1_funct_1(E_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_485])).

tff(c_506,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_497])).

tff(c_513,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_506])).

tff(c_66,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_365,plain,(
    ! [D_101,C_102,A_103,B_104] :
      ( D_101 = C_102
      | ~ r2_relset_1(A_103,B_104,C_102,D_101)
      | ~ m1_subset_1(D_101,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104)))
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_373,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_66,c_365])).

tff(c_388,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_373])).

tff(c_401,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_388])).

tff(c_520,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_401])).

tff(c_531,plain,(
    ! [B_137,A_138,C_134,E_136,D_135,F_133] :
      ( m1_subset_1(k1_partfun1(A_138,B_137,C_134,D_135,E_136,F_133),k1_zfmisc_1(k2_zfmisc_1(A_138,D_135)))
      | ~ m1_subset_1(F_133,k1_zfmisc_1(k2_zfmisc_1(C_134,D_135)))
      | ~ v1_funct_1(F_133)
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1(A_138,B_137)))
      | ~ v1_funct_1(E_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_579,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_513,c_531])).

tff(c_600,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_579])).

tff(c_603,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_520,c_600])).

tff(c_604,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_388])).

tff(c_1082,plain,(
    ! [A_183,B_184,C_185,D_186] :
      ( k2_relset_1(A_183,B_184,C_185) = B_184
      | ~ r2_relset_1(B_184,B_184,k1_partfun1(B_184,A_183,A_183,B_184,D_186,C_185),k6_partfun1(B_184))
      | ~ m1_subset_1(D_186,k1_zfmisc_1(k2_zfmisc_1(B_184,A_183)))
      | ~ v1_funct_2(D_186,B_184,A_183)
      | ~ v1_funct_1(D_186)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184)))
      | ~ v1_funct_2(C_185,A_183,B_184)
      | ~ v1_funct_1(C_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1085,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_604,c_1082])).

tff(c_1087,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_80,c_78,c_76,c_146,c_160,c_1085])).

tff(c_1089,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_641,c_1087])).

tff(c_1091,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_640])).

tff(c_1099,plain,
    ( k10_relat_1('#skF_4','#skF_1') = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1091,c_2])).

tff(c_1105,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_349,c_1099])).

tff(c_81,plain,(
    ! [A_3,B_5] :
      ( k2_funct_1(A_3) = B_5
      | k6_partfun1(k2_relat_1(A_3)) != k5_relat_1(B_5,A_3)
      | k2_relat_1(B_5) != k1_relat_1(A_3)
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(B_5)
      | ~ v1_relat_1(B_5)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6])).

tff(c_1096,plain,(
    ! [B_5] :
      ( k2_funct_1('#skF_4') = B_5
      | k5_relat_1(B_5,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_5) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_5)
      | ~ v1_relat_1(B_5)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1091,c_81])).

tff(c_1103,plain,(
    ! [B_5] :
      ( k2_funct_1('#skF_4') = B_5
      | k5_relat_1(B_5,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_5) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_5)
      | ~ v1_relat_1(B_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_74,c_1096])).

tff(c_1121,plain,(
    ! [B_5] :
      ( k2_funct_1('#skF_4') = B_5
      | k5_relat_1(B_5,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_5) != '#skF_2'
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_5)
      | ~ v1_relat_1(B_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1105,c_1103])).

tff(c_1122,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1121])).

tff(c_4,plain,(
    ! [A_2] : v2_funct_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_82,plain,(
    ! [A_2] : v2_funct_1(k6_partfun1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_4])).

tff(c_1561,plain,(
    ! [E_227,C_230,B_228,D_229,A_231] :
      ( k1_xboole_0 = C_230
      | v2_funct_1(E_227)
      | k2_relset_1(A_231,B_228,D_229) != B_228
      | ~ v2_funct_1(k1_partfun1(A_231,B_228,B_228,C_230,D_229,E_227))
      | ~ m1_subset_1(E_227,k1_zfmisc_1(k2_zfmisc_1(B_228,C_230)))
      | ~ v1_funct_2(E_227,B_228,C_230)
      | ~ v1_funct_1(E_227)
      | ~ m1_subset_1(D_229,k1_zfmisc_1(k2_zfmisc_1(A_231,B_228)))
      | ~ v1_funct_2(D_229,A_231,B_228)
      | ~ v1_funct_1(D_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_1563,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_604,c_1561])).

tff(c_1565,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_74,c_72,c_70,c_82,c_68,c_1563])).

tff(c_1567,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1122,c_62,c_1565])).

tff(c_1569,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1121])).

tff(c_1570,plain,(
    ! [B_232] :
      ( k2_funct_1('#skF_4') = B_232
      | k5_relat_1(B_232,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_232) != '#skF_2'
      | ~ v1_funct_1(B_232)
      | ~ v1_relat_1(B_232) ) ),
    inference(splitRight,[status(thm)],[c_1121])).

tff(c_1576,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_111,c_1570])).

tff(c_1583,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_162,c_1576])).

tff(c_1587,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1583])).

tff(c_1628,plain,(
    ! [C_248,A_243,D_244,B_247,F_245,E_246] :
      ( k1_partfun1(A_243,B_247,C_248,D_244,E_246,F_245) = k5_relat_1(E_246,F_245)
      | ~ m1_subset_1(F_245,k1_zfmisc_1(k2_zfmisc_1(C_248,D_244)))
      | ~ v1_funct_1(F_245)
      | ~ m1_subset_1(E_246,k1_zfmisc_1(k2_zfmisc_1(A_243,B_247)))
      | ~ v1_funct_1(E_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1632,plain,(
    ! [A_243,B_247,E_246] :
      ( k1_partfun1(A_243,B_247,'#skF_2','#skF_1',E_246,'#skF_4') = k5_relat_1(E_246,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_246,k1_zfmisc_1(k2_zfmisc_1(A_243,B_247)))
      | ~ v1_funct_1(E_246) ) ),
    inference(resolution,[status(thm)],[c_70,c_1628])).

tff(c_1989,plain,(
    ! [A_278,B_279,E_280] :
      ( k1_partfun1(A_278,B_279,'#skF_2','#skF_1',E_280,'#skF_4') = k5_relat_1(E_280,'#skF_4')
      | ~ m1_subset_1(E_280,k1_zfmisc_1(k2_zfmisc_1(A_278,B_279)))
      | ~ v1_funct_1(E_280) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1632])).

tff(c_2007,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_1989])).

tff(c_2021,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_604,c_2007])).

tff(c_2023,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1587,c_2021])).

tff(c_2024,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1583])).

tff(c_8,plain,(
    ! [A_6] :
      ( k2_funct_1(k2_funct_1(A_6)) = A_6
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2030,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2024,c_8])).

tff(c_2034,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_74,c_1569,c_2030])).

tff(c_2036,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2034])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:31:14 EST 2020
% 0.18/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.76/1.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.76/1.84  
% 4.76/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.76/1.84  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.76/1.84  
% 4.76/1.84  %Foreground sorts:
% 4.76/1.84  
% 4.76/1.84  
% 4.76/1.84  %Background operators:
% 4.76/1.84  
% 4.76/1.84  
% 4.76/1.84  %Foreground operators:
% 4.76/1.84  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.76/1.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.76/1.84  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.76/1.84  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.76/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.76/1.84  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.76/1.84  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.76/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.76/1.84  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.76/1.84  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.76/1.84  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.76/1.84  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.76/1.84  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.76/1.84  tff('#skF_2', type, '#skF_2': $i).
% 4.76/1.84  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.76/1.84  tff('#skF_3', type, '#skF_3': $i).
% 4.76/1.84  tff('#skF_1', type, '#skF_1': $i).
% 4.76/1.84  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.76/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.76/1.84  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.76/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.76/1.84  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.76/1.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.76/1.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.76/1.84  tff('#skF_4', type, '#skF_4': $i).
% 4.76/1.84  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.76/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.76/1.84  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.76/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.76/1.84  
% 4.76/1.86  tff(f_197, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 4.76/1.86  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.76/1.86  tff(f_68, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.76/1.86  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 4.76/1.86  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.76/1.86  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.76/1.86  tff(f_29, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 4.76/1.86  tff(f_128, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.76/1.86  tff(f_48, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 4.76/1.86  tff(f_116, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.76/1.86  tff(f_76, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.76/1.86  tff(f_126, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.76/1.86  tff(f_112, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.76/1.86  tff(f_145, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 4.76/1.86  tff(f_31, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 4.76/1.86  tff(f_171, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 4.76/1.86  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 4.76/1.86  tff(c_58, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.76/1.86  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.76/1.86  tff(c_99, plain, (![C_57, A_58, B_59]: (v1_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.76/1.86  tff(c_110, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_99])).
% 4.76/1.86  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.76/1.86  tff(c_62, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.76/1.86  tff(c_72, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.76/1.86  tff(c_191, plain, (![A_72, B_73, C_74, D_75]: (k8_relset_1(A_72, B_73, C_74, D_75)=k10_relat_1(C_74, D_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.76/1.86  tff(c_199, plain, (![D_75]: (k8_relset_1('#skF_2', '#skF_1', '#skF_4', D_75)=k10_relat_1('#skF_4', D_75))), inference(resolution, [status(thm)], [c_70, c_191])).
% 4.76/1.86  tff(c_265, plain, (![A_86, B_87, C_88]: (k8_relset_1(A_86, B_87, C_88, B_87)=k1_relset_1(A_86, B_87, C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.76/1.86  tff(c_269, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_1')=k1_relset_1('#skF_2', '#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_70, c_265])).
% 4.76/1.86  tff(c_275, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k10_relat_1('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_269])).
% 4.76/1.86  tff(c_334, plain, (![B_98, A_99, C_100]: (k1_xboole_0=B_98 | k1_relset_1(A_99, B_98, C_100)=A_99 | ~v1_funct_2(C_100, A_99, B_98) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_99, B_98))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.76/1.86  tff(c_340, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_70, c_334])).
% 4.76/1.86  tff(c_348, plain, (k1_xboole_0='#skF_1' | k10_relat_1('#skF_4', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_275, c_340])).
% 4.76/1.86  tff(c_349, plain, (k10_relat_1('#skF_4', '#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_62, c_348])).
% 4.76/1.86  tff(c_76, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.76/1.86  tff(c_111, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_99])).
% 4.76/1.86  tff(c_80, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.76/1.86  tff(c_64, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.76/1.86  tff(c_60, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.76/1.86  tff(c_78, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.76/1.86  tff(c_68, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.76/1.86  tff(c_149, plain, (![A_66, B_67, C_68]: (k2_relset_1(A_66, B_67, C_68)=k2_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.76/1.86  tff(c_158, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_149])).
% 4.76/1.86  tff(c_162, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_158])).
% 4.76/1.86  tff(c_2, plain, (![A_1]: (k10_relat_1(A_1, k2_relat_1(A_1))=k1_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.76/1.86  tff(c_166, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_162, c_2])).
% 4.76/1.86  tff(c_170, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_166])).
% 4.76/1.86  tff(c_200, plain, (![D_75]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_75)=k10_relat_1('#skF_3', D_75))), inference(resolution, [status(thm)], [c_76, c_191])).
% 4.76/1.86  tff(c_271, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_76, c_265])).
% 4.76/1.86  tff(c_277, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_170, c_200, c_271])).
% 4.76/1.86  tff(c_343, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_76, c_334])).
% 4.76/1.86  tff(c_352, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_277, c_343])).
% 4.76/1.86  tff(c_353, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_60, c_352])).
% 4.76/1.86  tff(c_46, plain, (![A_40]: (k6_relat_1(A_40)=k6_partfun1(A_40))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.76/1.86  tff(c_6, plain, (![A_3, B_5]: (k2_funct_1(A_3)=B_5 | k6_relat_1(k2_relat_1(A_3))!=k5_relat_1(B_5, A_3) | k2_relat_1(B_5)!=k1_relat_1(A_3) | ~v2_funct_1(A_3) | ~v1_funct_1(B_5) | ~v1_relat_1(B_5) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.76/1.86  tff(c_618, plain, (![A_140, B_141]: (k2_funct_1(A_140)=B_141 | k6_partfun1(k2_relat_1(A_140))!=k5_relat_1(B_141, A_140) | k2_relat_1(B_141)!=k1_relat_1(A_140) | ~v2_funct_1(A_140) | ~v1_funct_1(B_141) | ~v1_relat_1(B_141) | ~v1_funct_1(A_140) | ~v1_relat_1(A_140))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_6])).
% 4.76/1.86  tff(c_620, plain, (![B_141]: (k2_funct_1('#skF_3')=B_141 | k5_relat_1(B_141, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_141)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_141) | ~v1_relat_1(B_141) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_162, c_618])).
% 4.76/1.86  tff(c_623, plain, (![B_142]: (k2_funct_1('#skF_3')=B_142 | k5_relat_1(B_142, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_142)!='#skF_1' | ~v1_funct_1(B_142) | ~v1_relat_1(B_142))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_80, c_64, c_353, c_620])).
% 4.76/1.86  tff(c_632, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_110, c_623])).
% 4.76/1.86  tff(c_639, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_632])).
% 4.76/1.86  tff(c_640, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_58, c_639])).
% 4.76/1.86  tff(c_641, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_640])).
% 4.76/1.86  tff(c_42, plain, (![A_33]: (m1_subset_1(k6_partfun1(A_33), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.76/1.86  tff(c_139, plain, (![A_63, B_64, D_65]: (r2_relset_1(A_63, B_64, D_65, D_65) | ~m1_subset_1(D_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.76/1.86  tff(c_146, plain, (![A_33]: (r2_relset_1(A_33, A_33, k6_partfun1(A_33), k6_partfun1(A_33)))), inference(resolution, [status(thm)], [c_42, c_139])).
% 4.76/1.86  tff(c_160, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_149])).
% 4.76/1.86  tff(c_481, plain, (![B_126, F_124, A_122, D_123, E_125, C_127]: (k1_partfun1(A_122, B_126, C_127, D_123, E_125, F_124)=k5_relat_1(E_125, F_124) | ~m1_subset_1(F_124, k1_zfmisc_1(k2_zfmisc_1(C_127, D_123))) | ~v1_funct_1(F_124) | ~m1_subset_1(E_125, k1_zfmisc_1(k2_zfmisc_1(A_122, B_126))) | ~v1_funct_1(E_125))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.76/1.86  tff(c_485, plain, (![A_122, B_126, E_125]: (k1_partfun1(A_122, B_126, '#skF_2', '#skF_1', E_125, '#skF_4')=k5_relat_1(E_125, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_125, k1_zfmisc_1(k2_zfmisc_1(A_122, B_126))) | ~v1_funct_1(E_125))), inference(resolution, [status(thm)], [c_70, c_481])).
% 4.76/1.86  tff(c_497, plain, (![A_130, B_131, E_132]: (k1_partfun1(A_130, B_131, '#skF_2', '#skF_1', E_132, '#skF_4')=k5_relat_1(E_132, '#skF_4') | ~m1_subset_1(E_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))) | ~v1_funct_1(E_132))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_485])).
% 4.76/1.86  tff(c_506, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_497])).
% 4.76/1.86  tff(c_513, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_506])).
% 4.76/1.86  tff(c_66, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.76/1.86  tff(c_365, plain, (![D_101, C_102, A_103, B_104]: (D_101=C_102 | ~r2_relset_1(A_103, B_104, C_102, D_101) | ~m1_subset_1(D_101, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.76/1.86  tff(c_373, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_66, c_365])).
% 4.76/1.86  tff(c_388, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_373])).
% 4.76/1.86  tff(c_401, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_388])).
% 4.76/1.86  tff(c_520, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_513, c_401])).
% 4.76/1.86  tff(c_531, plain, (![B_137, A_138, C_134, E_136, D_135, F_133]: (m1_subset_1(k1_partfun1(A_138, B_137, C_134, D_135, E_136, F_133), k1_zfmisc_1(k2_zfmisc_1(A_138, D_135))) | ~m1_subset_1(F_133, k1_zfmisc_1(k2_zfmisc_1(C_134, D_135))) | ~v1_funct_1(F_133) | ~m1_subset_1(E_136, k1_zfmisc_1(k2_zfmisc_1(A_138, B_137))) | ~v1_funct_1(E_136))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.76/1.86  tff(c_579, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_513, c_531])).
% 4.76/1.86  tff(c_600, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_579])).
% 4.76/1.86  tff(c_603, plain, $false, inference(negUnitSimplification, [status(thm)], [c_520, c_600])).
% 4.76/1.86  tff(c_604, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_388])).
% 4.76/1.86  tff(c_1082, plain, (![A_183, B_184, C_185, D_186]: (k2_relset_1(A_183, B_184, C_185)=B_184 | ~r2_relset_1(B_184, B_184, k1_partfun1(B_184, A_183, A_183, B_184, D_186, C_185), k6_partfun1(B_184)) | ~m1_subset_1(D_186, k1_zfmisc_1(k2_zfmisc_1(B_184, A_183))) | ~v1_funct_2(D_186, B_184, A_183) | ~v1_funct_1(D_186) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))) | ~v1_funct_2(C_185, A_183, B_184) | ~v1_funct_1(C_185))), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.76/1.86  tff(c_1085, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_604, c_1082])).
% 4.76/1.86  tff(c_1087, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_80, c_78, c_76, c_146, c_160, c_1085])).
% 4.76/1.86  tff(c_1089, plain, $false, inference(negUnitSimplification, [status(thm)], [c_641, c_1087])).
% 4.76/1.86  tff(c_1091, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_640])).
% 4.76/1.86  tff(c_1099, plain, (k10_relat_1('#skF_4', '#skF_1')=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1091, c_2])).
% 4.76/1.86  tff(c_1105, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_349, c_1099])).
% 4.76/1.86  tff(c_81, plain, (![A_3, B_5]: (k2_funct_1(A_3)=B_5 | k6_partfun1(k2_relat_1(A_3))!=k5_relat_1(B_5, A_3) | k2_relat_1(B_5)!=k1_relat_1(A_3) | ~v2_funct_1(A_3) | ~v1_funct_1(B_5) | ~v1_relat_1(B_5) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_6])).
% 4.76/1.86  tff(c_1096, plain, (![B_5]: (k2_funct_1('#skF_4')=B_5 | k5_relat_1(B_5, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_5)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_5) | ~v1_relat_1(B_5) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1091, c_81])).
% 4.76/1.86  tff(c_1103, plain, (![B_5]: (k2_funct_1('#skF_4')=B_5 | k5_relat_1(B_5, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_5)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_5) | ~v1_relat_1(B_5))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_74, c_1096])).
% 4.76/1.86  tff(c_1121, plain, (![B_5]: (k2_funct_1('#skF_4')=B_5 | k5_relat_1(B_5, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_5)!='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_5) | ~v1_relat_1(B_5))), inference(demodulation, [status(thm), theory('equality')], [c_1105, c_1103])).
% 4.76/1.86  tff(c_1122, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1121])).
% 4.76/1.86  tff(c_4, plain, (![A_2]: (v2_funct_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.76/1.86  tff(c_82, plain, (![A_2]: (v2_funct_1(k6_partfun1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_4])).
% 4.76/1.86  tff(c_1561, plain, (![E_227, C_230, B_228, D_229, A_231]: (k1_xboole_0=C_230 | v2_funct_1(E_227) | k2_relset_1(A_231, B_228, D_229)!=B_228 | ~v2_funct_1(k1_partfun1(A_231, B_228, B_228, C_230, D_229, E_227)) | ~m1_subset_1(E_227, k1_zfmisc_1(k2_zfmisc_1(B_228, C_230))) | ~v1_funct_2(E_227, B_228, C_230) | ~v1_funct_1(E_227) | ~m1_subset_1(D_229, k1_zfmisc_1(k2_zfmisc_1(A_231, B_228))) | ~v1_funct_2(D_229, A_231, B_228) | ~v1_funct_1(D_229))), inference(cnfTransformation, [status(thm)], [f_171])).
% 4.76/1.86  tff(c_1563, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_604, c_1561])).
% 4.76/1.86  tff(c_1565, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_74, c_72, c_70, c_82, c_68, c_1563])).
% 4.76/1.86  tff(c_1567, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1122, c_62, c_1565])).
% 4.76/1.86  tff(c_1569, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_1121])).
% 4.76/1.86  tff(c_1570, plain, (![B_232]: (k2_funct_1('#skF_4')=B_232 | k5_relat_1(B_232, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_232)!='#skF_2' | ~v1_funct_1(B_232) | ~v1_relat_1(B_232))), inference(splitRight, [status(thm)], [c_1121])).
% 4.76/1.86  tff(c_1576, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_111, c_1570])).
% 4.76/1.86  tff(c_1583, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_162, c_1576])).
% 4.76/1.86  tff(c_1587, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_1583])).
% 4.76/1.86  tff(c_1628, plain, (![C_248, A_243, D_244, B_247, F_245, E_246]: (k1_partfun1(A_243, B_247, C_248, D_244, E_246, F_245)=k5_relat_1(E_246, F_245) | ~m1_subset_1(F_245, k1_zfmisc_1(k2_zfmisc_1(C_248, D_244))) | ~v1_funct_1(F_245) | ~m1_subset_1(E_246, k1_zfmisc_1(k2_zfmisc_1(A_243, B_247))) | ~v1_funct_1(E_246))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.76/1.86  tff(c_1632, plain, (![A_243, B_247, E_246]: (k1_partfun1(A_243, B_247, '#skF_2', '#skF_1', E_246, '#skF_4')=k5_relat_1(E_246, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_246, k1_zfmisc_1(k2_zfmisc_1(A_243, B_247))) | ~v1_funct_1(E_246))), inference(resolution, [status(thm)], [c_70, c_1628])).
% 4.76/1.86  tff(c_1989, plain, (![A_278, B_279, E_280]: (k1_partfun1(A_278, B_279, '#skF_2', '#skF_1', E_280, '#skF_4')=k5_relat_1(E_280, '#skF_4') | ~m1_subset_1(E_280, k1_zfmisc_1(k2_zfmisc_1(A_278, B_279))) | ~v1_funct_1(E_280))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1632])).
% 4.76/1.86  tff(c_2007, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_1989])).
% 4.76/1.86  tff(c_2021, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_604, c_2007])).
% 4.76/1.86  tff(c_2023, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1587, c_2021])).
% 4.76/1.86  tff(c_2024, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_1583])).
% 4.76/1.86  tff(c_8, plain, (![A_6]: (k2_funct_1(k2_funct_1(A_6))=A_6 | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.76/1.86  tff(c_2030, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2024, c_8])).
% 4.76/1.86  tff(c_2034, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_74, c_1569, c_2030])).
% 4.76/1.86  tff(c_2036, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_2034])).
% 4.76/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.76/1.86  
% 4.76/1.86  Inference rules
% 4.76/1.86  ----------------------
% 4.76/1.86  #Ref     : 0
% 4.76/1.86  #Sup     : 443
% 4.76/1.86  #Fact    : 0
% 4.76/1.86  #Define  : 0
% 4.76/1.86  #Split   : 19
% 4.76/1.86  #Chain   : 0
% 4.76/1.86  #Close   : 0
% 4.76/1.86  
% 4.76/1.86  Ordering : KBO
% 4.76/1.86  
% 4.76/1.86  Simplification rules
% 4.76/1.86  ----------------------
% 4.76/1.86  #Subsume      : 2
% 4.76/1.86  #Demod        : 283
% 4.76/1.86  #Tautology    : 138
% 4.76/1.86  #SimpNegUnit  : 34
% 4.76/1.86  #BackRed      : 20
% 4.76/1.86  
% 4.76/1.86  #Partial instantiations: 0
% 4.76/1.86  #Strategies tried      : 1
% 4.76/1.86  
% 4.76/1.86  Timing (in seconds)
% 4.76/1.86  ----------------------
% 4.76/1.87  Preprocessing        : 0.38
% 4.76/1.87  Parsing              : 0.20
% 4.76/1.87  CNF conversion       : 0.03
% 4.76/1.87  Main loop            : 0.72
% 4.76/1.87  Inferencing          : 0.25
% 4.76/1.87  Reduction            : 0.26
% 4.76/1.87  Demodulation         : 0.19
% 4.76/1.87  BG Simplification    : 0.04
% 4.76/1.87  Subsumption          : 0.12
% 4.76/1.87  Abstraction          : 0.03
% 4.76/1.87  MUC search           : 0.00
% 4.76/1.87  Cooper               : 0.00
% 4.76/1.87  Total                : 1.14
% 4.76/1.87  Index Insertion      : 0.00
% 4.76/1.87  Index Deletion       : 0.00
% 4.76/1.87  Index Matching       : 0.00
% 4.76/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
