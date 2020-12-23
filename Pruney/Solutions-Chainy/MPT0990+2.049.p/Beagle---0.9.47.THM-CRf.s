%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:02 EST 2020

% Result     : Theorem 4.58s
% Output     : CNFRefutation 4.99s
% Verified   : 
% Statistics : Number of formulae       :  144 (1111 expanded)
%              Number of leaves         :   45 ( 411 expanded)
%              Depth                    :   23
%              Number of atoms          :  335 (4595 expanded)
%              Number of equality atoms :  129 (1739 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_104,axiom,(
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

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_128,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_50,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_80,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_126,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_116,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

tff(f_58,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(c_58,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_101,plain,(
    ! [C_57,A_58,B_59] :
      ( v1_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_113,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_101])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_72,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_200,plain,(
    ! [A_73,B_74,C_75,D_76] :
      ( k8_relset_1(A_73,B_74,C_75,D_76) = k10_relat_1(C_75,D_76)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_208,plain,(
    ! [D_76] : k8_relset_1('#skF_2','#skF_1','#skF_4',D_76) = k10_relat_1('#skF_4',D_76) ),
    inference(resolution,[status(thm)],[c_70,c_200])).

tff(c_252,plain,(
    ! [A_85,B_86,C_87] :
      ( k8_relset_1(A_85,B_86,C_87,B_86) = k1_relset_1(A_85,B_86,C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_256,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_4','#skF_1') = k1_relset_1('#skF_2','#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_252])).

tff(c_262,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k10_relat_1('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_256])).

tff(c_336,plain,(
    ! [B_97,A_98,C_99] :
      ( k1_xboole_0 = B_97
      | k1_relset_1(A_98,B_97,C_99) = A_98
      | ~ v1_funct_2(C_99,A_98,B_97)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_98,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_342,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_336])).

tff(c_350,plain,
    ( k1_xboole_0 = '#skF_1'
    | k10_relat_1('#skF_4','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_262,c_342])).

tff(c_351,plain,(
    k10_relat_1('#skF_4','#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_350])).

tff(c_76,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_114,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_101])).

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

tff(c_153,plain,(
    ! [A_67,B_68,C_69] :
      ( k2_relset_1(A_67,B_68,C_69) = k2_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_162,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_153])).

tff(c_166,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_162])).

tff(c_2,plain,(
    ! [A_1] :
      ( k10_relat_1(A_1,k2_relat_1(A_1)) = k1_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_170,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_2])).

tff(c_174,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_170])).

tff(c_209,plain,(
    ! [D_76] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_76) = k10_relat_1('#skF_3',D_76) ),
    inference(resolution,[status(thm)],[c_76,c_200])).

tff(c_258,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') = k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_252])).

tff(c_264,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_209,c_258])).

tff(c_345,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_336])).

tff(c_354,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_264,c_345])).

tff(c_355,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_354])).

tff(c_46,plain,(
    ! [A_40] : k6_relat_1(A_40) = k6_partfun1(A_40) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_8,plain,(
    ! [A_3,B_5] :
      ( k2_funct_1(A_3) = B_5
      | k6_relat_1(k2_relat_1(A_3)) != k5_relat_1(B_5,A_3)
      | k2_relat_1(B_5) != k1_relat_1(A_3)
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(B_5)
      | ~ v1_relat_1(B_5)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_620,plain,(
    ! [A_139,B_140] :
      ( k2_funct_1(A_139) = B_140
      | k6_partfun1(k2_relat_1(A_139)) != k5_relat_1(B_140,A_139)
      | k2_relat_1(B_140) != k1_relat_1(A_139)
      | ~ v2_funct_1(A_139)
      | ~ v1_funct_1(B_140)
      | ~ v1_relat_1(B_140)
      | ~ v1_funct_1(A_139)
      | ~ v1_relat_1(A_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8])).

tff(c_622,plain,(
    ! [B_140] :
      ( k2_funct_1('#skF_3') = B_140
      | k5_relat_1(B_140,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_140) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_140)
      | ~ v1_relat_1(B_140)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_620])).

tff(c_625,plain,(
    ! [B_141] :
      ( k2_funct_1('#skF_3') = B_141
      | k5_relat_1(B_141,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_141) != '#skF_1'
      | ~ v1_funct_1(B_141)
      | ~ v1_relat_1(B_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_80,c_64,c_355,c_622])).

tff(c_631,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_113,c_625])).

tff(c_640,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_631])).

tff(c_641,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_640])).

tff(c_643,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_641])).

tff(c_22,plain,(
    ! [A_21] : m1_subset_1(k6_relat_1(A_21),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_81,plain,(
    ! [A_21] : m1_subset_1(k6_partfun1(A_21),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_22])).

tff(c_141,plain,(
    ! [A_62,B_63,D_64] :
      ( r2_relset_1(A_62,B_63,D_64,D_64)
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_148,plain,(
    ! [A_21] : r2_relset_1(A_21,A_21,k6_partfun1(A_21),k6_partfun1(A_21)) ),
    inference(resolution,[status(thm)],[c_81,c_141])).

tff(c_164,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_153])).

tff(c_483,plain,(
    ! [C_126,D_122,A_121,B_125,F_123,E_124] :
      ( k1_partfun1(A_121,B_125,C_126,D_122,E_124,F_123) = k5_relat_1(E_124,F_123)
      | ~ m1_subset_1(F_123,k1_zfmisc_1(k2_zfmisc_1(C_126,D_122)))
      | ~ v1_funct_1(F_123)
      | ~ m1_subset_1(E_124,k1_zfmisc_1(k2_zfmisc_1(A_121,B_125)))
      | ~ v1_funct_1(E_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_487,plain,(
    ! [A_121,B_125,E_124] :
      ( k1_partfun1(A_121,B_125,'#skF_2','#skF_1',E_124,'#skF_4') = k5_relat_1(E_124,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_124,k1_zfmisc_1(k2_zfmisc_1(A_121,B_125)))
      | ~ v1_funct_1(E_124) ) ),
    inference(resolution,[status(thm)],[c_70,c_483])).

tff(c_499,plain,(
    ! [A_129,B_130,E_131] :
      ( k1_partfun1(A_129,B_130,'#skF_2','#skF_1',E_131,'#skF_4') = k5_relat_1(E_131,'#skF_4')
      | ~ m1_subset_1(E_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130)))
      | ~ v1_funct_1(E_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_487])).

tff(c_508,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_499])).

tff(c_515,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_508])).

tff(c_66,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_367,plain,(
    ! [D_100,C_101,A_102,B_103] :
      ( D_100 = C_101
      | ~ r2_relset_1(A_102,B_103,C_101,D_100)
      | ~ m1_subset_1(D_100,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103)))
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_375,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_66,c_367])).

tff(c_390,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_375])).

tff(c_403,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_390])).

tff(c_522,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_515,c_403])).

tff(c_533,plain,(
    ! [A_134,D_137,E_133,B_136,F_132,C_135] :
      ( m1_subset_1(k1_partfun1(A_134,B_136,C_135,D_137,E_133,F_132),k1_zfmisc_1(k2_zfmisc_1(A_134,D_137)))
      | ~ m1_subset_1(F_132,k1_zfmisc_1(k2_zfmisc_1(C_135,D_137)))
      | ~ v1_funct_1(F_132)
      | ~ m1_subset_1(E_133,k1_zfmisc_1(k2_zfmisc_1(A_134,B_136)))
      | ~ v1_funct_1(E_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_581,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_515,c_533])).

tff(c_602,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_581])).

tff(c_605,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_522,c_602])).

tff(c_606,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_390])).

tff(c_1084,plain,(
    ! [A_182,B_183,C_184,D_185] :
      ( k2_relset_1(A_182,B_183,C_184) = B_183
      | ~ r2_relset_1(B_183,B_183,k1_partfun1(B_183,A_182,A_182,B_183,D_185,C_184),k6_partfun1(B_183))
      | ~ m1_subset_1(D_185,k1_zfmisc_1(k2_zfmisc_1(B_183,A_182)))
      | ~ v1_funct_2(D_185,B_183,A_182)
      | ~ v1_funct_1(D_185)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_182,B_183)))
      | ~ v1_funct_2(C_184,A_182,B_183)
      | ~ v1_funct_1(C_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1087,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_606,c_1084])).

tff(c_1089,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_80,c_78,c_76,c_148,c_164,c_1087])).

tff(c_1091,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_643,c_1089])).

tff(c_1093,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_641])).

tff(c_1101,plain,
    ( k10_relat_1('#skF_4','#skF_1') = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1093,c_2])).

tff(c_1107,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_351,c_1101])).

tff(c_82,plain,(
    ! [A_3,B_5] :
      ( k2_funct_1(A_3) = B_5
      | k6_partfun1(k2_relat_1(A_3)) != k5_relat_1(B_5,A_3)
      | k2_relat_1(B_5) != k1_relat_1(A_3)
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(B_5)
      | ~ v1_relat_1(B_5)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8])).

tff(c_1098,plain,(
    ! [B_5] :
      ( k2_funct_1('#skF_4') = B_5
      | k5_relat_1(B_5,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_5) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_5)
      | ~ v1_relat_1(B_5)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1093,c_82])).

tff(c_1105,plain,(
    ! [B_5] :
      ( k2_funct_1('#skF_4') = B_5
      | k5_relat_1(B_5,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_5) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_5)
      | ~ v1_relat_1(B_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_74,c_1098])).

tff(c_1123,plain,(
    ! [B_5] :
      ( k2_funct_1('#skF_4') = B_5
      | k5_relat_1(B_5,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_5) != '#skF_2'
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_5)
      | ~ v1_relat_1(B_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1107,c_1105])).

tff(c_1124,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1123])).

tff(c_6,plain,(
    ! [A_2] : v2_funct_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_83,plain,(
    ! [A_2] : v2_funct_1(k6_partfun1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6])).

tff(c_1563,plain,(
    ! [D_228,A_230,B_227,C_229,E_226] :
      ( k1_xboole_0 = C_229
      | v2_funct_1(E_226)
      | k2_relset_1(A_230,B_227,D_228) != B_227
      | ~ v2_funct_1(k1_partfun1(A_230,B_227,B_227,C_229,D_228,E_226))
      | ~ m1_subset_1(E_226,k1_zfmisc_1(k2_zfmisc_1(B_227,C_229)))
      | ~ v1_funct_2(E_226,B_227,C_229)
      | ~ v1_funct_1(E_226)
      | ~ m1_subset_1(D_228,k1_zfmisc_1(k2_zfmisc_1(A_230,B_227)))
      | ~ v1_funct_2(D_228,A_230,B_227)
      | ~ v1_funct_1(D_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_1565,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_606,c_1563])).

tff(c_1567,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_74,c_72,c_70,c_83,c_68,c_1565])).

tff(c_1569,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1124,c_62,c_1567])).

tff(c_1571,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1123])).

tff(c_1572,plain,(
    ! [B_231] :
      ( k2_funct_1('#skF_4') = B_231
      | k5_relat_1(B_231,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_231) != '#skF_2'
      | ~ v1_funct_1(B_231)
      | ~ v1_relat_1(B_231) ) ),
    inference(splitRight,[status(thm)],[c_1123])).

tff(c_1575,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_1572])).

tff(c_1584,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_166,c_1575])).

tff(c_1589,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1584])).

tff(c_1630,plain,(
    ! [E_245,D_243,C_247,F_244,A_242,B_246] :
      ( k1_partfun1(A_242,B_246,C_247,D_243,E_245,F_244) = k5_relat_1(E_245,F_244)
      | ~ m1_subset_1(F_244,k1_zfmisc_1(k2_zfmisc_1(C_247,D_243)))
      | ~ v1_funct_1(F_244)
      | ~ m1_subset_1(E_245,k1_zfmisc_1(k2_zfmisc_1(A_242,B_246)))
      | ~ v1_funct_1(E_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1634,plain,(
    ! [A_242,B_246,E_245] :
      ( k1_partfun1(A_242,B_246,'#skF_2','#skF_1',E_245,'#skF_4') = k5_relat_1(E_245,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_245,k1_zfmisc_1(k2_zfmisc_1(A_242,B_246)))
      | ~ v1_funct_1(E_245) ) ),
    inference(resolution,[status(thm)],[c_70,c_1630])).

tff(c_1991,plain,(
    ! [A_277,B_278,E_279] :
      ( k1_partfun1(A_277,B_278,'#skF_2','#skF_1',E_279,'#skF_4') = k5_relat_1(E_279,'#skF_4')
      | ~ m1_subset_1(E_279,k1_zfmisc_1(k2_zfmisc_1(A_277,B_278)))
      | ~ v1_funct_1(E_279) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1634])).

tff(c_2009,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_1991])).

tff(c_2023,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_606,c_2009])).

tff(c_2025,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1589,c_2023])).

tff(c_2026,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1584])).

tff(c_10,plain,(
    ! [A_6] :
      ( k2_funct_1(k2_funct_1(A_6)) = A_6
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2032,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2026,c_10])).

tff(c_2036,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_74,c_1571,c_2032])).

tff(c_2038,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2036])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:43:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.58/1.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.58/1.92  
% 4.58/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.58/1.92  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.58/1.92  
% 4.58/1.92  %Foreground sorts:
% 4.58/1.92  
% 4.58/1.92  
% 4.58/1.92  %Background operators:
% 4.58/1.92  
% 4.58/1.92  
% 4.58/1.92  %Foreground operators:
% 4.58/1.92  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.58/1.92  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.58/1.92  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.58/1.92  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.58/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.58/1.92  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.58/1.92  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.58/1.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.58/1.92  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.58/1.92  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.58/1.92  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.58/1.92  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.58/1.92  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.58/1.92  tff('#skF_2', type, '#skF_2': $i).
% 4.58/1.92  tff('#skF_3', type, '#skF_3': $i).
% 4.58/1.92  tff('#skF_1', type, '#skF_1': $i).
% 4.58/1.92  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.58/1.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.58/1.92  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.58/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.58/1.92  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.58/1.92  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.58/1.92  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.58/1.92  tff('#skF_4', type, '#skF_4': $i).
% 4.58/1.92  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.58/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.58/1.92  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.58/1.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.58/1.92  
% 4.99/1.94  tff(f_197, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 4.99/1.94  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.99/1.94  tff(f_70, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.99/1.94  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 4.99/1.94  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.99/1.94  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.99/1.94  tff(f_29, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 4.99/1.94  tff(f_128, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.99/1.94  tff(f_50, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 4.99/1.94  tff(f_80, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 4.99/1.94  tff(f_78, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.99/1.94  tff(f_126, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.99/1.94  tff(f_116, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.99/1.94  tff(f_145, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 4.99/1.94  tff(f_33, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.99/1.94  tff(f_171, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 4.99/1.94  tff(f_58, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 4.99/1.94  tff(c_58, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.99/1.94  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.99/1.94  tff(c_101, plain, (![C_57, A_58, B_59]: (v1_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.99/1.94  tff(c_113, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_101])).
% 4.99/1.94  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.99/1.94  tff(c_62, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.99/1.94  tff(c_72, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.99/1.94  tff(c_200, plain, (![A_73, B_74, C_75, D_76]: (k8_relset_1(A_73, B_74, C_75, D_76)=k10_relat_1(C_75, D_76) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.99/1.94  tff(c_208, plain, (![D_76]: (k8_relset_1('#skF_2', '#skF_1', '#skF_4', D_76)=k10_relat_1('#skF_4', D_76))), inference(resolution, [status(thm)], [c_70, c_200])).
% 4.99/1.94  tff(c_252, plain, (![A_85, B_86, C_87]: (k8_relset_1(A_85, B_86, C_87, B_86)=k1_relset_1(A_85, B_86, C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.99/1.94  tff(c_256, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_1')=k1_relset_1('#skF_2', '#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_70, c_252])).
% 4.99/1.94  tff(c_262, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k10_relat_1('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_208, c_256])).
% 4.99/1.94  tff(c_336, plain, (![B_97, A_98, C_99]: (k1_xboole_0=B_97 | k1_relset_1(A_98, B_97, C_99)=A_98 | ~v1_funct_2(C_99, A_98, B_97) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_98, B_97))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.99/1.94  tff(c_342, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_70, c_336])).
% 4.99/1.94  tff(c_350, plain, (k1_xboole_0='#skF_1' | k10_relat_1('#skF_4', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_262, c_342])).
% 4.99/1.94  tff(c_351, plain, (k10_relat_1('#skF_4', '#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_62, c_350])).
% 4.99/1.94  tff(c_76, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.99/1.94  tff(c_114, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_101])).
% 4.99/1.94  tff(c_80, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.99/1.94  tff(c_64, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.99/1.94  tff(c_60, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.99/1.94  tff(c_78, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.99/1.94  tff(c_68, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.99/1.94  tff(c_153, plain, (![A_67, B_68, C_69]: (k2_relset_1(A_67, B_68, C_69)=k2_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.99/1.94  tff(c_162, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_153])).
% 4.99/1.94  tff(c_166, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_162])).
% 4.99/1.94  tff(c_2, plain, (![A_1]: (k10_relat_1(A_1, k2_relat_1(A_1))=k1_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.99/1.94  tff(c_170, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_166, c_2])).
% 4.99/1.94  tff(c_174, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_170])).
% 4.99/1.94  tff(c_209, plain, (![D_76]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_76)=k10_relat_1('#skF_3', D_76))), inference(resolution, [status(thm)], [c_76, c_200])).
% 4.99/1.94  tff(c_258, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_76, c_252])).
% 4.99/1.94  tff(c_264, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_174, c_209, c_258])).
% 4.99/1.94  tff(c_345, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_76, c_336])).
% 4.99/1.94  tff(c_354, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_264, c_345])).
% 4.99/1.94  tff(c_355, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_60, c_354])).
% 4.99/1.94  tff(c_46, plain, (![A_40]: (k6_relat_1(A_40)=k6_partfun1(A_40))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.99/1.94  tff(c_8, plain, (![A_3, B_5]: (k2_funct_1(A_3)=B_5 | k6_relat_1(k2_relat_1(A_3))!=k5_relat_1(B_5, A_3) | k2_relat_1(B_5)!=k1_relat_1(A_3) | ~v2_funct_1(A_3) | ~v1_funct_1(B_5) | ~v1_relat_1(B_5) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.99/1.94  tff(c_620, plain, (![A_139, B_140]: (k2_funct_1(A_139)=B_140 | k6_partfun1(k2_relat_1(A_139))!=k5_relat_1(B_140, A_139) | k2_relat_1(B_140)!=k1_relat_1(A_139) | ~v2_funct_1(A_139) | ~v1_funct_1(B_140) | ~v1_relat_1(B_140) | ~v1_funct_1(A_139) | ~v1_relat_1(A_139))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8])).
% 4.99/1.94  tff(c_622, plain, (![B_140]: (k2_funct_1('#skF_3')=B_140 | k5_relat_1(B_140, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_140)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_140) | ~v1_relat_1(B_140) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_166, c_620])).
% 4.99/1.94  tff(c_625, plain, (![B_141]: (k2_funct_1('#skF_3')=B_141 | k5_relat_1(B_141, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_141)!='#skF_1' | ~v1_funct_1(B_141) | ~v1_relat_1(B_141))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_80, c_64, c_355, c_622])).
% 4.99/1.94  tff(c_631, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_113, c_625])).
% 4.99/1.94  tff(c_640, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_631])).
% 4.99/1.94  tff(c_641, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_58, c_640])).
% 4.99/1.94  tff(c_643, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_641])).
% 4.99/1.94  tff(c_22, plain, (![A_21]: (m1_subset_1(k6_relat_1(A_21), k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.99/1.94  tff(c_81, plain, (![A_21]: (m1_subset_1(k6_partfun1(A_21), k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_22])).
% 4.99/1.94  tff(c_141, plain, (![A_62, B_63, D_64]: (r2_relset_1(A_62, B_63, D_64, D_64) | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.99/1.94  tff(c_148, plain, (![A_21]: (r2_relset_1(A_21, A_21, k6_partfun1(A_21), k6_partfun1(A_21)))), inference(resolution, [status(thm)], [c_81, c_141])).
% 4.99/1.94  tff(c_164, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_153])).
% 4.99/1.94  tff(c_483, plain, (![C_126, D_122, A_121, B_125, F_123, E_124]: (k1_partfun1(A_121, B_125, C_126, D_122, E_124, F_123)=k5_relat_1(E_124, F_123) | ~m1_subset_1(F_123, k1_zfmisc_1(k2_zfmisc_1(C_126, D_122))) | ~v1_funct_1(F_123) | ~m1_subset_1(E_124, k1_zfmisc_1(k2_zfmisc_1(A_121, B_125))) | ~v1_funct_1(E_124))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.99/1.94  tff(c_487, plain, (![A_121, B_125, E_124]: (k1_partfun1(A_121, B_125, '#skF_2', '#skF_1', E_124, '#skF_4')=k5_relat_1(E_124, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_124, k1_zfmisc_1(k2_zfmisc_1(A_121, B_125))) | ~v1_funct_1(E_124))), inference(resolution, [status(thm)], [c_70, c_483])).
% 4.99/1.94  tff(c_499, plain, (![A_129, B_130, E_131]: (k1_partfun1(A_129, B_130, '#skF_2', '#skF_1', E_131, '#skF_4')=k5_relat_1(E_131, '#skF_4') | ~m1_subset_1(E_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))) | ~v1_funct_1(E_131))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_487])).
% 4.99/1.94  tff(c_508, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_499])).
% 4.99/1.94  tff(c_515, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_508])).
% 4.99/1.94  tff(c_66, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.99/1.94  tff(c_367, plain, (![D_100, C_101, A_102, B_103]: (D_100=C_101 | ~r2_relset_1(A_102, B_103, C_101, D_100) | ~m1_subset_1(D_100, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.99/1.94  tff(c_375, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_66, c_367])).
% 4.99/1.94  tff(c_390, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_375])).
% 4.99/1.94  tff(c_403, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_390])).
% 4.99/1.94  tff(c_522, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_515, c_403])).
% 4.99/1.94  tff(c_533, plain, (![A_134, D_137, E_133, B_136, F_132, C_135]: (m1_subset_1(k1_partfun1(A_134, B_136, C_135, D_137, E_133, F_132), k1_zfmisc_1(k2_zfmisc_1(A_134, D_137))) | ~m1_subset_1(F_132, k1_zfmisc_1(k2_zfmisc_1(C_135, D_137))) | ~v1_funct_1(F_132) | ~m1_subset_1(E_133, k1_zfmisc_1(k2_zfmisc_1(A_134, B_136))) | ~v1_funct_1(E_133))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.99/1.94  tff(c_581, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_515, c_533])).
% 4.99/1.94  tff(c_602, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_581])).
% 4.99/1.94  tff(c_605, plain, $false, inference(negUnitSimplification, [status(thm)], [c_522, c_602])).
% 4.99/1.94  tff(c_606, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_390])).
% 4.99/1.94  tff(c_1084, plain, (![A_182, B_183, C_184, D_185]: (k2_relset_1(A_182, B_183, C_184)=B_183 | ~r2_relset_1(B_183, B_183, k1_partfun1(B_183, A_182, A_182, B_183, D_185, C_184), k6_partfun1(B_183)) | ~m1_subset_1(D_185, k1_zfmisc_1(k2_zfmisc_1(B_183, A_182))) | ~v1_funct_2(D_185, B_183, A_182) | ~v1_funct_1(D_185) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_182, B_183))) | ~v1_funct_2(C_184, A_182, B_183) | ~v1_funct_1(C_184))), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.99/1.94  tff(c_1087, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_606, c_1084])).
% 4.99/1.94  tff(c_1089, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_80, c_78, c_76, c_148, c_164, c_1087])).
% 4.99/1.94  tff(c_1091, plain, $false, inference(negUnitSimplification, [status(thm)], [c_643, c_1089])).
% 4.99/1.94  tff(c_1093, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_641])).
% 4.99/1.94  tff(c_1101, plain, (k10_relat_1('#skF_4', '#skF_1')=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1093, c_2])).
% 4.99/1.94  tff(c_1107, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_113, c_351, c_1101])).
% 4.99/1.94  tff(c_82, plain, (![A_3, B_5]: (k2_funct_1(A_3)=B_5 | k6_partfun1(k2_relat_1(A_3))!=k5_relat_1(B_5, A_3) | k2_relat_1(B_5)!=k1_relat_1(A_3) | ~v2_funct_1(A_3) | ~v1_funct_1(B_5) | ~v1_relat_1(B_5) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8])).
% 4.99/1.94  tff(c_1098, plain, (![B_5]: (k2_funct_1('#skF_4')=B_5 | k5_relat_1(B_5, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_5)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_5) | ~v1_relat_1(B_5) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1093, c_82])).
% 4.99/1.94  tff(c_1105, plain, (![B_5]: (k2_funct_1('#skF_4')=B_5 | k5_relat_1(B_5, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_5)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_5) | ~v1_relat_1(B_5))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_74, c_1098])).
% 4.99/1.94  tff(c_1123, plain, (![B_5]: (k2_funct_1('#skF_4')=B_5 | k5_relat_1(B_5, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_5)!='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_5) | ~v1_relat_1(B_5))), inference(demodulation, [status(thm), theory('equality')], [c_1107, c_1105])).
% 4.99/1.94  tff(c_1124, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1123])).
% 4.99/1.94  tff(c_6, plain, (![A_2]: (v2_funct_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.99/1.94  tff(c_83, plain, (![A_2]: (v2_funct_1(k6_partfun1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_6])).
% 4.99/1.94  tff(c_1563, plain, (![D_228, A_230, B_227, C_229, E_226]: (k1_xboole_0=C_229 | v2_funct_1(E_226) | k2_relset_1(A_230, B_227, D_228)!=B_227 | ~v2_funct_1(k1_partfun1(A_230, B_227, B_227, C_229, D_228, E_226)) | ~m1_subset_1(E_226, k1_zfmisc_1(k2_zfmisc_1(B_227, C_229))) | ~v1_funct_2(E_226, B_227, C_229) | ~v1_funct_1(E_226) | ~m1_subset_1(D_228, k1_zfmisc_1(k2_zfmisc_1(A_230, B_227))) | ~v1_funct_2(D_228, A_230, B_227) | ~v1_funct_1(D_228))), inference(cnfTransformation, [status(thm)], [f_171])).
% 4.99/1.94  tff(c_1565, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_606, c_1563])).
% 4.99/1.94  tff(c_1567, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_74, c_72, c_70, c_83, c_68, c_1565])).
% 4.99/1.94  tff(c_1569, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1124, c_62, c_1567])).
% 4.99/1.94  tff(c_1571, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_1123])).
% 4.99/1.94  tff(c_1572, plain, (![B_231]: (k2_funct_1('#skF_4')=B_231 | k5_relat_1(B_231, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_231)!='#skF_2' | ~v1_funct_1(B_231) | ~v1_relat_1(B_231))), inference(splitRight, [status(thm)], [c_1123])).
% 4.99/1.94  tff(c_1575, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_114, c_1572])).
% 4.99/1.94  tff(c_1584, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_166, c_1575])).
% 4.99/1.94  tff(c_1589, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_1584])).
% 4.99/1.94  tff(c_1630, plain, (![E_245, D_243, C_247, F_244, A_242, B_246]: (k1_partfun1(A_242, B_246, C_247, D_243, E_245, F_244)=k5_relat_1(E_245, F_244) | ~m1_subset_1(F_244, k1_zfmisc_1(k2_zfmisc_1(C_247, D_243))) | ~v1_funct_1(F_244) | ~m1_subset_1(E_245, k1_zfmisc_1(k2_zfmisc_1(A_242, B_246))) | ~v1_funct_1(E_245))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.99/1.94  tff(c_1634, plain, (![A_242, B_246, E_245]: (k1_partfun1(A_242, B_246, '#skF_2', '#skF_1', E_245, '#skF_4')=k5_relat_1(E_245, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_245, k1_zfmisc_1(k2_zfmisc_1(A_242, B_246))) | ~v1_funct_1(E_245))), inference(resolution, [status(thm)], [c_70, c_1630])).
% 4.99/1.94  tff(c_1991, plain, (![A_277, B_278, E_279]: (k1_partfun1(A_277, B_278, '#skF_2', '#skF_1', E_279, '#skF_4')=k5_relat_1(E_279, '#skF_4') | ~m1_subset_1(E_279, k1_zfmisc_1(k2_zfmisc_1(A_277, B_278))) | ~v1_funct_1(E_279))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1634])).
% 4.99/1.94  tff(c_2009, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_1991])).
% 4.99/1.94  tff(c_2023, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_606, c_2009])).
% 4.99/1.94  tff(c_2025, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1589, c_2023])).
% 4.99/1.94  tff(c_2026, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_1584])).
% 4.99/1.94  tff(c_10, plain, (![A_6]: (k2_funct_1(k2_funct_1(A_6))=A_6 | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.99/1.94  tff(c_2032, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2026, c_10])).
% 4.99/1.94  tff(c_2036, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_113, c_74, c_1571, c_2032])).
% 4.99/1.94  tff(c_2038, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_2036])).
% 4.99/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.99/1.94  
% 4.99/1.94  Inference rules
% 4.99/1.94  ----------------------
% 4.99/1.94  #Ref     : 0
% 4.99/1.94  #Sup     : 443
% 4.99/1.94  #Fact    : 0
% 4.99/1.94  #Define  : 0
% 4.99/1.94  #Split   : 19
% 4.99/1.94  #Chain   : 0
% 4.99/1.94  #Close   : 0
% 4.99/1.94  
% 4.99/1.94  Ordering : KBO
% 4.99/1.94  
% 4.99/1.94  Simplification rules
% 4.99/1.94  ----------------------
% 4.99/1.94  #Subsume      : 2
% 4.99/1.94  #Demod        : 285
% 4.99/1.94  #Tautology    : 139
% 4.99/1.94  #SimpNegUnit  : 34
% 4.99/1.94  #BackRed      : 21
% 4.99/1.94  
% 4.99/1.94  #Partial instantiations: 0
% 4.99/1.94  #Strategies tried      : 1
% 4.99/1.94  
% 4.99/1.94  Timing (in seconds)
% 4.99/1.94  ----------------------
% 4.99/1.95  Preprocessing        : 0.40
% 4.99/1.95  Parsing              : 0.21
% 4.99/1.95  CNF conversion       : 0.03
% 4.99/1.95  Main loop            : 0.70
% 4.99/1.95  Inferencing          : 0.24
% 4.99/1.95  Reduction            : 0.25
% 4.99/1.95  Demodulation         : 0.18
% 4.99/1.95  BG Simplification    : 0.04
% 4.99/1.95  Subsumption          : 0.12
% 4.99/1.95  Abstraction          : 0.04
% 4.99/1.95  MUC search           : 0.00
% 4.99/1.95  Cooper               : 0.00
% 4.99/1.95  Total                : 1.15
% 4.99/1.95  Index Insertion      : 0.00
% 4.99/1.95  Index Deletion       : 0.00
% 4.99/1.95  Index Matching       : 0.00
% 4.99/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
