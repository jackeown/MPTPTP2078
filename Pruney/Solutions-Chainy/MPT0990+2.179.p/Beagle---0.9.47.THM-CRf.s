%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:22 EST 2020

% Result     : Theorem 7.46s
% Output     : CNFRefutation 7.70s
% Verified   : 
% Statistics : Number of formulae       :  176 (1526 expanded)
%              Number of leaves         :   46 ( 553 expanded)
%              Depth                    :   19
%              Number of atoms          :  404 (6039 expanded)
%              Number of equality atoms :  140 (1987 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_217,negated_conjecture,(
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

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_191,axiom,(
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

tff(f_120,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_104,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_116,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_149,axiom,(
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

tff(f_132,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_175,axiom,(
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

tff(f_96,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_130,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_66,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_6,plain,(
    ! [A_5,B_6] : v1_relat_1(k2_zfmisc_1(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_84,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_180,plain,(
    ! [B_71,A_72] :
      ( v1_relat_1(B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_72))
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_189,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_84,c_180])).

tff(c_198,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_189])).

tff(c_88,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_72,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_216,plain,(
    ! [A_74] :
      ( k4_relat_1(A_74) = k2_funct_1(A_74)
      | ~ v2_funct_1(A_74)
      | ~ v1_funct_1(A_74)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_222,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_216])).

tff(c_228,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_88,c_222])).

tff(c_4,plain,(
    ! [A_4] :
      ( v1_relat_1(k4_relat_1(A_4))
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_238,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_4])).

tff(c_246,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_238])).

tff(c_78,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_186,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_78,c_180])).

tff(c_195,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_186])).

tff(c_82,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_70,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_80,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_2312,plain,(
    ! [A_154,C_155,B_156] :
      ( k6_partfun1(A_154) = k5_relat_1(C_155,k2_funct_1(C_155))
      | k1_xboole_0 = B_156
      | ~ v2_funct_1(C_155)
      | k2_relset_1(A_154,B_156,C_155) != B_156
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_154,B_156)))
      | ~ v1_funct_2(C_155,A_154,B_156)
      | ~ v1_funct_1(C_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_2316,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_2312])).

tff(c_2324,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_2316])).

tff(c_2325,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2324])).

tff(c_2476,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2325])).

tff(c_86,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_46,plain,(
    ! [A_32] : m1_subset_1(k6_partfun1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_257,plain,(
    ! [A_75,B_76,D_77] :
      ( r2_relset_1(A_75,B_76,D_77,D_77)
      | ~ m1_subset_1(D_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_264,plain,(
    ! [A_32] : r2_relset_1(A_32,A_32,k6_partfun1(A_32),k6_partfun1(A_32)) ),
    inference(resolution,[status(thm)],[c_46,c_257])).

tff(c_1708,plain,(
    ! [C_132,B_129,A_130,E_133,F_131,D_128] :
      ( m1_subset_1(k1_partfun1(A_130,B_129,C_132,D_128,E_133,F_131),k1_zfmisc_1(k2_zfmisc_1(A_130,D_128)))
      | ~ m1_subset_1(F_131,k1_zfmisc_1(k2_zfmisc_1(C_132,D_128)))
      | ~ v1_funct_1(F_131)
      | ~ m1_subset_1(E_133,k1_zfmisc_1(k2_zfmisc_1(A_130,B_129)))
      | ~ v1_funct_1(E_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_74,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_537,plain,(
    ! [D_91,C_92,A_93,B_94] :
      ( D_91 = C_92
      | ~ r2_relset_1(A_93,B_94,C_92,D_91)
      | ~ m1_subset_1(D_91,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94)))
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_545,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_74,c_537])).

tff(c_560,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_545])).

tff(c_801,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_560])).

tff(c_1725,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1708,c_801])).

tff(c_1740,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_84,c_82,c_78,c_1725])).

tff(c_1741,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_560])).

tff(c_3041,plain,(
    ! [A_182,B_183,C_184,D_185] :
      ( k2_relset_1(A_182,B_183,C_184) = B_183
      | ~ r2_relset_1(B_183,B_183,k1_partfun1(B_183,A_182,A_182,B_183,D_185,C_184),k6_partfun1(B_183))
      | ~ m1_subset_1(D_185,k1_zfmisc_1(k2_zfmisc_1(B_183,A_182)))
      | ~ v1_funct_2(D_185,B_183,A_182)
      | ~ v1_funct_1(D_185)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_182,B_183)))
      | ~ v1_funct_2(C_184,A_182,B_183)
      | ~ v1_funct_1(C_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_3044,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1741,c_3041])).

tff(c_3046,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_88,c_86,c_84,c_264,c_3044])).

tff(c_3048,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2476,c_3046])).

tff(c_3049,plain,
    ( ~ v2_funct_1('#skF_4')
    | k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2325])).

tff(c_3075,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3049])).

tff(c_50,plain,(
    ! [A_39] : k6_relat_1(A_39) = k6_partfun1(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_30,plain,(
    ! [A_20] : v2_funct_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_91,plain,(
    ! [A_20] : v2_funct_1(k6_partfun1(A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_30])).

tff(c_76,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_3497,plain,(
    ! [A_207,D_209,C_210,B_206,E_208] :
      ( k1_xboole_0 = C_210
      | v2_funct_1(E_208)
      | k2_relset_1(A_207,B_206,D_209) != B_206
      | ~ v2_funct_1(k1_partfun1(A_207,B_206,B_206,C_210,D_209,E_208))
      | ~ m1_subset_1(E_208,k1_zfmisc_1(k2_zfmisc_1(B_206,C_210)))
      | ~ v1_funct_2(E_208,B_206,C_210)
      | ~ v1_funct_1(E_208)
      | ~ m1_subset_1(D_209,k1_zfmisc_1(k2_zfmisc_1(A_207,B_206)))
      | ~ v1_funct_2(D_209,A_207,B_206)
      | ~ v1_funct_1(D_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_3501,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_1741,c_3497])).

tff(c_3506,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_84,c_82,c_80,c_78,c_91,c_76,c_3501])).

tff(c_3508,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3075,c_70,c_3506])).

tff(c_3510,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_3049])).

tff(c_3050,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2325])).

tff(c_3622,plain,(
    ! [B_214,C_215,A_216] :
      ( k6_partfun1(B_214) = k5_relat_1(k2_funct_1(C_215),C_215)
      | k1_xboole_0 = B_214
      | ~ v2_funct_1(C_215)
      | k2_relset_1(A_216,B_214,C_215) != B_214
      | ~ m1_subset_1(C_215,k1_zfmisc_1(k2_zfmisc_1(A_216,B_214)))
      | ~ v1_funct_2(C_215,A_216,B_214)
      | ~ v1_funct_1(C_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_3626,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_3622])).

tff(c_3634,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_3050,c_3510,c_3626])).

tff(c_3635,plain,(
    k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_3634])).

tff(c_32,plain,(
    ! [A_21] :
      ( k5_relat_1(k2_funct_1(A_21),A_21) = k6_relat_1(k2_relat_1(A_21))
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_90,plain,(
    ! [A_21] :
      ( k5_relat_1(k2_funct_1(A_21),A_21) = k6_partfun1(k2_relat_1(A_21))
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_32])).

tff(c_3757,plain,
    ( k6_partfun1(k2_relat_1('#skF_4')) = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3635,c_90])).

tff(c_3768,plain,(
    k6_partfun1(k2_relat_1('#skF_4')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_82,c_3510,c_3757])).

tff(c_20,plain,(
    ! [A_17] :
      ( k5_relat_1(A_17,k6_relat_1(k2_relat_1(A_17))) = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_93,plain,(
    ! [A_17] :
      ( k5_relat_1(A_17,k6_partfun1(k2_relat_1(A_17))) = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_20])).

tff(c_3854,plain,
    ( k5_relat_1('#skF_4',k6_partfun1('#skF_1')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3768,c_93])).

tff(c_3898,plain,(
    k5_relat_1('#skF_4',k6_partfun1('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_3854])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_2318,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_2312])).

tff(c_2328,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_76,c_72,c_2318])).

tff(c_2329,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2328])).

tff(c_22,plain,(
    ! [A_18] :
      ( k4_relat_1(A_18) = k2_funct_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_3513,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3510,c_22])).

tff(c_3516,plain,(
    k4_relat_1('#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_82,c_3513])).

tff(c_3532,plain,
    ( v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3516,c_4])).

tff(c_3544,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_3532])).

tff(c_28,plain,(
    ! [A_20] : v1_relat_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_92,plain,(
    ! [A_20] : v1_relat_1(k6_partfun1(A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_28])).

tff(c_14,plain,(
    ! [A_15] : k1_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_96,plain,(
    ! [A_15] : k1_relat_1(k6_partfun1(A_15)) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_14])).

tff(c_18,plain,(
    ! [A_16] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_16)),A_16) = A_16
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_154,plain,(
    ! [A_69] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_69)),A_69) = A_69
      | ~ v1_relat_1(A_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_18])).

tff(c_166,plain,(
    ! [A_15] :
      ( k5_relat_1(k6_partfun1(A_15),k6_partfun1(A_15)) = k6_partfun1(A_15)
      | ~ v1_relat_1(k6_partfun1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_154])).

tff(c_170,plain,(
    ! [A_15] : k5_relat_1(k6_partfun1(A_15),k6_partfun1(A_15)) = k6_partfun1(A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_166])).

tff(c_10,plain,(
    ! [A_7] :
      ( k1_relat_1(k4_relat_1(A_7)) = k2_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_232,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_10])).

tff(c_242,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_232])).

tff(c_94,plain,(
    ! [A_16] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_16)),A_16) = A_16
      | ~ v1_relat_1(A_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_18])).

tff(c_304,plain,(
    ! [A_82,B_83,C_84] :
      ( k5_relat_1(k5_relat_1(A_82,B_83),C_84) = k5_relat_1(A_82,k5_relat_1(B_83,C_84))
      | ~ v1_relat_1(C_84)
      | ~ v1_relat_1(B_83)
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_353,plain,(
    ! [A_16,C_84] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_16)),k5_relat_1(A_16,C_84)) = k5_relat_1(A_16,C_84)
      | ~ v1_relat_1(C_84)
      | ~ v1_relat_1(A_16)
      | ~ v1_relat_1(k6_partfun1(k1_relat_1(A_16)))
      | ~ v1_relat_1(A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_304])).

tff(c_651,plain,(
    ! [A_97,C_98] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_97)),k5_relat_1(A_97,C_98)) = k5_relat_1(A_97,C_98)
      | ~ v1_relat_1(C_98)
      | ~ v1_relat_1(A_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_353])).

tff(c_708,plain,(
    ! [C_98] :
      ( k5_relat_1(k6_partfun1(k2_relat_1('#skF_3')),k5_relat_1(k2_funct_1('#skF_3'),C_98)) = k5_relat_1(k2_funct_1('#skF_3'),C_98)
      | ~ v1_relat_1(C_98)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_651])).

tff(c_1962,plain,(
    ! [C_141] :
      ( k5_relat_1(k6_partfun1(k2_relat_1('#skF_3')),k5_relat_1(k2_funct_1('#skF_3'),C_141)) = k5_relat_1(k2_funct_1('#skF_3'),C_141)
      | ~ v1_relat_1(C_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_708])).

tff(c_1998,plain,
    ( k5_relat_1(k6_partfun1(k2_relat_1('#skF_3')),k6_partfun1(k2_relat_1('#skF_3'))) = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_1962])).

tff(c_2022,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_88,c_72,c_198,c_170,c_1998])).

tff(c_3628,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_3622])).

tff(c_3638,plain,
    ( k6_partfun1(k2_relat_1('#skF_3')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_76,c_72,c_2022,c_3628])).

tff(c_3639,plain,(
    k6_partfun1(k2_relat_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3638])).

tff(c_3701,plain,
    ( k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3639,c_93])).

tff(c_3740,plain,(
    k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_3701])).

tff(c_3509,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3049])).

tff(c_2183,plain,(
    ! [B_150,D_149,C_147,A_145,F_148,E_146] :
      ( k1_partfun1(A_145,B_150,C_147,D_149,E_146,F_148) = k5_relat_1(E_146,F_148)
      | ~ m1_subset_1(F_148,k1_zfmisc_1(k2_zfmisc_1(C_147,D_149)))
      | ~ v1_funct_1(F_148)
      | ~ m1_subset_1(E_146,k1_zfmisc_1(k2_zfmisc_1(A_145,B_150)))
      | ~ v1_funct_1(E_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2187,plain,(
    ! [A_145,B_150,E_146] :
      ( k1_partfun1(A_145,B_150,'#skF_2','#skF_1',E_146,'#skF_4') = k5_relat_1(E_146,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_146,k1_zfmisc_1(k2_zfmisc_1(A_145,B_150)))
      | ~ v1_funct_1(E_146) ) ),
    inference(resolution,[status(thm)],[c_78,c_2183])).

tff(c_3546,plain,(
    ! [A_211,B_212,E_213] :
      ( k1_partfun1(A_211,B_212,'#skF_2','#skF_1',E_213,'#skF_4') = k5_relat_1(E_213,'#skF_4')
      | ~ m1_subset_1(E_213,k1_zfmisc_1(k2_zfmisc_1(A_211,B_212)))
      | ~ v1_funct_1(E_213) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2187])).

tff(c_3555,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_3546])).

tff(c_3562,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1741,c_3555])).

tff(c_12,plain,(
    ! [A_8,B_12,C_14] :
      ( k5_relat_1(k5_relat_1(A_8,B_12),C_14) = k5_relat_1(A_8,k5_relat_1(B_12,C_14))
      | ~ v1_relat_1(C_14)
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3570,plain,(
    ! [C_14] :
      ( k5_relat_1(k6_partfun1('#skF_1'),C_14) = k5_relat_1('#skF_3',k5_relat_1('#skF_4',C_14))
      | ~ v1_relat_1(C_14)
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3562,c_12])).

tff(c_4938,plain,(
    ! [C_264] :
      ( k5_relat_1(k6_partfun1('#skF_1'),C_264) = k5_relat_1('#skF_3',k5_relat_1('#skF_4',C_264))
      | ~ v1_relat_1(C_264) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_195,c_3570])).

tff(c_163,plain,(
    ! [A_7] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_7)),k4_relat_1(A_7)) = k4_relat_1(A_7)
      | ~ v1_relat_1(k4_relat_1(A_7))
      | ~ v1_relat_1(A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_154])).

tff(c_3842,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),k4_relat_1('#skF_4')) = k4_relat_1('#skF_4')
    | ~ v1_relat_1(k4_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3768,c_163])).

tff(c_3892,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_3544,c_3516,c_3516,c_3516,c_3842])).

tff(c_4958,plain,
    ( k5_relat_1('#skF_3',k5_relat_1('#skF_4',k2_funct_1('#skF_4'))) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4938,c_3892])).

tff(c_5045,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3544,c_3740,c_3509,c_4958])).

tff(c_16,plain,(
    ! [A_15] : k2_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_95,plain,(
    ! [A_15] : k2_relat_1(k6_partfun1(A_15)) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_16])).

tff(c_34,plain,(
    ! [A_21] :
      ( k5_relat_1(A_21,k2_funct_1(A_21)) = k6_relat_1(k1_relat_1(A_21))
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_89,plain,(
    ! [A_21] :
      ( k5_relat_1(A_21,k2_funct_1(A_21)) = k6_partfun1(k1_relat_1(A_21))
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_34])).

tff(c_4034,plain,
    ( k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3509,c_89])).

tff(c_4045,plain,(
    k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_82,c_3510,c_4034])).

tff(c_4100,plain,(
    k2_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4045,c_95])).

tff(c_4132,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_4100])).

tff(c_5663,plain,(
    ! [A_270,C_271] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_270)),C_271) = k5_relat_1(A_270,k5_relat_1(k2_funct_1(A_270),C_271))
      | ~ v1_relat_1(C_271)
      | ~ v1_relat_1(k2_funct_1(A_270))
      | ~ v1_relat_1(A_270)
      | ~ v2_funct_1(A_270)
      | ~ v1_funct_1(A_270)
      | ~ v1_relat_1(A_270) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_304])).

tff(c_5823,plain,(
    ! [C_271] :
      ( k5_relat_1('#skF_4',k5_relat_1(k2_funct_1('#skF_4'),C_271)) = k5_relat_1(k6_partfun1('#skF_2'),C_271)
      | ~ v1_relat_1(C_271)
      | ~ v1_relat_1(k2_funct_1('#skF_4'))
      | ~ v1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4132,c_5663])).

tff(c_6822,plain,(
    ! [C_287] :
      ( k5_relat_1(k6_partfun1('#skF_2'),C_287) = k5_relat_1('#skF_4',k5_relat_1('#skF_3',C_287))
      | ~ v1_relat_1(C_287) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_82,c_3510,c_195,c_198,c_5045,c_5045,c_5823])).

tff(c_251,plain,
    ( k5_relat_1(k6_partfun1(k2_relat_1('#skF_3')),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_94])).

tff(c_255,plain,(
    k5_relat_1(k6_partfun1(k2_relat_1('#skF_3')),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_251])).

tff(c_3664,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3639,c_255])).

tff(c_6859,plain,
    ( k5_relat_1('#skF_4',k5_relat_1('#skF_3',k2_funct_1('#skF_3'))) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6822,c_3664])).

tff(c_6956,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_3898,c_2329,c_6859])).

tff(c_6958,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_6956])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:35:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.46/2.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.46/2.58  
% 7.46/2.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.70/2.58  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.70/2.58  
% 7.70/2.58  %Foreground sorts:
% 7.70/2.58  
% 7.70/2.58  
% 7.70/2.58  %Background operators:
% 7.70/2.58  
% 7.70/2.58  
% 7.70/2.58  %Foreground operators:
% 7.70/2.58  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.70/2.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.70/2.58  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.70/2.58  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.70/2.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.70/2.58  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.70/2.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.70/2.58  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.70/2.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.70/2.58  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.70/2.58  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.70/2.58  tff('#skF_2', type, '#skF_2': $i).
% 7.70/2.58  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.70/2.58  tff('#skF_3', type, '#skF_3': $i).
% 7.70/2.58  tff('#skF_1', type, '#skF_1': $i).
% 7.70/2.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.70/2.58  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.70/2.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.70/2.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.70/2.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.70/2.58  tff('#skF_4', type, '#skF_4': $i).
% 7.70/2.58  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.70/2.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.70/2.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.70/2.58  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 7.70/2.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.70/2.58  
% 7.70/2.61  tff(f_217, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 7.70/2.61  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.70/2.61  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.70/2.61  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 7.70/2.61  tff(f_36, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 7.70/2.61  tff(f_191, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 7.70/2.61  tff(f_120, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.70/2.61  tff(f_104, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.70/2.61  tff(f_116, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.70/2.61  tff(f_149, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 7.70/2.61  tff(f_132, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.70/2.61  tff(f_86, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 7.70/2.61  tff(f_175, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 7.70/2.61  tff(f_96, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 7.70/2.61  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 7.70/2.61  tff(f_58, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 7.70/2.61  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 7.70/2.61  tff(f_44, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 7.70/2.61  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 7.70/2.61  tff(f_130, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.70/2.61  tff(c_66, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_217])).
% 7.70/2.61  tff(c_6, plain, (![A_5, B_6]: (v1_relat_1(k2_zfmisc_1(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.70/2.61  tff(c_84, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_217])).
% 7.70/2.61  tff(c_180, plain, (![B_71, A_72]: (v1_relat_1(B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(A_72)) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.70/2.61  tff(c_189, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_84, c_180])).
% 7.70/2.61  tff(c_198, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_189])).
% 7.70/2.61  tff(c_88, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_217])).
% 7.70/2.61  tff(c_72, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_217])).
% 7.70/2.61  tff(c_216, plain, (![A_74]: (k4_relat_1(A_74)=k2_funct_1(A_74) | ~v2_funct_1(A_74) | ~v1_funct_1(A_74) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.70/2.61  tff(c_222, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_216])).
% 7.70/2.61  tff(c_228, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_198, c_88, c_222])).
% 7.70/2.61  tff(c_4, plain, (![A_4]: (v1_relat_1(k4_relat_1(A_4)) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.70/2.61  tff(c_238, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_228, c_4])).
% 7.70/2.61  tff(c_246, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_198, c_238])).
% 7.70/2.61  tff(c_78, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_217])).
% 7.70/2.61  tff(c_186, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_78, c_180])).
% 7.70/2.61  tff(c_195, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_186])).
% 7.70/2.61  tff(c_82, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_217])).
% 7.70/2.61  tff(c_70, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_217])).
% 7.70/2.61  tff(c_80, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_217])).
% 7.70/2.61  tff(c_2312, plain, (![A_154, C_155, B_156]: (k6_partfun1(A_154)=k5_relat_1(C_155, k2_funct_1(C_155)) | k1_xboole_0=B_156 | ~v2_funct_1(C_155) | k2_relset_1(A_154, B_156, C_155)!=B_156 | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_154, B_156))) | ~v1_funct_2(C_155, A_154, B_156) | ~v1_funct_1(C_155))), inference(cnfTransformation, [status(thm)], [f_191])).
% 7.70/2.61  tff(c_2316, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_2312])).
% 7.70/2.61  tff(c_2324, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_2316])).
% 7.70/2.61  tff(c_2325, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_70, c_2324])).
% 7.70/2.61  tff(c_2476, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2325])).
% 7.70/2.61  tff(c_86, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_217])).
% 7.70/2.61  tff(c_46, plain, (![A_32]: (m1_subset_1(k6_partfun1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.70/2.61  tff(c_257, plain, (![A_75, B_76, D_77]: (r2_relset_1(A_75, B_76, D_77, D_77) | ~m1_subset_1(D_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.70/2.61  tff(c_264, plain, (![A_32]: (r2_relset_1(A_32, A_32, k6_partfun1(A_32), k6_partfun1(A_32)))), inference(resolution, [status(thm)], [c_46, c_257])).
% 7.70/2.61  tff(c_1708, plain, (![C_132, B_129, A_130, E_133, F_131, D_128]: (m1_subset_1(k1_partfun1(A_130, B_129, C_132, D_128, E_133, F_131), k1_zfmisc_1(k2_zfmisc_1(A_130, D_128))) | ~m1_subset_1(F_131, k1_zfmisc_1(k2_zfmisc_1(C_132, D_128))) | ~v1_funct_1(F_131) | ~m1_subset_1(E_133, k1_zfmisc_1(k2_zfmisc_1(A_130, B_129))) | ~v1_funct_1(E_133))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.70/2.61  tff(c_74, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_217])).
% 7.70/2.61  tff(c_537, plain, (![D_91, C_92, A_93, B_94]: (D_91=C_92 | ~r2_relset_1(A_93, B_94, C_92, D_91) | ~m1_subset_1(D_91, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.70/2.61  tff(c_545, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_74, c_537])).
% 7.70/2.61  tff(c_560, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_545])).
% 7.70/2.61  tff(c_801, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_560])).
% 7.70/2.61  tff(c_1725, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1708, c_801])).
% 7.70/2.61  tff(c_1740, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_84, c_82, c_78, c_1725])).
% 7.70/2.61  tff(c_1741, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_560])).
% 7.70/2.61  tff(c_3041, plain, (![A_182, B_183, C_184, D_185]: (k2_relset_1(A_182, B_183, C_184)=B_183 | ~r2_relset_1(B_183, B_183, k1_partfun1(B_183, A_182, A_182, B_183, D_185, C_184), k6_partfun1(B_183)) | ~m1_subset_1(D_185, k1_zfmisc_1(k2_zfmisc_1(B_183, A_182))) | ~v1_funct_2(D_185, B_183, A_182) | ~v1_funct_1(D_185) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_182, B_183))) | ~v1_funct_2(C_184, A_182, B_183) | ~v1_funct_1(C_184))), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.70/2.61  tff(c_3044, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1741, c_3041])).
% 7.70/2.61  tff(c_3046, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_88, c_86, c_84, c_264, c_3044])).
% 7.70/2.61  tff(c_3048, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2476, c_3046])).
% 7.70/2.61  tff(c_3049, plain, (~v2_funct_1('#skF_4') | k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_2325])).
% 7.70/2.61  tff(c_3075, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_3049])).
% 7.70/2.61  tff(c_50, plain, (![A_39]: (k6_relat_1(A_39)=k6_partfun1(A_39))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.70/2.61  tff(c_30, plain, (![A_20]: (v2_funct_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.70/2.61  tff(c_91, plain, (![A_20]: (v2_funct_1(k6_partfun1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_30])).
% 7.70/2.61  tff(c_76, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_217])).
% 7.70/2.61  tff(c_3497, plain, (![A_207, D_209, C_210, B_206, E_208]: (k1_xboole_0=C_210 | v2_funct_1(E_208) | k2_relset_1(A_207, B_206, D_209)!=B_206 | ~v2_funct_1(k1_partfun1(A_207, B_206, B_206, C_210, D_209, E_208)) | ~m1_subset_1(E_208, k1_zfmisc_1(k2_zfmisc_1(B_206, C_210))) | ~v1_funct_2(E_208, B_206, C_210) | ~v1_funct_1(E_208) | ~m1_subset_1(D_209, k1_zfmisc_1(k2_zfmisc_1(A_207, B_206))) | ~v1_funct_2(D_209, A_207, B_206) | ~v1_funct_1(D_209))), inference(cnfTransformation, [status(thm)], [f_175])).
% 7.70/2.61  tff(c_3501, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1741, c_3497])).
% 7.70/2.61  tff(c_3506, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_84, c_82, c_80, c_78, c_91, c_76, c_3501])).
% 7.70/2.61  tff(c_3508, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3075, c_70, c_3506])).
% 7.70/2.61  tff(c_3510, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_3049])).
% 7.70/2.61  tff(c_3050, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_2325])).
% 7.70/2.61  tff(c_3622, plain, (![B_214, C_215, A_216]: (k6_partfun1(B_214)=k5_relat_1(k2_funct_1(C_215), C_215) | k1_xboole_0=B_214 | ~v2_funct_1(C_215) | k2_relset_1(A_216, B_214, C_215)!=B_214 | ~m1_subset_1(C_215, k1_zfmisc_1(k2_zfmisc_1(A_216, B_214))) | ~v1_funct_2(C_215, A_216, B_214) | ~v1_funct_1(C_215))), inference(cnfTransformation, [status(thm)], [f_191])).
% 7.70/2.61  tff(c_3626, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_3622])).
% 7.70/2.61  tff(c_3634, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_3050, c_3510, c_3626])).
% 7.70/2.61  tff(c_3635, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_70, c_3634])).
% 7.70/2.61  tff(c_32, plain, (![A_21]: (k5_relat_1(k2_funct_1(A_21), A_21)=k6_relat_1(k2_relat_1(A_21)) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.70/2.61  tff(c_90, plain, (![A_21]: (k5_relat_1(k2_funct_1(A_21), A_21)=k6_partfun1(k2_relat_1(A_21)) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_32])).
% 7.70/2.61  tff(c_3757, plain, (k6_partfun1(k2_relat_1('#skF_4'))=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3635, c_90])).
% 7.70/2.61  tff(c_3768, plain, (k6_partfun1(k2_relat_1('#skF_4'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_195, c_82, c_3510, c_3757])).
% 7.70/2.61  tff(c_20, plain, (![A_17]: (k5_relat_1(A_17, k6_relat_1(k2_relat_1(A_17)))=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.70/2.61  tff(c_93, plain, (![A_17]: (k5_relat_1(A_17, k6_partfun1(k2_relat_1(A_17)))=A_17 | ~v1_relat_1(A_17))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_20])).
% 7.70/2.61  tff(c_3854, plain, (k5_relat_1('#skF_4', k6_partfun1('#skF_1'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3768, c_93])).
% 7.70/2.61  tff(c_3898, plain, (k5_relat_1('#skF_4', k6_partfun1('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_195, c_3854])).
% 7.70/2.61  tff(c_68, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_217])).
% 7.70/2.61  tff(c_2318, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_2312])).
% 7.70/2.61  tff(c_2328, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_76, c_72, c_2318])).
% 7.70/2.61  tff(c_2329, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_68, c_2328])).
% 7.70/2.61  tff(c_22, plain, (![A_18]: (k4_relat_1(A_18)=k2_funct_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.70/2.61  tff(c_3513, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_3510, c_22])).
% 7.70/2.61  tff(c_3516, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_195, c_82, c_3513])).
% 7.70/2.61  tff(c_3532, plain, (v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3516, c_4])).
% 7.70/2.61  tff(c_3544, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_195, c_3532])).
% 7.70/2.61  tff(c_28, plain, (![A_20]: (v1_relat_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.70/2.61  tff(c_92, plain, (![A_20]: (v1_relat_1(k6_partfun1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_28])).
% 7.70/2.61  tff(c_14, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.70/2.61  tff(c_96, plain, (![A_15]: (k1_relat_1(k6_partfun1(A_15))=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_14])).
% 7.70/2.61  tff(c_18, plain, (![A_16]: (k5_relat_1(k6_relat_1(k1_relat_1(A_16)), A_16)=A_16 | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.70/2.61  tff(c_154, plain, (![A_69]: (k5_relat_1(k6_partfun1(k1_relat_1(A_69)), A_69)=A_69 | ~v1_relat_1(A_69))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_18])).
% 7.70/2.61  tff(c_166, plain, (![A_15]: (k5_relat_1(k6_partfun1(A_15), k6_partfun1(A_15))=k6_partfun1(A_15) | ~v1_relat_1(k6_partfun1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_96, c_154])).
% 7.70/2.61  tff(c_170, plain, (![A_15]: (k5_relat_1(k6_partfun1(A_15), k6_partfun1(A_15))=k6_partfun1(A_15))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_166])).
% 7.70/2.61  tff(c_10, plain, (![A_7]: (k1_relat_1(k4_relat_1(A_7))=k2_relat_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.70/2.61  tff(c_232, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_228, c_10])).
% 7.70/2.61  tff(c_242, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_198, c_232])).
% 7.70/2.61  tff(c_94, plain, (![A_16]: (k5_relat_1(k6_partfun1(k1_relat_1(A_16)), A_16)=A_16 | ~v1_relat_1(A_16))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_18])).
% 7.70/2.61  tff(c_304, plain, (![A_82, B_83, C_84]: (k5_relat_1(k5_relat_1(A_82, B_83), C_84)=k5_relat_1(A_82, k5_relat_1(B_83, C_84)) | ~v1_relat_1(C_84) | ~v1_relat_1(B_83) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.70/2.61  tff(c_353, plain, (![A_16, C_84]: (k5_relat_1(k6_partfun1(k1_relat_1(A_16)), k5_relat_1(A_16, C_84))=k5_relat_1(A_16, C_84) | ~v1_relat_1(C_84) | ~v1_relat_1(A_16) | ~v1_relat_1(k6_partfun1(k1_relat_1(A_16))) | ~v1_relat_1(A_16))), inference(superposition, [status(thm), theory('equality')], [c_94, c_304])).
% 7.70/2.61  tff(c_651, plain, (![A_97, C_98]: (k5_relat_1(k6_partfun1(k1_relat_1(A_97)), k5_relat_1(A_97, C_98))=k5_relat_1(A_97, C_98) | ~v1_relat_1(C_98) | ~v1_relat_1(A_97))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_353])).
% 7.70/2.61  tff(c_708, plain, (![C_98]: (k5_relat_1(k6_partfun1(k2_relat_1('#skF_3')), k5_relat_1(k2_funct_1('#skF_3'), C_98))=k5_relat_1(k2_funct_1('#skF_3'), C_98) | ~v1_relat_1(C_98) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_242, c_651])).
% 7.70/2.61  tff(c_1962, plain, (![C_141]: (k5_relat_1(k6_partfun1(k2_relat_1('#skF_3')), k5_relat_1(k2_funct_1('#skF_3'), C_141))=k5_relat_1(k2_funct_1('#skF_3'), C_141) | ~v1_relat_1(C_141))), inference(demodulation, [status(thm), theory('equality')], [c_246, c_708])).
% 7.70/2.61  tff(c_1998, plain, (k5_relat_1(k6_partfun1(k2_relat_1('#skF_3')), k6_partfun1(k2_relat_1('#skF_3')))=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_90, c_1962])).
% 7.70/2.61  tff(c_2022, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_198, c_88, c_72, c_198, c_170, c_1998])).
% 7.70/2.61  tff(c_3628, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_3622])).
% 7.70/2.61  tff(c_3638, plain, (k6_partfun1(k2_relat_1('#skF_3'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_76, c_72, c_2022, c_3628])).
% 7.70/2.61  tff(c_3639, plain, (k6_partfun1(k2_relat_1('#skF_3'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_68, c_3638])).
% 7.70/2.61  tff(c_3701, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3639, c_93])).
% 7.70/2.61  tff(c_3740, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_198, c_3701])).
% 7.70/2.61  tff(c_3509, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_3049])).
% 7.70/2.61  tff(c_2183, plain, (![B_150, D_149, C_147, A_145, F_148, E_146]: (k1_partfun1(A_145, B_150, C_147, D_149, E_146, F_148)=k5_relat_1(E_146, F_148) | ~m1_subset_1(F_148, k1_zfmisc_1(k2_zfmisc_1(C_147, D_149))) | ~v1_funct_1(F_148) | ~m1_subset_1(E_146, k1_zfmisc_1(k2_zfmisc_1(A_145, B_150))) | ~v1_funct_1(E_146))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.70/2.61  tff(c_2187, plain, (![A_145, B_150, E_146]: (k1_partfun1(A_145, B_150, '#skF_2', '#skF_1', E_146, '#skF_4')=k5_relat_1(E_146, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_146, k1_zfmisc_1(k2_zfmisc_1(A_145, B_150))) | ~v1_funct_1(E_146))), inference(resolution, [status(thm)], [c_78, c_2183])).
% 7.70/2.61  tff(c_3546, plain, (![A_211, B_212, E_213]: (k1_partfun1(A_211, B_212, '#skF_2', '#skF_1', E_213, '#skF_4')=k5_relat_1(E_213, '#skF_4') | ~m1_subset_1(E_213, k1_zfmisc_1(k2_zfmisc_1(A_211, B_212))) | ~v1_funct_1(E_213))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_2187])).
% 7.70/2.61  tff(c_3555, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_3546])).
% 7.70/2.61  tff(c_3562, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1741, c_3555])).
% 7.70/2.61  tff(c_12, plain, (![A_8, B_12, C_14]: (k5_relat_1(k5_relat_1(A_8, B_12), C_14)=k5_relat_1(A_8, k5_relat_1(B_12, C_14)) | ~v1_relat_1(C_14) | ~v1_relat_1(B_12) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.70/2.61  tff(c_3570, plain, (![C_14]: (k5_relat_1(k6_partfun1('#skF_1'), C_14)=k5_relat_1('#skF_3', k5_relat_1('#skF_4', C_14)) | ~v1_relat_1(C_14) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3562, c_12])).
% 7.70/2.61  tff(c_4938, plain, (![C_264]: (k5_relat_1(k6_partfun1('#skF_1'), C_264)=k5_relat_1('#skF_3', k5_relat_1('#skF_4', C_264)) | ~v1_relat_1(C_264))), inference(demodulation, [status(thm), theory('equality')], [c_198, c_195, c_3570])).
% 7.70/2.61  tff(c_163, plain, (![A_7]: (k5_relat_1(k6_partfun1(k2_relat_1(A_7)), k4_relat_1(A_7))=k4_relat_1(A_7) | ~v1_relat_1(k4_relat_1(A_7)) | ~v1_relat_1(A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_154])).
% 7.70/2.61  tff(c_3842, plain, (k5_relat_1(k6_partfun1('#skF_1'), k4_relat_1('#skF_4'))=k4_relat_1('#skF_4') | ~v1_relat_1(k4_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3768, c_163])).
% 7.70/2.61  tff(c_3892, plain, (k5_relat_1(k6_partfun1('#skF_1'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_195, c_3544, c_3516, c_3516, c_3516, c_3842])).
% 7.70/2.61  tff(c_4958, plain, (k5_relat_1('#skF_3', k5_relat_1('#skF_4', k2_funct_1('#skF_4')))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4938, c_3892])).
% 7.70/2.61  tff(c_5045, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3544, c_3740, c_3509, c_4958])).
% 7.70/2.61  tff(c_16, plain, (![A_15]: (k2_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.70/2.61  tff(c_95, plain, (![A_15]: (k2_relat_1(k6_partfun1(A_15))=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_16])).
% 7.70/2.61  tff(c_34, plain, (![A_21]: (k5_relat_1(A_21, k2_funct_1(A_21))=k6_relat_1(k1_relat_1(A_21)) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.70/2.61  tff(c_89, plain, (![A_21]: (k5_relat_1(A_21, k2_funct_1(A_21))=k6_partfun1(k1_relat_1(A_21)) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_34])).
% 7.70/2.61  tff(c_4034, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3509, c_89])).
% 7.70/2.61  tff(c_4045, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_195, c_82, c_3510, c_4034])).
% 7.70/2.61  tff(c_4100, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4045, c_95])).
% 7.70/2.61  tff(c_4132, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_95, c_4100])).
% 7.70/2.61  tff(c_5663, plain, (![A_270, C_271]: (k5_relat_1(k6_partfun1(k1_relat_1(A_270)), C_271)=k5_relat_1(A_270, k5_relat_1(k2_funct_1(A_270), C_271)) | ~v1_relat_1(C_271) | ~v1_relat_1(k2_funct_1(A_270)) | ~v1_relat_1(A_270) | ~v2_funct_1(A_270) | ~v1_funct_1(A_270) | ~v1_relat_1(A_270))), inference(superposition, [status(thm), theory('equality')], [c_89, c_304])).
% 7.70/2.61  tff(c_5823, plain, (![C_271]: (k5_relat_1('#skF_4', k5_relat_1(k2_funct_1('#skF_4'), C_271))=k5_relat_1(k6_partfun1('#skF_2'), C_271) | ~v1_relat_1(C_271) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4132, c_5663])).
% 7.70/2.61  tff(c_6822, plain, (![C_287]: (k5_relat_1(k6_partfun1('#skF_2'), C_287)=k5_relat_1('#skF_4', k5_relat_1('#skF_3', C_287)) | ~v1_relat_1(C_287))), inference(demodulation, [status(thm), theory('equality')], [c_195, c_82, c_3510, c_195, c_198, c_5045, c_5045, c_5823])).
% 7.70/2.61  tff(c_251, plain, (k5_relat_1(k6_partfun1(k2_relat_1('#skF_3')), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_242, c_94])).
% 7.70/2.61  tff(c_255, plain, (k5_relat_1(k6_partfun1(k2_relat_1('#skF_3')), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_246, c_251])).
% 7.70/2.61  tff(c_3664, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3639, c_255])).
% 7.70/2.61  tff(c_6859, plain, (k5_relat_1('#skF_4', k5_relat_1('#skF_3', k2_funct_1('#skF_3')))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6822, c_3664])).
% 7.70/2.61  tff(c_6956, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_246, c_3898, c_2329, c_6859])).
% 7.70/2.61  tff(c_6958, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_6956])).
% 7.70/2.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.70/2.61  
% 7.70/2.61  Inference rules
% 7.70/2.61  ----------------------
% 7.70/2.61  #Ref     : 0
% 7.70/2.61  #Sup     : 1500
% 7.70/2.61  #Fact    : 0
% 7.70/2.61  #Define  : 0
% 7.70/2.61  #Split   : 9
% 7.70/2.61  #Chain   : 0
% 7.70/2.61  #Close   : 0
% 7.70/2.61  
% 7.70/2.61  Ordering : KBO
% 7.70/2.61  
% 7.70/2.61  Simplification rules
% 7.70/2.61  ----------------------
% 7.70/2.61  #Subsume      : 72
% 7.70/2.61  #Demod        : 2955
% 7.70/2.61  #Tautology    : 766
% 7.70/2.61  #SimpNegUnit  : 33
% 7.70/2.61  #BackRed      : 71
% 7.70/2.61  
% 7.70/2.61  #Partial instantiations: 0
% 7.70/2.61  #Strategies tried      : 1
% 7.70/2.61  
% 7.70/2.61  Timing (in seconds)
% 7.70/2.61  ----------------------
% 7.70/2.61  Preprocessing        : 0.40
% 7.70/2.61  Parsing              : 0.21
% 7.70/2.61  CNF conversion       : 0.03
% 7.70/2.61  Main loop            : 1.36
% 7.70/2.61  Inferencing          : 0.43
% 7.70/2.61  Reduction            : 0.58
% 7.70/2.61  Demodulation         : 0.46
% 7.70/2.61  BG Simplification    : 0.06
% 7.70/2.61  Subsumption          : 0.22
% 7.70/2.61  Abstraction          : 0.08
% 7.70/2.61  MUC search           : 0.00
% 7.70/2.62  Cooper               : 0.00
% 7.70/2.62  Total                : 1.82
% 7.70/2.62  Index Insertion      : 0.00
% 7.70/2.62  Index Deletion       : 0.00
% 7.70/2.62  Index Matching       : 0.00
% 7.70/2.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
