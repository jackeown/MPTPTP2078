%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:18 EST 2020

% Result     : Theorem 4.42s
% Output     : CNFRefutation 4.86s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 801 expanded)
%              Number of leaves         :   42 ( 302 expanded)
%              Depth                    :   18
%              Number of atoms          :  340 (3374 expanded)
%              Number of equality atoms :  117 (1189 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_187,negated_conjecture,(
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_116,axiom,(
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

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_144,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_82,axiom,(
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

tff(f_132,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_128,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_161,axiom,(
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

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_142,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_55,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(c_54,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_100,plain,(
    ! [B_54,A_55] :
      ( v1_relat_1(B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_55))
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_109,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_66,c_100])).

tff(c_118,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_109])).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_106,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_72,c_100])).

tff(c_115,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_106])).

tff(c_76,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_60,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_74,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_162,plain,(
    ! [A_65,B_66,C_67] :
      ( k1_relset_1(A_65,B_66,C_67) = k1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_173,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_162])).

tff(c_256,plain,(
    ! [B_81,A_82,C_83] :
      ( k1_xboole_0 = B_81
      | k1_relset_1(A_82,B_81,C_83) = A_82
      | ~ v1_funct_2(C_83,A_82,B_81)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_82,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_262,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_256])).

tff(c_270,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_173,c_262])).

tff(c_271,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_270])).

tff(c_64,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_130,plain,(
    ! [A_60,B_61,C_62] :
      ( k2_relset_1(A_60,B_61,C_62) = k2_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_136,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_130])).

tff(c_142,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_136])).

tff(c_50,plain,(
    ! [A_40] : k6_relat_1(A_40) = k6_partfun1(A_40) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_18,plain,(
    ! [A_11,B_13] :
      ( k2_funct_1(A_11) = B_13
      | k6_relat_1(k2_relat_1(A_11)) != k5_relat_1(B_13,A_11)
      | k2_relat_1(B_13) != k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_347,plain,(
    ! [A_95,B_96] :
      ( k2_funct_1(A_95) = B_96
      | k6_partfun1(k2_relat_1(A_95)) != k5_relat_1(B_96,A_95)
      | k2_relat_1(B_96) != k1_relat_1(A_95)
      | ~ v2_funct_1(A_95)
      | ~ v1_funct_1(B_96)
      | ~ v1_relat_1(B_96)
      | ~ v1_funct_1(A_95)
      | ~ v1_relat_1(A_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_18])).

tff(c_353,plain,(
    ! [B_96] :
      ( k2_funct_1('#skF_3') = B_96
      | k5_relat_1(B_96,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_96) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_96)
      | ~ v1_relat_1(B_96)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_347])).

tff(c_358,plain,(
    ! [B_97] :
      ( k2_funct_1('#skF_3') = B_97
      | k5_relat_1(B_97,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_97) != '#skF_1'
      | ~ v1_funct_1(B_97)
      | ~ v1_relat_1(B_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_76,c_60,c_271,c_353])).

tff(c_361,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_118,c_358])).

tff(c_373,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_361])).

tff(c_374,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_373])).

tff(c_380,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_374])).

tff(c_68,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_46,plain,(
    ! [A_33] : m1_subset_1(k6_partfun1(A_33),k1_zfmisc_1(k2_zfmisc_1(A_33,A_33))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_119,plain,(
    ! [A_56,B_57,D_58] :
      ( r2_relset_1(A_56,B_57,D_58,D_58)
      | ~ m1_subset_1(D_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_126,plain,(
    ! [A_33] : r2_relset_1(A_33,A_33,k6_partfun1(A_33),k6_partfun1(A_33)) ),
    inference(resolution,[status(thm)],[c_46,c_119])).

tff(c_143,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_130])).

tff(c_494,plain,(
    ! [B_137,A_138,C_134,E_136,D_135,F_133] :
      ( m1_subset_1(k1_partfun1(A_138,B_137,C_134,D_135,E_136,F_133),k1_zfmisc_1(k2_zfmisc_1(A_138,D_135)))
      | ~ m1_subset_1(F_133,k1_zfmisc_1(k2_zfmisc_1(C_134,D_135)))
      | ~ v1_funct_1(F_133)
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1(A_138,B_137)))
      | ~ v1_funct_1(E_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_62,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_321,plain,(
    ! [D_89,C_90,A_91,B_92] :
      ( D_89 = C_90
      | ~ r2_relset_1(A_91,B_92,C_90,D_89)
      | ~ m1_subset_1(D_89,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_329,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_62,c_321])).

tff(c_344,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_329])).

tff(c_381,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_344])).

tff(c_512,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_494,c_381])).

tff(c_557,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_70,c_66,c_512])).

tff(c_558,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_344])).

tff(c_810,plain,(
    ! [A_171,B_172,C_173,D_174] :
      ( k2_relset_1(A_171,B_172,C_173) = B_172
      | ~ r2_relset_1(B_172,B_172,k1_partfun1(B_172,A_171,A_171,B_172,D_174,C_173),k6_partfun1(B_172))
      | ~ m1_subset_1(D_174,k1_zfmisc_1(k2_zfmisc_1(B_172,A_171)))
      | ~ v1_funct_2(D_174,B_172,A_171)
      | ~ v1_funct_1(D_174)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172)))
      | ~ v1_funct_2(C_173,A_171,B_172)
      | ~ v1_funct_1(C_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_816,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_810])).

tff(c_820,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_76,c_74,c_72,c_126,c_143,c_816])).

tff(c_822,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_380,c_820])).

tff(c_823,plain,(
    k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_374])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_174,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_162])).

tff(c_265,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_256])).

tff(c_274,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_174,c_265])).

tff(c_275,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_274])).

tff(c_824,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_374])).

tff(c_77,plain,(
    ! [A_11,B_13] :
      ( k2_funct_1(A_11) = B_13
      | k6_partfun1(k2_relat_1(A_11)) != k5_relat_1(B_13,A_11)
      | k2_relat_1(B_13) != k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_18])).

tff(c_828,plain,(
    ! [B_13] :
      ( k2_funct_1('#skF_4') = B_13
      | k5_relat_1(B_13,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_13) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_824,c_77])).

tff(c_832,plain,(
    ! [B_13] :
      ( k2_funct_1('#skF_4') = B_13
      | k5_relat_1(B_13,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_13) != '#skF_2'
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_70,c_275,c_828])).

tff(c_1053,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_832])).

tff(c_8,plain,(
    ! [A_6] : v2_funct_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_80,plain,(
    ! [A_6] : v2_funct_1(k6_partfun1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_8])).

tff(c_892,plain,(
    ! [B_194,F_192,A_190,C_195,E_193,D_191] :
      ( k1_partfun1(A_190,B_194,C_195,D_191,E_193,F_192) = k5_relat_1(E_193,F_192)
      | ~ m1_subset_1(F_192,k1_zfmisc_1(k2_zfmisc_1(C_195,D_191)))
      | ~ v1_funct_1(F_192)
      | ~ m1_subset_1(E_193,k1_zfmisc_1(k2_zfmisc_1(A_190,B_194)))
      | ~ v1_funct_1(E_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_898,plain,(
    ! [A_190,B_194,E_193] :
      ( k1_partfun1(A_190,B_194,'#skF_2','#skF_1',E_193,'#skF_4') = k5_relat_1(E_193,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_193,k1_zfmisc_1(k2_zfmisc_1(A_190,B_194)))
      | ~ v1_funct_1(E_193) ) ),
    inference(resolution,[status(thm)],[c_66,c_892])).

tff(c_934,plain,(
    ! [A_200,B_201,E_202] :
      ( k1_partfun1(A_200,B_201,'#skF_2','#skF_1',E_202,'#skF_4') = k5_relat_1(E_202,'#skF_4')
      | ~ m1_subset_1(E_202,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201)))
      | ~ v1_funct_1(E_202) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_898])).

tff(c_940,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_934])).

tff(c_947,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_940])).

tff(c_838,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_344])).

tff(c_952,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_947,c_838])).

tff(c_958,plain,(
    ! [D_205,F_203,E_206,C_204,A_208,B_207] :
      ( m1_subset_1(k1_partfun1(A_208,B_207,C_204,D_205,E_206,F_203),k1_zfmisc_1(k2_zfmisc_1(A_208,D_205)))
      | ~ m1_subset_1(F_203,k1_zfmisc_1(k2_zfmisc_1(C_204,D_205)))
      | ~ v1_funct_1(F_203)
      | ~ m1_subset_1(E_206,k1_zfmisc_1(k2_zfmisc_1(A_208,B_207)))
      | ~ v1_funct_1(E_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1006,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_947,c_958])).

tff(c_1031,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_70,c_66,c_1006])).

tff(c_1041,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_952,c_1031])).

tff(c_1042,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_344])).

tff(c_1108,plain,(
    ! [E_227,A_224,D_225,B_228,C_229,F_226] :
      ( k1_partfun1(A_224,B_228,C_229,D_225,E_227,F_226) = k5_relat_1(E_227,F_226)
      | ~ m1_subset_1(F_226,k1_zfmisc_1(k2_zfmisc_1(C_229,D_225)))
      | ~ v1_funct_1(F_226)
      | ~ m1_subset_1(E_227,k1_zfmisc_1(k2_zfmisc_1(A_224,B_228)))
      | ~ v1_funct_1(E_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_1114,plain,(
    ! [A_224,B_228,E_227] :
      ( k1_partfun1(A_224,B_228,'#skF_2','#skF_1',E_227,'#skF_4') = k5_relat_1(E_227,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_227,k1_zfmisc_1(k2_zfmisc_1(A_224,B_228)))
      | ~ v1_funct_1(E_227) ) ),
    inference(resolution,[status(thm)],[c_66,c_1108])).

tff(c_1465,plain,(
    ! [A_244,B_245,E_246] :
      ( k1_partfun1(A_244,B_245,'#skF_2','#skF_1',E_246,'#skF_4') = k5_relat_1(E_246,'#skF_4')
      | ~ m1_subset_1(E_246,k1_zfmisc_1(k2_zfmisc_1(A_244,B_245)))
      | ~ v1_funct_1(E_246) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1114])).

tff(c_1483,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_1465])).

tff(c_1500,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1042,c_1483])).

tff(c_10,plain,(
    ! [A_7,B_9] :
      ( v2_funct_1(A_7)
      | k2_relat_1(B_9) != k1_relat_1(A_7)
      | ~ v2_funct_1(k5_relat_1(B_9,A_7))
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1510,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1500,c_10])).

tff(c_1516,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_70,c_115,c_76,c_80,c_142,c_275,c_1510])).

tff(c_1518,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1053,c_1516])).

tff(c_1520,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_832])).

tff(c_1521,plain,(
    ! [B_247] :
      ( k2_funct_1('#skF_4') = B_247
      | k5_relat_1(B_247,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_247) != '#skF_2'
      | ~ v1_funct_1(B_247)
      | ~ v1_relat_1(B_247) ) ),
    inference(splitRight,[status(thm)],[c_832])).

tff(c_1527,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_115,c_1521])).

tff(c_1539,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_142,c_1527])).

tff(c_1542,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1539])).

tff(c_1560,plain,(
    ! [D_260,E_262,F_261,C_264,A_259,B_263] :
      ( k1_partfun1(A_259,B_263,C_264,D_260,E_262,F_261) = k5_relat_1(E_262,F_261)
      | ~ m1_subset_1(F_261,k1_zfmisc_1(k2_zfmisc_1(C_264,D_260)))
      | ~ v1_funct_1(F_261)
      | ~ m1_subset_1(E_262,k1_zfmisc_1(k2_zfmisc_1(A_259,B_263)))
      | ~ v1_funct_1(E_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_1566,plain,(
    ! [A_259,B_263,E_262] :
      ( k1_partfun1(A_259,B_263,'#skF_2','#skF_1',E_262,'#skF_4') = k5_relat_1(E_262,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_262,k1_zfmisc_1(k2_zfmisc_1(A_259,B_263)))
      | ~ v1_funct_1(E_262) ) ),
    inference(resolution,[status(thm)],[c_66,c_1560])).

tff(c_1887,plain,(
    ! [A_286,B_287,E_288] :
      ( k1_partfun1(A_286,B_287,'#skF_2','#skF_1',E_288,'#skF_4') = k5_relat_1(E_288,'#skF_4')
      | ~ m1_subset_1(E_288,k1_zfmisc_1(k2_zfmisc_1(A_286,B_287)))
      | ~ v1_funct_1(E_288) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1566])).

tff(c_1902,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_1887])).

tff(c_1916,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1042,c_1902])).

tff(c_1918,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1542,c_1916])).

tff(c_1919,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1539])).

tff(c_16,plain,(
    ! [A_10] :
      ( k5_relat_1(A_10,k2_funct_1(A_10)) = k6_relat_1(k1_relat_1(A_10))
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_78,plain,(
    ! [A_10] :
      ( k5_relat_1(A_10,k2_funct_1(A_10)) = k6_partfun1(k1_relat_1(A_10))
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_16])).

tff(c_1931,plain,
    ( k6_partfun1(k1_relat_1('#skF_4')) = k5_relat_1('#skF_4','#skF_3')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1919,c_78])).

tff(c_1942,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_70,c_1520,c_275,c_1931])).

tff(c_1944,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_823,c_1942])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:52:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.42/1.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.42/1.89  
% 4.42/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.42/1.89  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.42/1.89  
% 4.42/1.89  %Foreground sorts:
% 4.42/1.89  
% 4.42/1.89  
% 4.42/1.89  %Background operators:
% 4.42/1.89  
% 4.42/1.89  
% 4.42/1.89  %Foreground operators:
% 4.42/1.89  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.42/1.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.42/1.89  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.42/1.89  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.42/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.42/1.89  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.42/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.42/1.89  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.42/1.89  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.42/1.89  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.42/1.89  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.42/1.89  tff('#skF_2', type, '#skF_2': $i).
% 4.42/1.89  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.42/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.42/1.89  tff('#skF_1', type, '#skF_1': $i).
% 4.42/1.89  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.42/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.42/1.89  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.42/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.42/1.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.42/1.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.42/1.89  tff('#skF_4', type, '#skF_4': $i).
% 4.42/1.89  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.42/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.42/1.89  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.42/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.42/1.89  
% 4.86/1.91  tff(f_187, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 4.86/1.91  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.86/1.91  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.86/1.91  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.86/1.91  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.86/1.91  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.86/1.91  tff(f_144, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.86/1.91  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 4.86/1.91  tff(f_132, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.86/1.91  tff(f_98, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.86/1.91  tff(f_128, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.86/1.91  tff(f_161, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 4.86/1.91  tff(f_38, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.86/1.91  tff(f_142, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.86/1.91  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 4.86/1.91  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 4.86/1.91  tff(c_54, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.86/1.91  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.86/1.91  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.86/1.91  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.86/1.91  tff(c_100, plain, (![B_54, A_55]: (v1_relat_1(B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(A_55)) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.86/1.91  tff(c_109, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_66, c_100])).
% 4.86/1.91  tff(c_118, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_109])).
% 4.86/1.91  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.86/1.91  tff(c_106, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_72, c_100])).
% 4.86/1.91  tff(c_115, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_106])).
% 4.86/1.91  tff(c_76, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.86/1.91  tff(c_60, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.86/1.91  tff(c_56, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.86/1.91  tff(c_74, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.86/1.91  tff(c_162, plain, (![A_65, B_66, C_67]: (k1_relset_1(A_65, B_66, C_67)=k1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.86/1.91  tff(c_173, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_162])).
% 4.86/1.91  tff(c_256, plain, (![B_81, A_82, C_83]: (k1_xboole_0=B_81 | k1_relset_1(A_82, B_81, C_83)=A_82 | ~v1_funct_2(C_83, A_82, B_81) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_82, B_81))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.86/1.91  tff(c_262, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_256])).
% 4.86/1.91  tff(c_270, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_173, c_262])).
% 4.86/1.91  tff(c_271, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_56, c_270])).
% 4.86/1.91  tff(c_64, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.86/1.91  tff(c_130, plain, (![A_60, B_61, C_62]: (k2_relset_1(A_60, B_61, C_62)=k2_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.86/1.91  tff(c_136, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_130])).
% 4.86/1.91  tff(c_142, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_136])).
% 4.86/1.91  tff(c_50, plain, (![A_40]: (k6_relat_1(A_40)=k6_partfun1(A_40))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.86/1.91  tff(c_18, plain, (![A_11, B_13]: (k2_funct_1(A_11)=B_13 | k6_relat_1(k2_relat_1(A_11))!=k5_relat_1(B_13, A_11) | k2_relat_1(B_13)!=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.86/1.91  tff(c_347, plain, (![A_95, B_96]: (k2_funct_1(A_95)=B_96 | k6_partfun1(k2_relat_1(A_95))!=k5_relat_1(B_96, A_95) | k2_relat_1(B_96)!=k1_relat_1(A_95) | ~v2_funct_1(A_95) | ~v1_funct_1(B_96) | ~v1_relat_1(B_96) | ~v1_funct_1(A_95) | ~v1_relat_1(A_95))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_18])).
% 4.86/1.91  tff(c_353, plain, (![B_96]: (k2_funct_1('#skF_3')=B_96 | k5_relat_1(B_96, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_96)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_96) | ~v1_relat_1(B_96) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_142, c_347])).
% 4.86/1.91  tff(c_358, plain, (![B_97]: (k2_funct_1('#skF_3')=B_97 | k5_relat_1(B_97, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_97)!='#skF_1' | ~v1_funct_1(B_97) | ~v1_relat_1(B_97))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_76, c_60, c_271, c_353])).
% 4.86/1.91  tff(c_361, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_118, c_358])).
% 4.86/1.91  tff(c_373, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_361])).
% 4.86/1.91  tff(c_374, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_54, c_373])).
% 4.86/1.91  tff(c_380, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_374])).
% 4.86/1.91  tff(c_68, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.86/1.91  tff(c_46, plain, (![A_33]: (m1_subset_1(k6_partfun1(A_33), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.86/1.91  tff(c_119, plain, (![A_56, B_57, D_58]: (r2_relset_1(A_56, B_57, D_58, D_58) | ~m1_subset_1(D_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.86/1.91  tff(c_126, plain, (![A_33]: (r2_relset_1(A_33, A_33, k6_partfun1(A_33), k6_partfun1(A_33)))), inference(resolution, [status(thm)], [c_46, c_119])).
% 4.86/1.91  tff(c_143, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_130])).
% 4.86/1.91  tff(c_494, plain, (![B_137, A_138, C_134, E_136, D_135, F_133]: (m1_subset_1(k1_partfun1(A_138, B_137, C_134, D_135, E_136, F_133), k1_zfmisc_1(k2_zfmisc_1(A_138, D_135))) | ~m1_subset_1(F_133, k1_zfmisc_1(k2_zfmisc_1(C_134, D_135))) | ~v1_funct_1(F_133) | ~m1_subset_1(E_136, k1_zfmisc_1(k2_zfmisc_1(A_138, B_137))) | ~v1_funct_1(E_136))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.86/1.91  tff(c_62, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.86/1.91  tff(c_321, plain, (![D_89, C_90, A_91, B_92]: (D_89=C_90 | ~r2_relset_1(A_91, B_92, C_90, D_89) | ~m1_subset_1(D_89, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.86/1.91  tff(c_329, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_62, c_321])).
% 4.86/1.91  tff(c_344, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_329])).
% 4.86/1.91  tff(c_381, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_344])).
% 4.86/1.91  tff(c_512, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_494, c_381])).
% 4.86/1.91  tff(c_557, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_70, c_66, c_512])).
% 4.86/1.91  tff(c_558, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_344])).
% 4.86/1.91  tff(c_810, plain, (![A_171, B_172, C_173, D_174]: (k2_relset_1(A_171, B_172, C_173)=B_172 | ~r2_relset_1(B_172, B_172, k1_partfun1(B_172, A_171, A_171, B_172, D_174, C_173), k6_partfun1(B_172)) | ~m1_subset_1(D_174, k1_zfmisc_1(k2_zfmisc_1(B_172, A_171))) | ~v1_funct_2(D_174, B_172, A_171) | ~v1_funct_1(D_174) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))) | ~v1_funct_2(C_173, A_171, B_172) | ~v1_funct_1(C_173))), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.86/1.91  tff(c_816, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_558, c_810])).
% 4.86/1.91  tff(c_820, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_76, c_74, c_72, c_126, c_143, c_816])).
% 4.86/1.91  tff(c_822, plain, $false, inference(negUnitSimplification, [status(thm)], [c_380, c_820])).
% 4.86/1.91  tff(c_823, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_374])).
% 4.86/1.91  tff(c_58, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.86/1.91  tff(c_174, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_162])).
% 4.86/1.91  tff(c_265, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_256])).
% 4.86/1.91  tff(c_274, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_174, c_265])).
% 4.86/1.91  tff(c_275, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_58, c_274])).
% 4.86/1.91  tff(c_824, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_374])).
% 4.86/1.91  tff(c_77, plain, (![A_11, B_13]: (k2_funct_1(A_11)=B_13 | k6_partfun1(k2_relat_1(A_11))!=k5_relat_1(B_13, A_11) | k2_relat_1(B_13)!=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_18])).
% 4.86/1.91  tff(c_828, plain, (![B_13]: (k2_funct_1('#skF_4')=B_13 | k5_relat_1(B_13, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_13)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_13) | ~v1_relat_1(B_13) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_824, c_77])).
% 4.86/1.91  tff(c_832, plain, (![B_13]: (k2_funct_1('#skF_4')=B_13 | k5_relat_1(B_13, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_13)!='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_13) | ~v1_relat_1(B_13))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_70, c_275, c_828])).
% 4.86/1.91  tff(c_1053, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_832])).
% 4.86/1.91  tff(c_8, plain, (![A_6]: (v2_funct_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.86/1.91  tff(c_80, plain, (![A_6]: (v2_funct_1(k6_partfun1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_8])).
% 4.86/1.91  tff(c_892, plain, (![B_194, F_192, A_190, C_195, E_193, D_191]: (k1_partfun1(A_190, B_194, C_195, D_191, E_193, F_192)=k5_relat_1(E_193, F_192) | ~m1_subset_1(F_192, k1_zfmisc_1(k2_zfmisc_1(C_195, D_191))) | ~v1_funct_1(F_192) | ~m1_subset_1(E_193, k1_zfmisc_1(k2_zfmisc_1(A_190, B_194))) | ~v1_funct_1(E_193))), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.86/1.91  tff(c_898, plain, (![A_190, B_194, E_193]: (k1_partfun1(A_190, B_194, '#skF_2', '#skF_1', E_193, '#skF_4')=k5_relat_1(E_193, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_193, k1_zfmisc_1(k2_zfmisc_1(A_190, B_194))) | ~v1_funct_1(E_193))), inference(resolution, [status(thm)], [c_66, c_892])).
% 4.86/1.91  tff(c_934, plain, (![A_200, B_201, E_202]: (k1_partfun1(A_200, B_201, '#skF_2', '#skF_1', E_202, '#skF_4')=k5_relat_1(E_202, '#skF_4') | ~m1_subset_1(E_202, k1_zfmisc_1(k2_zfmisc_1(A_200, B_201))) | ~v1_funct_1(E_202))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_898])).
% 4.86/1.91  tff(c_940, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_934])).
% 4.86/1.91  tff(c_947, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_940])).
% 4.86/1.91  tff(c_838, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_344])).
% 4.86/1.91  tff(c_952, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_947, c_838])).
% 4.86/1.91  tff(c_958, plain, (![D_205, F_203, E_206, C_204, A_208, B_207]: (m1_subset_1(k1_partfun1(A_208, B_207, C_204, D_205, E_206, F_203), k1_zfmisc_1(k2_zfmisc_1(A_208, D_205))) | ~m1_subset_1(F_203, k1_zfmisc_1(k2_zfmisc_1(C_204, D_205))) | ~v1_funct_1(F_203) | ~m1_subset_1(E_206, k1_zfmisc_1(k2_zfmisc_1(A_208, B_207))) | ~v1_funct_1(E_206))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.86/1.91  tff(c_1006, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_947, c_958])).
% 4.86/1.91  tff(c_1031, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_70, c_66, c_1006])).
% 4.86/1.91  tff(c_1041, plain, $false, inference(negUnitSimplification, [status(thm)], [c_952, c_1031])).
% 4.86/1.91  tff(c_1042, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_344])).
% 4.86/1.91  tff(c_1108, plain, (![E_227, A_224, D_225, B_228, C_229, F_226]: (k1_partfun1(A_224, B_228, C_229, D_225, E_227, F_226)=k5_relat_1(E_227, F_226) | ~m1_subset_1(F_226, k1_zfmisc_1(k2_zfmisc_1(C_229, D_225))) | ~v1_funct_1(F_226) | ~m1_subset_1(E_227, k1_zfmisc_1(k2_zfmisc_1(A_224, B_228))) | ~v1_funct_1(E_227))), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.86/1.91  tff(c_1114, plain, (![A_224, B_228, E_227]: (k1_partfun1(A_224, B_228, '#skF_2', '#skF_1', E_227, '#skF_4')=k5_relat_1(E_227, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_227, k1_zfmisc_1(k2_zfmisc_1(A_224, B_228))) | ~v1_funct_1(E_227))), inference(resolution, [status(thm)], [c_66, c_1108])).
% 4.86/1.91  tff(c_1465, plain, (![A_244, B_245, E_246]: (k1_partfun1(A_244, B_245, '#skF_2', '#skF_1', E_246, '#skF_4')=k5_relat_1(E_246, '#skF_4') | ~m1_subset_1(E_246, k1_zfmisc_1(k2_zfmisc_1(A_244, B_245))) | ~v1_funct_1(E_246))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1114])).
% 4.86/1.91  tff(c_1483, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_1465])).
% 4.86/1.91  tff(c_1500, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1042, c_1483])).
% 4.86/1.91  tff(c_10, plain, (![A_7, B_9]: (v2_funct_1(A_7) | k2_relat_1(B_9)!=k1_relat_1(A_7) | ~v2_funct_1(k5_relat_1(B_9, A_7)) | ~v1_funct_1(B_9) | ~v1_relat_1(B_9) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.86/1.91  tff(c_1510, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1500, c_10])).
% 4.86/1.91  tff(c_1516, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_70, c_115, c_76, c_80, c_142, c_275, c_1510])).
% 4.86/1.91  tff(c_1518, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1053, c_1516])).
% 4.86/1.91  tff(c_1520, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_832])).
% 4.86/1.91  tff(c_1521, plain, (![B_247]: (k2_funct_1('#skF_4')=B_247 | k5_relat_1(B_247, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_247)!='#skF_2' | ~v1_funct_1(B_247) | ~v1_relat_1(B_247))), inference(splitRight, [status(thm)], [c_832])).
% 4.86/1.91  tff(c_1527, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_115, c_1521])).
% 4.86/1.91  tff(c_1539, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_142, c_1527])).
% 4.86/1.91  tff(c_1542, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_1539])).
% 4.86/1.91  tff(c_1560, plain, (![D_260, E_262, F_261, C_264, A_259, B_263]: (k1_partfun1(A_259, B_263, C_264, D_260, E_262, F_261)=k5_relat_1(E_262, F_261) | ~m1_subset_1(F_261, k1_zfmisc_1(k2_zfmisc_1(C_264, D_260))) | ~v1_funct_1(F_261) | ~m1_subset_1(E_262, k1_zfmisc_1(k2_zfmisc_1(A_259, B_263))) | ~v1_funct_1(E_262))), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.86/1.91  tff(c_1566, plain, (![A_259, B_263, E_262]: (k1_partfun1(A_259, B_263, '#skF_2', '#skF_1', E_262, '#skF_4')=k5_relat_1(E_262, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_262, k1_zfmisc_1(k2_zfmisc_1(A_259, B_263))) | ~v1_funct_1(E_262))), inference(resolution, [status(thm)], [c_66, c_1560])).
% 4.86/1.91  tff(c_1887, plain, (![A_286, B_287, E_288]: (k1_partfun1(A_286, B_287, '#skF_2', '#skF_1', E_288, '#skF_4')=k5_relat_1(E_288, '#skF_4') | ~m1_subset_1(E_288, k1_zfmisc_1(k2_zfmisc_1(A_286, B_287))) | ~v1_funct_1(E_288))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1566])).
% 4.86/1.91  tff(c_1902, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_1887])).
% 4.86/1.91  tff(c_1916, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1042, c_1902])).
% 4.86/1.91  tff(c_1918, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1542, c_1916])).
% 4.86/1.91  tff(c_1919, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_1539])).
% 4.86/1.91  tff(c_16, plain, (![A_10]: (k5_relat_1(A_10, k2_funct_1(A_10))=k6_relat_1(k1_relat_1(A_10)) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.86/1.91  tff(c_78, plain, (![A_10]: (k5_relat_1(A_10, k2_funct_1(A_10))=k6_partfun1(k1_relat_1(A_10)) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_16])).
% 4.86/1.91  tff(c_1931, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k5_relat_1('#skF_4', '#skF_3') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1919, c_78])).
% 4.86/1.91  tff(c_1942, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_70, c_1520, c_275, c_1931])).
% 4.86/1.91  tff(c_1944, plain, $false, inference(negUnitSimplification, [status(thm)], [c_823, c_1942])).
% 4.86/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.86/1.91  
% 4.86/1.91  Inference rules
% 4.86/1.91  ----------------------
% 4.86/1.91  #Ref     : 0
% 4.86/1.91  #Sup     : 393
% 4.86/1.91  #Fact    : 0
% 4.86/1.91  #Define  : 0
% 4.86/1.91  #Split   : 19
% 4.86/1.91  #Chain   : 0
% 4.86/1.91  #Close   : 0
% 4.86/1.91  
% 4.86/1.91  Ordering : KBO
% 4.86/1.91  
% 4.86/1.91  Simplification rules
% 4.86/1.91  ----------------------
% 4.86/1.91  #Subsume      : 2
% 4.86/1.91  #Demod        : 337
% 4.86/1.91  #Tautology    : 99
% 4.86/1.91  #SimpNegUnit  : 23
% 4.86/1.91  #BackRed      : 20
% 4.86/1.91  
% 4.86/1.91  #Partial instantiations: 0
% 4.86/1.91  #Strategies tried      : 1
% 4.86/1.91  
% 4.86/1.91  Timing (in seconds)
% 4.86/1.91  ----------------------
% 4.86/1.92  Preprocessing        : 0.39
% 4.86/1.92  Parsing              : 0.21
% 4.86/1.92  CNF conversion       : 0.03
% 4.86/1.92  Main loop            : 0.68
% 4.86/1.92  Inferencing          : 0.25
% 4.86/1.92  Reduction            : 0.23
% 4.86/1.92  Demodulation         : 0.16
% 4.86/1.92  BG Simplification    : 0.03
% 4.86/1.92  Subsumption          : 0.11
% 4.86/1.92  Abstraction          : 0.03
% 4.86/1.92  MUC search           : 0.00
% 4.86/1.92  Cooper               : 0.00
% 4.86/1.92  Total                : 1.13
% 4.86/1.92  Index Insertion      : 0.00
% 4.86/1.92  Index Deletion       : 0.00
% 4.86/1.92  Index Matching       : 0.00
% 4.86/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
