%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:59 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 262 expanded)
%              Number of leaves         :   38 ( 110 expanded)
%              Depth                    :   13
%              Number of atoms          :  186 ( 958 expanded)
%              Number of equality atoms :   54 ( 258 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_144,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,B,C)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ( ( k2_relset_1(A,C,k1_partfun1(A,B,B,C,D,E)) = C
                & v2_funct_1(E) )
             => ( C = k1_xboole_0
                | k2_relset_1(A,B,D) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_122,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_112,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A)
              & v2_funct_1(A) )
           => r1_tarski(k1_relat_1(A),k2_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_funct_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_133,plain,(
    ! [A_61,B_62,C_63] :
      ( k2_relset_1(A_61,B_62,C_63) = k2_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_140,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_133])).

tff(c_46,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_142,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_46])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_68,plain,(
    ! [B_44,A_45] :
      ( v1_relat_1(B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_45))
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_71,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_68])).

tff(c_77,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_71])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_97,plain,(
    ! [C_51,B_52,A_53] :
      ( v5_relat_1(C_51,B_52)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_53,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_104,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_97])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_347,plain,(
    ! [B_115,F_113,A_111,D_112,C_116,E_114] :
      ( k1_partfun1(A_111,B_115,C_116,D_112,E_114,F_113) = k5_relat_1(E_114,F_113)
      | ~ m1_subset_1(F_113,k1_zfmisc_1(k2_zfmisc_1(C_116,D_112)))
      | ~ v1_funct_1(F_113)
      | ~ m1_subset_1(E_114,k1_zfmisc_1(k2_zfmisc_1(A_111,B_115)))
      | ~ v1_funct_1(E_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_351,plain,(
    ! [A_111,B_115,E_114] :
      ( k1_partfun1(A_111,B_115,'#skF_2','#skF_3',E_114,'#skF_5') = k5_relat_1(E_114,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_114,k1_zfmisc_1(k2_zfmisc_1(A_111,B_115)))
      | ~ v1_funct_1(E_114) ) ),
    inference(resolution,[status(thm)],[c_54,c_347])).

tff(c_381,plain,(
    ! [A_120,B_121,E_122] :
      ( k1_partfun1(A_120,B_121,'#skF_2','#skF_3',E_122,'#skF_5') = k5_relat_1(E_122,'#skF_5')
      | ~ m1_subset_1(E_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121)))
      | ~ v1_funct_1(E_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_351])).

tff(c_384,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_381])).

tff(c_390,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_384])).

tff(c_52,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_395,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_52])).

tff(c_404,plain,(
    ! [C_126,F_123,E_124,B_127,A_125,D_128] :
      ( m1_subset_1(k1_partfun1(A_125,B_127,C_126,D_128,E_124,F_123),k1_zfmisc_1(k2_zfmisc_1(A_125,D_128)))
      | ~ m1_subset_1(F_123,k1_zfmisc_1(k2_zfmisc_1(C_126,D_128)))
      | ~ v1_funct_1(F_123)
      | ~ m1_subset_1(E_124,k1_zfmisc_1(k2_zfmisc_1(A_125,B_127)))
      | ~ v1_funct_1(E_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_456,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_404])).

tff(c_482,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_58,c_54,c_456])).

tff(c_26,plain,(
    ! [A_22,B_23,C_24] :
      ( k2_relset_1(A_22,B_23,C_24) = k2_relat_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_514,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_482,c_26])).

tff(c_550,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_514])).

tff(c_74,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_68])).

tff(c_80,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_74])).

tff(c_50,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_56,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_152,plain,(
    ! [A_65,B_66,C_67] :
      ( k1_relset_1(A_65,B_66,C_67) = k1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_160,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_152])).

tff(c_210,plain,(
    ! [B_85,A_86,C_87] :
      ( k1_xboole_0 = B_85
      | k1_relset_1(A_86,B_85,C_87) = A_86
      | ~ v1_funct_2(C_87,A_86,B_85)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_86,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_216,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_210])).

tff(c_222,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_160,c_216])).

tff(c_223,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_222])).

tff(c_230,plain,(
    ! [A_88,B_89] :
      ( r1_tarski(k1_relat_1(A_88),k2_relat_1(B_89))
      | ~ v2_funct_1(A_88)
      | k2_relat_1(k5_relat_1(B_89,A_88)) != k2_relat_1(A_88)
      | ~ v1_funct_1(B_89)
      | ~ v1_relat_1(B_89)
      | ~ v1_funct_1(A_88)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_238,plain,(
    ! [B_89] :
      ( r1_tarski('#skF_2',k2_relat_1(B_89))
      | ~ v2_funct_1('#skF_5')
      | k2_relat_1(k5_relat_1(B_89,'#skF_5')) != k2_relat_1('#skF_5')
      | ~ v1_funct_1(B_89)
      | ~ v1_relat_1(B_89)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_230])).

tff(c_261,plain,(
    ! [B_90] :
      ( r1_tarski('#skF_2',k2_relat_1(B_90))
      | k2_relat_1(k5_relat_1(B_90,'#skF_5')) != k2_relat_1('#skF_5')
      | ~ v1_funct_1(B_90)
      | ~ v1_relat_1(B_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_58,c_50,c_238])).

tff(c_110,plain,(
    ! [B_54,A_55] :
      ( r1_tarski(k2_relat_1(B_54),A_55)
      | ~ v5_relat_1(B_54,A_55)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_113,plain,(
    ! [B_54,A_55] :
      ( k2_relat_1(B_54) = A_55
      | ~ r1_tarski(A_55,k2_relat_1(B_54))
      | ~ v5_relat_1(B_54,A_55)
      | ~ v1_relat_1(B_54) ) ),
    inference(resolution,[status(thm)],[c_110,c_2])).

tff(c_267,plain,(
    ! [B_90] :
      ( k2_relat_1(B_90) = '#skF_2'
      | ~ v5_relat_1(B_90,'#skF_2')
      | k2_relat_1(k5_relat_1(B_90,'#skF_5')) != k2_relat_1('#skF_5')
      | ~ v1_funct_1(B_90)
      | ~ v1_relat_1(B_90) ) ),
    inference(resolution,[status(thm)],[c_261,c_113])).

tff(c_571,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ v5_relat_1('#skF_4','#skF_2')
    | k2_relat_1('#skF_5') != '#skF_3'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_550,c_267])).

tff(c_615,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | k2_relat_1('#skF_5') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_64,c_104,c_571])).

tff(c_616,plain,(
    k2_relat_1('#skF_5') != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_615])).

tff(c_105,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_97])).

tff(c_16,plain,(
    ! [A_10,B_12] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_10,B_12)),k2_relat_1(B_12))
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_169,plain,(
    ! [B_68,A_69] :
      ( k2_relat_1(B_68) = A_69
      | ~ r1_tarski(A_69,k2_relat_1(B_68))
      | ~ v5_relat_1(B_68,A_69)
      | ~ v1_relat_1(B_68) ) ),
    inference(resolution,[status(thm)],[c_110,c_2])).

tff(c_181,plain,(
    ! [A_10,B_12] :
      ( k2_relat_1(k5_relat_1(A_10,B_12)) = k2_relat_1(B_12)
      | ~ v5_relat_1(B_12,k2_relat_1(k5_relat_1(A_10,B_12)))
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_10) ) ),
    inference(resolution,[status(thm)],[c_16,c_169])).

tff(c_580,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = k2_relat_1('#skF_5')
    | ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_550,c_181])).

tff(c_622,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_80,c_105,c_550,c_580])).

tff(c_641,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_616,c_622])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:43:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.41  
% 2.94/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.42  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.94/1.42  
% 2.94/1.42  %Foreground sorts:
% 2.94/1.42  
% 2.94/1.42  
% 2.94/1.42  %Background operators:
% 2.94/1.42  
% 2.94/1.42  
% 2.94/1.42  %Foreground operators:
% 2.94/1.42  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.94/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.94/1.42  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.94/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.94/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.94/1.42  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.94/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.94/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.94/1.42  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.94/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.94/1.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.94/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.94/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.94/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.94/1.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.94/1.42  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.94/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.94/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.94/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.94/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.94/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.94/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.94/1.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.94/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.94/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.94/1.42  
% 2.94/1.43  tff(f_144, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_funct_2)).
% 2.94/1.43  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.94/1.43  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.94/1.43  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.94/1.43  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.94/1.43  tff(f_122, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 2.94/1.43  tff(f_112, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 2.94/1.43  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.94/1.43  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.94/1.43  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A)) & v2_funct_1(A)) => r1_tarski(k1_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_funct_1)).
% 2.94/1.43  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.94/1.43  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.94/1.43  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 2.94/1.43  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.94/1.43  tff(c_133, plain, (![A_61, B_62, C_63]: (k2_relset_1(A_61, B_62, C_63)=k2_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.94/1.43  tff(c_140, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_133])).
% 2.94/1.43  tff(c_46, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.94/1.43  tff(c_142, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_140, c_46])).
% 2.94/1.43  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.94/1.43  tff(c_68, plain, (![B_44, A_45]: (v1_relat_1(B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(A_45)) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.94/1.43  tff(c_71, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_68])).
% 2.94/1.43  tff(c_77, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_71])).
% 2.94/1.43  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.94/1.43  tff(c_97, plain, (![C_51, B_52, A_53]: (v5_relat_1(C_51, B_52) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_53, B_52))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.94/1.43  tff(c_104, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_97])).
% 2.94/1.43  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.94/1.43  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.94/1.43  tff(c_347, plain, (![B_115, F_113, A_111, D_112, C_116, E_114]: (k1_partfun1(A_111, B_115, C_116, D_112, E_114, F_113)=k5_relat_1(E_114, F_113) | ~m1_subset_1(F_113, k1_zfmisc_1(k2_zfmisc_1(C_116, D_112))) | ~v1_funct_1(F_113) | ~m1_subset_1(E_114, k1_zfmisc_1(k2_zfmisc_1(A_111, B_115))) | ~v1_funct_1(E_114))), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.94/1.43  tff(c_351, plain, (![A_111, B_115, E_114]: (k1_partfun1(A_111, B_115, '#skF_2', '#skF_3', E_114, '#skF_5')=k5_relat_1(E_114, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_114, k1_zfmisc_1(k2_zfmisc_1(A_111, B_115))) | ~v1_funct_1(E_114))), inference(resolution, [status(thm)], [c_54, c_347])).
% 2.94/1.43  tff(c_381, plain, (![A_120, B_121, E_122]: (k1_partfun1(A_120, B_121, '#skF_2', '#skF_3', E_122, '#skF_5')=k5_relat_1(E_122, '#skF_5') | ~m1_subset_1(E_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))) | ~v1_funct_1(E_122))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_351])).
% 2.94/1.43  tff(c_384, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_381])).
% 2.94/1.43  tff(c_390, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_384])).
% 2.94/1.43  tff(c_52, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.94/1.43  tff(c_395, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_390, c_52])).
% 2.94/1.43  tff(c_404, plain, (![C_126, F_123, E_124, B_127, A_125, D_128]: (m1_subset_1(k1_partfun1(A_125, B_127, C_126, D_128, E_124, F_123), k1_zfmisc_1(k2_zfmisc_1(A_125, D_128))) | ~m1_subset_1(F_123, k1_zfmisc_1(k2_zfmisc_1(C_126, D_128))) | ~v1_funct_1(F_123) | ~m1_subset_1(E_124, k1_zfmisc_1(k2_zfmisc_1(A_125, B_127))) | ~v1_funct_1(E_124))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.94/1.43  tff(c_456, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_390, c_404])).
% 2.94/1.43  tff(c_482, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_58, c_54, c_456])).
% 2.94/1.43  tff(c_26, plain, (![A_22, B_23, C_24]: (k2_relset_1(A_22, B_23, C_24)=k2_relat_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.94/1.43  tff(c_514, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_482, c_26])).
% 2.94/1.43  tff(c_550, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_395, c_514])).
% 2.94/1.43  tff(c_74, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_54, c_68])).
% 2.94/1.43  tff(c_80, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_74])).
% 2.94/1.43  tff(c_50, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.94/1.43  tff(c_48, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.94/1.43  tff(c_56, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.94/1.43  tff(c_152, plain, (![A_65, B_66, C_67]: (k1_relset_1(A_65, B_66, C_67)=k1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.94/1.43  tff(c_160, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_152])).
% 2.94/1.43  tff(c_210, plain, (![B_85, A_86, C_87]: (k1_xboole_0=B_85 | k1_relset_1(A_86, B_85, C_87)=A_86 | ~v1_funct_2(C_87, A_86, B_85) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_86, B_85))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.94/1.43  tff(c_216, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_210])).
% 2.94/1.43  tff(c_222, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_160, c_216])).
% 2.94/1.43  tff(c_223, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_48, c_222])).
% 2.94/1.43  tff(c_230, plain, (![A_88, B_89]: (r1_tarski(k1_relat_1(A_88), k2_relat_1(B_89)) | ~v2_funct_1(A_88) | k2_relat_1(k5_relat_1(B_89, A_88))!=k2_relat_1(A_88) | ~v1_funct_1(B_89) | ~v1_relat_1(B_89) | ~v1_funct_1(A_88) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.94/1.43  tff(c_238, plain, (![B_89]: (r1_tarski('#skF_2', k2_relat_1(B_89)) | ~v2_funct_1('#skF_5') | k2_relat_1(k5_relat_1(B_89, '#skF_5'))!=k2_relat_1('#skF_5') | ~v1_funct_1(B_89) | ~v1_relat_1(B_89) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_223, c_230])).
% 2.94/1.43  tff(c_261, plain, (![B_90]: (r1_tarski('#skF_2', k2_relat_1(B_90)) | k2_relat_1(k5_relat_1(B_90, '#skF_5'))!=k2_relat_1('#skF_5') | ~v1_funct_1(B_90) | ~v1_relat_1(B_90))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_58, c_50, c_238])).
% 2.94/1.43  tff(c_110, plain, (![B_54, A_55]: (r1_tarski(k2_relat_1(B_54), A_55) | ~v5_relat_1(B_54, A_55) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.94/1.43  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.94/1.43  tff(c_113, plain, (![B_54, A_55]: (k2_relat_1(B_54)=A_55 | ~r1_tarski(A_55, k2_relat_1(B_54)) | ~v5_relat_1(B_54, A_55) | ~v1_relat_1(B_54))), inference(resolution, [status(thm)], [c_110, c_2])).
% 2.94/1.43  tff(c_267, plain, (![B_90]: (k2_relat_1(B_90)='#skF_2' | ~v5_relat_1(B_90, '#skF_2') | k2_relat_1(k5_relat_1(B_90, '#skF_5'))!=k2_relat_1('#skF_5') | ~v1_funct_1(B_90) | ~v1_relat_1(B_90))), inference(resolution, [status(thm)], [c_261, c_113])).
% 2.94/1.43  tff(c_571, plain, (k2_relat_1('#skF_4')='#skF_2' | ~v5_relat_1('#skF_4', '#skF_2') | k2_relat_1('#skF_5')!='#skF_3' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_550, c_267])).
% 2.94/1.43  tff(c_615, plain, (k2_relat_1('#skF_4')='#skF_2' | k2_relat_1('#skF_5')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_77, c_64, c_104, c_571])).
% 2.94/1.43  tff(c_616, plain, (k2_relat_1('#skF_5')!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_142, c_615])).
% 2.94/1.43  tff(c_105, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_97])).
% 2.94/1.43  tff(c_16, plain, (![A_10, B_12]: (r1_tarski(k2_relat_1(k5_relat_1(A_10, B_12)), k2_relat_1(B_12)) | ~v1_relat_1(B_12) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.94/1.43  tff(c_169, plain, (![B_68, A_69]: (k2_relat_1(B_68)=A_69 | ~r1_tarski(A_69, k2_relat_1(B_68)) | ~v5_relat_1(B_68, A_69) | ~v1_relat_1(B_68))), inference(resolution, [status(thm)], [c_110, c_2])).
% 2.94/1.43  tff(c_181, plain, (![A_10, B_12]: (k2_relat_1(k5_relat_1(A_10, B_12))=k2_relat_1(B_12) | ~v5_relat_1(B_12, k2_relat_1(k5_relat_1(A_10, B_12))) | ~v1_relat_1(B_12) | ~v1_relat_1(A_10))), inference(resolution, [status(thm)], [c_16, c_169])).
% 2.94/1.43  tff(c_580, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1('#skF_5') | ~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_550, c_181])).
% 2.94/1.43  tff(c_622, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_77, c_80, c_105, c_550, c_580])).
% 2.94/1.43  tff(c_641, plain, $false, inference(negUnitSimplification, [status(thm)], [c_616, c_622])).
% 2.94/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.43  
% 2.94/1.43  Inference rules
% 2.94/1.43  ----------------------
% 2.94/1.43  #Ref     : 0
% 2.94/1.43  #Sup     : 126
% 2.94/1.43  #Fact    : 0
% 2.94/1.43  #Define  : 0
% 2.94/1.43  #Split   : 3
% 2.94/1.43  #Chain   : 0
% 2.94/1.43  #Close   : 0
% 2.94/1.43  
% 2.94/1.43  Ordering : KBO
% 2.94/1.43  
% 2.94/1.43  Simplification rules
% 2.94/1.43  ----------------------
% 2.94/1.43  #Subsume      : 8
% 2.94/1.43  #Demod        : 104
% 2.94/1.43  #Tautology    : 35
% 2.94/1.43  #SimpNegUnit  : 6
% 2.94/1.43  #BackRed      : 7
% 2.94/1.43  
% 2.94/1.43  #Partial instantiations: 0
% 2.94/1.43  #Strategies tried      : 1
% 2.94/1.43  
% 2.94/1.43  Timing (in seconds)
% 2.94/1.43  ----------------------
% 2.94/1.44  Preprocessing        : 0.34
% 2.94/1.44  Parsing              : 0.19
% 2.94/1.44  CNF conversion       : 0.02
% 2.94/1.44  Main loop            : 0.33
% 2.94/1.44  Inferencing          : 0.12
% 2.94/1.44  Reduction            : 0.11
% 2.94/1.44  Demodulation         : 0.08
% 2.94/1.44  BG Simplification    : 0.02
% 2.94/1.44  Subsumption          : 0.06
% 2.94/1.44  Abstraction          : 0.02
% 2.94/1.44  MUC search           : 0.00
% 2.94/1.44  Cooper               : 0.00
% 2.94/1.44  Total                : 0.71
% 2.94/1.44  Index Insertion      : 0.00
% 2.94/1.44  Index Deletion       : 0.00
% 2.94/1.44  Index Matching       : 0.00
% 2.94/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
