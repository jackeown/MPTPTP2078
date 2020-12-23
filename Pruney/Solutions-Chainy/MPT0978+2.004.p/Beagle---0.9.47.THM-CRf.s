%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:52 EST 2020

% Result     : Theorem 3.88s
% Output     : CNFRefutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 157 expanded)
%              Number of leaves         :   40 (  72 expanded)
%              Depth                    :    8
%              Number of atoms          :  144 ( 414 expanded)
%              Number of equality atoms :   38 (  83 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
    ~ ! [A,B,C] :
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

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_98,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_48,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_37,axiom,(
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

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_219,plain,(
    ! [A_80,B_81,C_82] :
      ( k2_relset_1(A_80,B_81,C_82) = k2_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_231,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_219])).

tff(c_42,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_233,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_42])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_97,plain,(
    ! [C_51,A_52,B_53] :
      ( v1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_109,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_97])).

tff(c_108,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_97])).

tff(c_125,plain,(
    ! [C_59,B_60,A_61] :
      ( v5_relat_1(C_59,B_60)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_61,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_136,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_125])).

tff(c_40,plain,(
    ! [A_41] : k6_relat_1(A_41) = k6_partfun1(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_16,plain,(
    ! [A_8] : k2_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_57,plain,(
    ! [A_8] : k2_relat_1(k6_partfun1(A_8)) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_16])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_410,plain,(
    ! [E_108,B_107,A_110,D_111,F_109,C_106] :
      ( k4_relset_1(A_110,B_107,C_106,D_111,E_108,F_109) = k5_relat_1(E_108,F_109)
      | ~ m1_subset_1(F_109,k1_zfmisc_1(k2_zfmisc_1(C_106,D_111)))
      | ~ m1_subset_1(E_108,k1_zfmisc_1(k2_zfmisc_1(A_110,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_420,plain,(
    ! [A_112,B_113,E_114] :
      ( k4_relset_1(A_112,B_113,'#skF_1','#skF_2',E_114,'#skF_3') = k5_relat_1(E_114,'#skF_3')
      | ~ m1_subset_1(E_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(resolution,[status(thm)],[c_52,c_410])).

tff(c_432,plain,(
    k4_relset_1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_420])).

tff(c_491,plain,(
    ! [A_127,E_126,D_123,C_122,B_124,F_125] :
      ( m1_subset_1(k4_relset_1(A_127,B_124,C_122,D_123,E_126,F_125),k1_zfmisc_1(k2_zfmisc_1(A_127,D_123)))
      | ~ m1_subset_1(F_125,k1_zfmisc_1(k2_zfmisc_1(C_122,D_123)))
      | ~ m1_subset_1(E_126,k1_zfmisc_1(k2_zfmisc_1(A_127,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_528,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_491])).

tff(c_549,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_52,c_528])).

tff(c_56,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_621,plain,(
    ! [B_133,F_129,C_130,A_128,D_132,E_131] :
      ( k1_partfun1(A_128,B_133,C_130,D_132,E_131,F_129) = k5_relat_1(E_131,F_129)
      | ~ m1_subset_1(F_129,k1_zfmisc_1(k2_zfmisc_1(C_130,D_132)))
      | ~ v1_funct_1(F_129)
      | ~ m1_subset_1(E_131,k1_zfmisc_1(k2_zfmisc_1(A_128,B_133)))
      | ~ v1_funct_1(E_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_631,plain,(
    ! [A_128,B_133,E_131] :
      ( k1_partfun1(A_128,B_133,'#skF_1','#skF_2',E_131,'#skF_3') = k5_relat_1(E_131,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_131,k1_zfmisc_1(k2_zfmisc_1(A_128,B_133)))
      | ~ v1_funct_1(E_131) ) ),
    inference(resolution,[status(thm)],[c_52,c_621])).

tff(c_719,plain,(
    ! [A_134,B_135,E_136] :
      ( k1_partfun1(A_134,B_135,'#skF_1','#skF_2',E_136,'#skF_3') = k5_relat_1(E_136,'#skF_3')
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135)))
      | ~ v1_funct_1(E_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_631])).

tff(c_743,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_719])).

tff(c_755,plain,(
    k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_743])).

tff(c_36,plain,(
    ! [A_34] : m1_subset_1(k6_partfun1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_44,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_296,plain,(
    ! [D_88,C_89,A_90,B_91] :
      ( D_88 = C_89
      | ~ r2_relset_1(A_90,B_91,C_89,D_88)
      | ~ m1_subset_1(D_88,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91)))
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_304,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_44,c_296])).

tff(c_319,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_304])).

tff(c_333,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_319])).

tff(c_796,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_755,c_333])).

tff(c_800,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_796])).

tff(c_801,plain,(
    k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_319])).

tff(c_1086,plain,(
    ! [C_170,D_172,E_171,B_173,A_168,F_169] :
      ( k1_partfun1(A_168,B_173,C_170,D_172,E_171,F_169) = k5_relat_1(E_171,F_169)
      | ~ m1_subset_1(F_169,k1_zfmisc_1(k2_zfmisc_1(C_170,D_172)))
      | ~ v1_funct_1(F_169)
      | ~ m1_subset_1(E_171,k1_zfmisc_1(k2_zfmisc_1(A_168,B_173)))
      | ~ v1_funct_1(E_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1096,plain,(
    ! [A_168,B_173,E_171] :
      ( k1_partfun1(A_168,B_173,'#skF_1','#skF_2',E_171,'#skF_3') = k5_relat_1(E_171,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_171,k1_zfmisc_1(k2_zfmisc_1(A_168,B_173)))
      | ~ v1_funct_1(E_171) ) ),
    inference(resolution,[status(thm)],[c_52,c_1086])).

tff(c_1367,plain,(
    ! [A_187,B_188,E_189] :
      ( k1_partfun1(A_187,B_188,'#skF_1','#skF_2',E_189,'#skF_3') = k5_relat_1(E_189,'#skF_3')
      | ~ m1_subset_1(E_189,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188)))
      | ~ v1_funct_1(E_189) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1096])).

tff(c_1397,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_1367])).

tff(c_1411,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_801,c_1397])).

tff(c_12,plain,(
    ! [A_5,B_7] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_5,B_7)),k2_relat_1(B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_138,plain,(
    ! [B_62,A_63] :
      ( r1_tarski(k2_relat_1(B_62),A_63)
      | ~ v5_relat_1(B_62,A_63)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_251,plain,(
    ! [B_84,A_85] :
      ( k2_relat_1(B_84) = A_85
      | ~ r1_tarski(A_85,k2_relat_1(B_84))
      | ~ v5_relat_1(B_84,A_85)
      | ~ v1_relat_1(B_84) ) ),
    inference(resolution,[status(thm)],[c_138,c_2])).

tff(c_271,plain,(
    ! [A_5,B_7] :
      ( k2_relat_1(k5_relat_1(A_5,B_7)) = k2_relat_1(B_7)
      | ~ v5_relat_1(B_7,k2_relat_1(k5_relat_1(A_5,B_7)))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(resolution,[status(thm)],[c_12,c_251])).

tff(c_1431,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_3')) = k2_relat_1('#skF_3')
    | ~ v5_relat_1('#skF_3',k2_relat_1(k6_partfun1('#skF_2')))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1411,c_271])).

tff(c_1444,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_108,c_136,c_57,c_57,c_1411,c_1431])).

tff(c_1446,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_233,c_1444])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:40:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.88/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.70  
% 3.88/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.70  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.88/1.70  
% 3.88/1.70  %Foreground sorts:
% 3.88/1.70  
% 3.88/1.70  
% 3.88/1.70  %Background operators:
% 3.88/1.70  
% 3.88/1.70  
% 3.88/1.70  %Foreground operators:
% 3.88/1.70  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.88/1.70  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.88/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.88/1.70  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.88/1.70  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.88/1.70  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.88/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.88/1.70  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.88/1.70  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.88/1.70  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.88/1.70  tff('#skF_2', type, '#skF_2': $i).
% 3.88/1.70  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.88/1.70  tff('#skF_3', type, '#skF_3': $i).
% 3.88/1.70  tff('#skF_1', type, '#skF_1': $i).
% 3.88/1.70  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.88/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.88/1.70  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.88/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.88/1.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.88/1.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.88/1.70  tff('#skF_4', type, '#skF_4': $i).
% 3.88/1.70  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.88/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.88/1.70  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.88/1.70  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.88/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.88/1.70  
% 3.88/1.72  tff(f_116, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 3.88/1.72  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.88/1.72  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.88/1.72  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.88/1.72  tff(f_98, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.88/1.72  tff(f_48, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.88/1.72  tff(f_74, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 3.88/1.72  tff(f_64, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 3.88/1.72  tff(f_96, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.88/1.72  tff(f_86, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 3.88/1.72  tff(f_82, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.88/1.72  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 3.88/1.72  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.88/1.72  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.88/1.72  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.88/1.72  tff(c_219, plain, (![A_80, B_81, C_82]: (k2_relset_1(A_80, B_81, C_82)=k2_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.88/1.72  tff(c_231, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_219])).
% 3.88/1.72  tff(c_42, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.88/1.72  tff(c_233, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_231, c_42])).
% 3.88/1.72  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.88/1.72  tff(c_97, plain, (![C_51, A_52, B_53]: (v1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.88/1.72  tff(c_109, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_97])).
% 3.88/1.72  tff(c_108, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_97])).
% 3.88/1.72  tff(c_125, plain, (![C_59, B_60, A_61]: (v5_relat_1(C_59, B_60) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_61, B_60))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.88/1.72  tff(c_136, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_52, c_125])).
% 3.88/1.72  tff(c_40, plain, (![A_41]: (k6_relat_1(A_41)=k6_partfun1(A_41))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.88/1.72  tff(c_16, plain, (![A_8]: (k2_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.88/1.72  tff(c_57, plain, (![A_8]: (k2_relat_1(k6_partfun1(A_8))=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_16])).
% 3.88/1.72  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.88/1.72  tff(c_410, plain, (![E_108, B_107, A_110, D_111, F_109, C_106]: (k4_relset_1(A_110, B_107, C_106, D_111, E_108, F_109)=k5_relat_1(E_108, F_109) | ~m1_subset_1(F_109, k1_zfmisc_1(k2_zfmisc_1(C_106, D_111))) | ~m1_subset_1(E_108, k1_zfmisc_1(k2_zfmisc_1(A_110, B_107))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.88/1.72  tff(c_420, plain, (![A_112, B_113, E_114]: (k4_relset_1(A_112, B_113, '#skF_1', '#skF_2', E_114, '#skF_3')=k5_relat_1(E_114, '#skF_3') | ~m1_subset_1(E_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(resolution, [status(thm)], [c_52, c_410])).
% 3.88/1.72  tff(c_432, plain, (k4_relset_1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_420])).
% 3.88/1.72  tff(c_491, plain, (![A_127, E_126, D_123, C_122, B_124, F_125]: (m1_subset_1(k4_relset_1(A_127, B_124, C_122, D_123, E_126, F_125), k1_zfmisc_1(k2_zfmisc_1(A_127, D_123))) | ~m1_subset_1(F_125, k1_zfmisc_1(k2_zfmisc_1(C_122, D_123))) | ~m1_subset_1(E_126, k1_zfmisc_1(k2_zfmisc_1(A_127, B_124))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.88/1.72  tff(c_528, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_432, c_491])).
% 3.88/1.72  tff(c_549, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_52, c_528])).
% 3.88/1.72  tff(c_56, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.88/1.72  tff(c_621, plain, (![B_133, F_129, C_130, A_128, D_132, E_131]: (k1_partfun1(A_128, B_133, C_130, D_132, E_131, F_129)=k5_relat_1(E_131, F_129) | ~m1_subset_1(F_129, k1_zfmisc_1(k2_zfmisc_1(C_130, D_132))) | ~v1_funct_1(F_129) | ~m1_subset_1(E_131, k1_zfmisc_1(k2_zfmisc_1(A_128, B_133))) | ~v1_funct_1(E_131))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.88/1.72  tff(c_631, plain, (![A_128, B_133, E_131]: (k1_partfun1(A_128, B_133, '#skF_1', '#skF_2', E_131, '#skF_3')=k5_relat_1(E_131, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_131, k1_zfmisc_1(k2_zfmisc_1(A_128, B_133))) | ~v1_funct_1(E_131))), inference(resolution, [status(thm)], [c_52, c_621])).
% 3.88/1.72  tff(c_719, plain, (![A_134, B_135, E_136]: (k1_partfun1(A_134, B_135, '#skF_1', '#skF_2', E_136, '#skF_3')=k5_relat_1(E_136, '#skF_3') | ~m1_subset_1(E_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))) | ~v1_funct_1(E_136))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_631])).
% 3.88/1.72  tff(c_743, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_719])).
% 3.88/1.72  tff(c_755, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_743])).
% 3.88/1.72  tff(c_36, plain, (![A_34]: (m1_subset_1(k6_partfun1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.88/1.72  tff(c_44, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.88/1.72  tff(c_296, plain, (![D_88, C_89, A_90, B_91]: (D_88=C_89 | ~r2_relset_1(A_90, B_91, C_89, D_88) | ~m1_subset_1(D_88, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.88/1.72  tff(c_304, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_44, c_296])).
% 3.88/1.72  tff(c_319, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_304])).
% 3.88/1.72  tff(c_333, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_319])).
% 3.88/1.72  tff(c_796, plain, (~m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_755, c_333])).
% 3.88/1.72  tff(c_800, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_549, c_796])).
% 3.88/1.72  tff(c_801, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_319])).
% 3.88/1.72  tff(c_1086, plain, (![C_170, D_172, E_171, B_173, A_168, F_169]: (k1_partfun1(A_168, B_173, C_170, D_172, E_171, F_169)=k5_relat_1(E_171, F_169) | ~m1_subset_1(F_169, k1_zfmisc_1(k2_zfmisc_1(C_170, D_172))) | ~v1_funct_1(F_169) | ~m1_subset_1(E_171, k1_zfmisc_1(k2_zfmisc_1(A_168, B_173))) | ~v1_funct_1(E_171))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.88/1.72  tff(c_1096, plain, (![A_168, B_173, E_171]: (k1_partfun1(A_168, B_173, '#skF_1', '#skF_2', E_171, '#skF_3')=k5_relat_1(E_171, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_171, k1_zfmisc_1(k2_zfmisc_1(A_168, B_173))) | ~v1_funct_1(E_171))), inference(resolution, [status(thm)], [c_52, c_1086])).
% 3.88/1.72  tff(c_1367, plain, (![A_187, B_188, E_189]: (k1_partfun1(A_187, B_188, '#skF_1', '#skF_2', E_189, '#skF_3')=k5_relat_1(E_189, '#skF_3') | ~m1_subset_1(E_189, k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))) | ~v1_funct_1(E_189))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1096])).
% 3.88/1.72  tff(c_1397, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_1367])).
% 3.88/1.72  tff(c_1411, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_801, c_1397])).
% 3.88/1.72  tff(c_12, plain, (![A_5, B_7]: (r1_tarski(k2_relat_1(k5_relat_1(A_5, B_7)), k2_relat_1(B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.88/1.72  tff(c_138, plain, (![B_62, A_63]: (r1_tarski(k2_relat_1(B_62), A_63) | ~v5_relat_1(B_62, A_63) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.88/1.72  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.88/1.72  tff(c_251, plain, (![B_84, A_85]: (k2_relat_1(B_84)=A_85 | ~r1_tarski(A_85, k2_relat_1(B_84)) | ~v5_relat_1(B_84, A_85) | ~v1_relat_1(B_84))), inference(resolution, [status(thm)], [c_138, c_2])).
% 3.88/1.72  tff(c_271, plain, (![A_5, B_7]: (k2_relat_1(k5_relat_1(A_5, B_7))=k2_relat_1(B_7) | ~v5_relat_1(B_7, k2_relat_1(k5_relat_1(A_5, B_7))) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(resolution, [status(thm)], [c_12, c_251])).
% 3.88/1.72  tff(c_1431, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_3'))=k2_relat_1('#skF_3') | ~v5_relat_1('#skF_3', k2_relat_1(k6_partfun1('#skF_2'))) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1411, c_271])).
% 3.88/1.72  tff(c_1444, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_109, c_108, c_136, c_57, c_57, c_1411, c_1431])).
% 3.88/1.72  tff(c_1446, plain, $false, inference(negUnitSimplification, [status(thm)], [c_233, c_1444])).
% 3.88/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.72  
% 3.88/1.72  Inference rules
% 3.88/1.72  ----------------------
% 3.88/1.72  #Ref     : 0
% 3.88/1.72  #Sup     : 331
% 3.88/1.72  #Fact    : 0
% 3.88/1.72  #Define  : 0
% 3.88/1.72  #Split   : 1
% 3.88/1.72  #Chain   : 0
% 3.88/1.72  #Close   : 0
% 3.88/1.72  
% 3.88/1.72  Ordering : KBO
% 3.88/1.72  
% 3.88/1.72  Simplification rules
% 3.88/1.72  ----------------------
% 3.88/1.72  #Subsume      : 15
% 3.88/1.72  #Demod        : 153
% 3.88/1.72  #Tautology    : 96
% 3.88/1.72  #SimpNegUnit  : 2
% 3.88/1.72  #BackRed      : 11
% 3.88/1.72  
% 3.88/1.72  #Partial instantiations: 0
% 3.88/1.72  #Strategies tried      : 1
% 3.88/1.72  
% 3.88/1.72  Timing (in seconds)
% 3.88/1.72  ----------------------
% 3.88/1.73  Preprocessing        : 0.36
% 3.88/1.73  Parsing              : 0.19
% 3.88/1.73  CNF conversion       : 0.02
% 3.88/1.73  Main loop            : 0.54
% 3.88/1.73  Inferencing          : 0.20
% 3.88/1.73  Reduction            : 0.18
% 3.88/1.73  Demodulation         : 0.13
% 3.88/1.73  BG Simplification    : 0.03
% 3.88/1.73  Subsumption          : 0.09
% 3.88/1.73  Abstraction          : 0.03
% 3.88/1.73  MUC search           : 0.00
% 3.88/1.73  Cooper               : 0.00
% 3.88/1.73  Total                : 0.94
% 3.88/1.73  Index Insertion      : 0.00
% 3.88/1.73  Index Deletion       : 0.00
% 3.88/1.73  Index Matching       : 0.00
% 3.88/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
