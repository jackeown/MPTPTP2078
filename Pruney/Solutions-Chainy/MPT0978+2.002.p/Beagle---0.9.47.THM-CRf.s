%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:52 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 166 expanded)
%              Number of leaves         :   38 (  75 expanded)
%              Depth                    :    8
%              Number of atoms          :  142 ( 468 expanded)
%              Number of equality atoms :   34 (  89 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_62,axiom,(
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

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

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

tff(c_218,plain,(
    ! [A_73,B_74,C_75] :
      ( k2_relset_1(A_73,B_74,C_75) = k2_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_230,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_218])).

tff(c_42,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_236,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_42])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_97,plain,(
    ! [C_45,A_46,B_47] :
      ( v1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_109,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_97])).

tff(c_108,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_97])).

tff(c_125,plain,(
    ! [C_53,B_54,A_55] :
      ( v5_relat_1(C_53,B_54)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_55,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_136,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_125])).

tff(c_40,plain,(
    ! [A_35] : k6_relat_1(A_35) = k6_partfun1(A_35) ),
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

tff(c_56,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_471,plain,(
    ! [C_121,D_116,A_118,F_119,E_120,B_117] :
      ( k1_partfun1(A_118,B_117,C_121,D_116,E_120,F_119) = k5_relat_1(E_120,F_119)
      | ~ m1_subset_1(F_119,k1_zfmisc_1(k2_zfmisc_1(C_121,D_116)))
      | ~ v1_funct_1(F_119)
      | ~ m1_subset_1(E_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_117)))
      | ~ v1_funct_1(E_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_475,plain,(
    ! [A_118,B_117,E_120] :
      ( k1_partfun1(A_118,B_117,'#skF_1','#skF_2',E_120,'#skF_3') = k5_relat_1(E_120,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_117)))
      | ~ v1_funct_1(E_120) ) ),
    inference(resolution,[status(thm)],[c_52,c_471])).

tff(c_485,plain,(
    ! [A_122,B_123,E_124] :
      ( k1_partfun1(A_122,B_123,'#skF_1','#skF_2',E_124,'#skF_3') = k5_relat_1(E_124,'#skF_3')
      | ~ m1_subset_1(E_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123)))
      | ~ v1_funct_1(E_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_475])).

tff(c_494,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_485])).

tff(c_501,plain,(
    k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_494])).

tff(c_36,plain,(
    ! [A_28] : m1_subset_1(k6_partfun1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_44,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_296,plain,(
    ! [D_82,C_83,A_84,B_85] :
      ( D_82 = C_83
      | ~ r2_relset_1(A_84,B_85,C_83,D_82)
      | ~ m1_subset_1(D_82,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85)))
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

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

tff(c_508,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_333])).

tff(c_520,plain,(
    ! [D_130,F_129,B_131,A_126,C_127,E_128] :
      ( m1_subset_1(k1_partfun1(A_126,B_131,C_127,D_130,E_128,F_129),k1_zfmisc_1(k2_zfmisc_1(A_126,D_130)))
      | ~ m1_subset_1(F_129,k1_zfmisc_1(k2_zfmisc_1(C_127,D_130)))
      | ~ v1_funct_1(F_129)
      | ~ m1_subset_1(E_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_131)))
      | ~ v1_funct_1(E_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_550,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_520])).

tff(c_565,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_56,c_52,c_550])).

tff(c_567,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_508,c_565])).

tff(c_568,plain,(
    k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_319])).

tff(c_634,plain,(
    ! [E_151,B_148,F_150,C_152,A_149,D_147] :
      ( k1_partfun1(A_149,B_148,C_152,D_147,E_151,F_150) = k5_relat_1(E_151,F_150)
      | ~ m1_subset_1(F_150,k1_zfmisc_1(k2_zfmisc_1(C_152,D_147)))
      | ~ v1_funct_1(F_150)
      | ~ m1_subset_1(E_151,k1_zfmisc_1(k2_zfmisc_1(A_149,B_148)))
      | ~ v1_funct_1(E_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_638,plain,(
    ! [A_149,B_148,E_151] :
      ( k1_partfun1(A_149,B_148,'#skF_1','#skF_2',E_151,'#skF_3') = k5_relat_1(E_151,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_151,k1_zfmisc_1(k2_zfmisc_1(A_149,B_148)))
      | ~ v1_funct_1(E_151) ) ),
    inference(resolution,[status(thm)],[c_52,c_634])).

tff(c_649,plain,(
    ! [A_154,B_155,E_156] :
      ( k1_partfun1(A_154,B_155,'#skF_1','#skF_2',E_156,'#skF_3') = k5_relat_1(E_156,'#skF_3')
      | ~ m1_subset_1(E_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155)))
      | ~ v1_funct_1(E_156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_638])).

tff(c_658,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_649])).

tff(c_665,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_568,c_658])).

tff(c_12,plain,(
    ! [A_5,B_7] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_5,B_7)),k2_relat_1(B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_138,plain,(
    ! [B_56,A_57] :
      ( r1_tarski(k2_relat_1(B_56),A_57)
      | ~ v5_relat_1(B_56,A_57)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_251,plain,(
    ! [B_78,A_79] :
      ( k2_relat_1(B_78) = A_79
      | ~ r1_tarski(A_79,k2_relat_1(B_78))
      | ~ v5_relat_1(B_78,A_79)
      | ~ v1_relat_1(B_78) ) ),
    inference(resolution,[status(thm)],[c_138,c_2])).

tff(c_271,plain,(
    ! [A_5,B_7] :
      ( k2_relat_1(k5_relat_1(A_5,B_7)) = k2_relat_1(B_7)
      | ~ v5_relat_1(B_7,k2_relat_1(k5_relat_1(A_5,B_7)))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(resolution,[status(thm)],[c_12,c_251])).

tff(c_669,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_3')) = k2_relat_1('#skF_3')
    | ~ v5_relat_1('#skF_3',k2_relat_1(k6_partfun1('#skF_2')))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_665,c_271])).

tff(c_679,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_108,c_136,c_57,c_57,c_665,c_669])).

tff(c_681,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_679])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:48:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.47  
% 3.06/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.47  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.06/1.47  
% 3.06/1.47  %Foreground sorts:
% 3.06/1.47  
% 3.06/1.47  
% 3.06/1.47  %Background operators:
% 3.06/1.47  
% 3.06/1.47  
% 3.06/1.47  %Foreground operators:
% 3.06/1.47  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.06/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.06/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.06/1.47  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.06/1.47  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.06/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.06/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.06/1.47  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.06/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.06/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.06/1.47  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.06/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.06/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.06/1.47  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.06/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.06/1.47  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.06/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.06/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.06/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.06/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.06/1.47  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.06/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.06/1.47  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.06/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.06/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.06/1.47  
% 3.18/1.49  tff(f_116, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 3.18/1.49  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.18/1.49  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.18/1.49  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.18/1.49  tff(f_98, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.18/1.49  tff(f_48, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.18/1.49  tff(f_96, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.18/1.49  tff(f_86, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 3.18/1.49  tff(f_70, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.18/1.49  tff(f_82, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.18/1.49  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 3.18/1.49  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.18/1.49  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.18/1.49  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.18/1.49  tff(c_218, plain, (![A_73, B_74, C_75]: (k2_relset_1(A_73, B_74, C_75)=k2_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.18/1.49  tff(c_230, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_218])).
% 3.18/1.49  tff(c_42, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.18/1.49  tff(c_236, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_230, c_42])).
% 3.18/1.49  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.18/1.49  tff(c_97, plain, (![C_45, A_46, B_47]: (v1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.18/1.49  tff(c_109, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_97])).
% 3.18/1.49  tff(c_108, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_97])).
% 3.18/1.49  tff(c_125, plain, (![C_53, B_54, A_55]: (v5_relat_1(C_53, B_54) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_55, B_54))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.18/1.49  tff(c_136, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_52, c_125])).
% 3.18/1.49  tff(c_40, plain, (![A_35]: (k6_relat_1(A_35)=k6_partfun1(A_35))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.18/1.49  tff(c_16, plain, (![A_8]: (k2_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.18/1.49  tff(c_57, plain, (![A_8]: (k2_relat_1(k6_partfun1(A_8))=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_16])).
% 3.18/1.49  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.18/1.49  tff(c_56, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.18/1.49  tff(c_471, plain, (![C_121, D_116, A_118, F_119, E_120, B_117]: (k1_partfun1(A_118, B_117, C_121, D_116, E_120, F_119)=k5_relat_1(E_120, F_119) | ~m1_subset_1(F_119, k1_zfmisc_1(k2_zfmisc_1(C_121, D_116))) | ~v1_funct_1(F_119) | ~m1_subset_1(E_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_117))) | ~v1_funct_1(E_120))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.18/1.49  tff(c_475, plain, (![A_118, B_117, E_120]: (k1_partfun1(A_118, B_117, '#skF_1', '#skF_2', E_120, '#skF_3')=k5_relat_1(E_120, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_117))) | ~v1_funct_1(E_120))), inference(resolution, [status(thm)], [c_52, c_471])).
% 3.18/1.49  tff(c_485, plain, (![A_122, B_123, E_124]: (k1_partfun1(A_122, B_123, '#skF_1', '#skF_2', E_124, '#skF_3')=k5_relat_1(E_124, '#skF_3') | ~m1_subset_1(E_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))) | ~v1_funct_1(E_124))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_475])).
% 3.18/1.49  tff(c_494, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_485])).
% 3.18/1.49  tff(c_501, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_494])).
% 3.18/1.49  tff(c_36, plain, (![A_28]: (m1_subset_1(k6_partfun1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.18/1.49  tff(c_44, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.18/1.49  tff(c_296, plain, (![D_82, C_83, A_84, B_85]: (D_82=C_83 | ~r2_relset_1(A_84, B_85, C_83, D_82) | ~m1_subset_1(D_82, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.18/1.49  tff(c_304, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_44, c_296])).
% 3.18/1.49  tff(c_319, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_304])).
% 3.18/1.49  tff(c_333, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_319])).
% 3.18/1.49  tff(c_508, plain, (~m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_501, c_333])).
% 3.18/1.49  tff(c_520, plain, (![D_130, F_129, B_131, A_126, C_127, E_128]: (m1_subset_1(k1_partfun1(A_126, B_131, C_127, D_130, E_128, F_129), k1_zfmisc_1(k2_zfmisc_1(A_126, D_130))) | ~m1_subset_1(F_129, k1_zfmisc_1(k2_zfmisc_1(C_127, D_130))) | ~v1_funct_1(F_129) | ~m1_subset_1(E_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_131))) | ~v1_funct_1(E_128))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.18/1.49  tff(c_550, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_501, c_520])).
% 3.18/1.49  tff(c_565, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_56, c_52, c_550])).
% 3.18/1.49  tff(c_567, plain, $false, inference(negUnitSimplification, [status(thm)], [c_508, c_565])).
% 3.18/1.49  tff(c_568, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_319])).
% 3.18/1.49  tff(c_634, plain, (![E_151, B_148, F_150, C_152, A_149, D_147]: (k1_partfun1(A_149, B_148, C_152, D_147, E_151, F_150)=k5_relat_1(E_151, F_150) | ~m1_subset_1(F_150, k1_zfmisc_1(k2_zfmisc_1(C_152, D_147))) | ~v1_funct_1(F_150) | ~m1_subset_1(E_151, k1_zfmisc_1(k2_zfmisc_1(A_149, B_148))) | ~v1_funct_1(E_151))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.18/1.49  tff(c_638, plain, (![A_149, B_148, E_151]: (k1_partfun1(A_149, B_148, '#skF_1', '#skF_2', E_151, '#skF_3')=k5_relat_1(E_151, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_151, k1_zfmisc_1(k2_zfmisc_1(A_149, B_148))) | ~v1_funct_1(E_151))), inference(resolution, [status(thm)], [c_52, c_634])).
% 3.18/1.49  tff(c_649, plain, (![A_154, B_155, E_156]: (k1_partfun1(A_154, B_155, '#skF_1', '#skF_2', E_156, '#skF_3')=k5_relat_1(E_156, '#skF_3') | ~m1_subset_1(E_156, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))) | ~v1_funct_1(E_156))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_638])).
% 3.18/1.49  tff(c_658, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_649])).
% 3.18/1.49  tff(c_665, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_568, c_658])).
% 3.18/1.49  tff(c_12, plain, (![A_5, B_7]: (r1_tarski(k2_relat_1(k5_relat_1(A_5, B_7)), k2_relat_1(B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.18/1.49  tff(c_138, plain, (![B_56, A_57]: (r1_tarski(k2_relat_1(B_56), A_57) | ~v5_relat_1(B_56, A_57) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.18/1.49  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.18/1.49  tff(c_251, plain, (![B_78, A_79]: (k2_relat_1(B_78)=A_79 | ~r1_tarski(A_79, k2_relat_1(B_78)) | ~v5_relat_1(B_78, A_79) | ~v1_relat_1(B_78))), inference(resolution, [status(thm)], [c_138, c_2])).
% 3.18/1.49  tff(c_271, plain, (![A_5, B_7]: (k2_relat_1(k5_relat_1(A_5, B_7))=k2_relat_1(B_7) | ~v5_relat_1(B_7, k2_relat_1(k5_relat_1(A_5, B_7))) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(resolution, [status(thm)], [c_12, c_251])).
% 3.18/1.49  tff(c_669, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_3'))=k2_relat_1('#skF_3') | ~v5_relat_1('#skF_3', k2_relat_1(k6_partfun1('#skF_2'))) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_665, c_271])).
% 3.18/1.49  tff(c_679, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_109, c_108, c_136, c_57, c_57, c_665, c_669])).
% 3.18/1.49  tff(c_681, plain, $false, inference(negUnitSimplification, [status(thm)], [c_236, c_679])).
% 3.18/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.49  
% 3.18/1.49  Inference rules
% 3.18/1.49  ----------------------
% 3.18/1.49  #Ref     : 0
% 3.18/1.49  #Sup     : 127
% 3.18/1.49  #Fact    : 0
% 3.18/1.49  #Define  : 0
% 3.18/1.49  #Split   : 1
% 3.18/1.49  #Chain   : 0
% 3.18/1.49  #Close   : 0
% 3.18/1.49  
% 3.18/1.49  Ordering : KBO
% 3.18/1.49  
% 3.18/1.49  Simplification rules
% 3.18/1.49  ----------------------
% 3.18/1.49  #Subsume      : 10
% 3.18/1.49  #Demod        : 92
% 3.18/1.49  #Tautology    : 40
% 3.18/1.49  #SimpNegUnit  : 2
% 3.18/1.49  #BackRed      : 6
% 3.18/1.49  
% 3.18/1.49  #Partial instantiations: 0
% 3.18/1.49  #Strategies tried      : 1
% 3.18/1.49  
% 3.18/1.49  Timing (in seconds)
% 3.18/1.49  ----------------------
% 3.18/1.49  Preprocessing        : 0.31
% 3.18/1.49  Parsing              : 0.17
% 3.18/1.49  CNF conversion       : 0.02
% 3.18/1.49  Main loop            : 0.35
% 3.18/1.49  Inferencing          : 0.13
% 3.18/1.49  Reduction            : 0.11
% 3.18/1.49  Demodulation         : 0.08
% 3.18/1.49  BG Simplification    : 0.02
% 3.18/1.49  Subsumption          : 0.06
% 3.18/1.49  Abstraction          : 0.02
% 3.18/1.49  MUC search           : 0.00
% 3.18/1.49  Cooper               : 0.00
% 3.18/1.49  Total                : 0.70
% 3.18/1.49  Index Insertion      : 0.00
% 3.18/1.49  Index Deletion       : 0.00
% 3.18/1.49  Index Matching       : 0.00
% 3.18/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
