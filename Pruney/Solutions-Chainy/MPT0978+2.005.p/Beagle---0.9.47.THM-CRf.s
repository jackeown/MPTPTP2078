%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:52 EST 2020

% Result     : Theorem 3.68s
% Output     : CNFRefutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 165 expanded)
%              Number of leaves         :   39 (  74 expanded)
%              Depth                    :    8
%              Number of atoms          :  144 ( 420 expanded)
%              Number of equality atoms :   38 (  89 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_114,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_96,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_48,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_84,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_217,plain,(
    ! [A_78,B_79,C_80] :
      ( k2_relset_1(A_78,B_79,C_80) = k2_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_229,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_217])).

tff(c_40,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_240,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_40])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_88,plain,(
    ! [C_48,A_49,B_50] :
      ( v1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_100,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_88])).

tff(c_99,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_88])).

tff(c_128,plain,(
    ! [C_60,B_61,A_62] :
      ( v5_relat_1(C_60,B_61)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_62,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_140,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_128])).

tff(c_38,plain,(
    ! [A_41] : k6_relat_1(A_41) = k6_partfun1(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_16,plain,(
    ! [A_8] : k2_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_56,plain,(
    ! [A_8] : k2_relat_1(k6_partfun1(A_8)) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_16])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_420,plain,(
    ! [A_111,B_108,D_112,F_110,E_109,C_107] :
      ( k4_relset_1(A_111,B_108,C_107,D_112,E_109,F_110) = k5_relat_1(E_109,F_110)
      | ~ m1_subset_1(F_110,k1_zfmisc_1(k2_zfmisc_1(C_107,D_112)))
      | ~ m1_subset_1(E_109,k1_zfmisc_1(k2_zfmisc_1(A_111,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_430,plain,(
    ! [A_113,B_114,E_115] :
      ( k4_relset_1(A_113,B_114,'#skF_1','#skF_2',E_115,'#skF_3') = k5_relat_1(E_115,'#skF_3')
      | ~ m1_subset_1(E_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(resolution,[status(thm)],[c_50,c_420])).

tff(c_442,plain,(
    k4_relset_1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_430])).

tff(c_500,plain,(
    ! [C_125,A_130,D_126,F_128,E_129,B_127] :
      ( m1_subset_1(k4_relset_1(A_130,B_127,C_125,D_126,E_129,F_128),k1_zfmisc_1(k2_zfmisc_1(A_130,D_126)))
      | ~ m1_subset_1(F_128,k1_zfmisc_1(k2_zfmisc_1(C_125,D_126)))
      | ~ m1_subset_1(E_129,k1_zfmisc_1(k2_zfmisc_1(A_130,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_539,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_500])).

tff(c_561,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_50,c_539])).

tff(c_54,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_644,plain,(
    ! [B_137,A_132,D_136,C_134,E_135,F_133] :
      ( k1_partfun1(A_132,B_137,C_134,D_136,E_135,F_133) = k5_relat_1(E_135,F_133)
      | ~ m1_subset_1(F_133,k1_zfmisc_1(k2_zfmisc_1(C_134,D_136)))
      | ~ v1_funct_1(F_133)
      | ~ m1_subset_1(E_135,k1_zfmisc_1(k2_zfmisc_1(A_132,B_137)))
      | ~ v1_funct_1(E_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_654,plain,(
    ! [A_132,B_137,E_135] :
      ( k1_partfun1(A_132,B_137,'#skF_1','#skF_2',E_135,'#skF_3') = k5_relat_1(E_135,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_135,k1_zfmisc_1(k2_zfmisc_1(A_132,B_137)))
      | ~ v1_funct_1(E_135) ) ),
    inference(resolution,[status(thm)],[c_50,c_644])).

tff(c_753,plain,(
    ! [A_139,B_140,E_141] :
      ( k1_partfun1(A_139,B_140,'#skF_1','#skF_2',E_141,'#skF_3') = k5_relat_1(E_141,'#skF_3')
      | ~ m1_subset_1(E_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140)))
      | ~ v1_funct_1(E_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_654])).

tff(c_777,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_753])).

tff(c_789,plain,(
    k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_777])).

tff(c_34,plain,(
    ! [A_34] : m1_subset_1(k6_relat_1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_55,plain,(
    ! [A_34] : m1_subset_1(k6_partfun1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34])).

tff(c_42,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_296,plain,(
    ! [D_89,C_90,A_91,B_92] :
      ( D_89 = C_90
      | ~ r2_relset_1(A_91,B_92,C_90,D_89)
      | ~ m1_subset_1(D_89,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_304,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_42,c_296])).

tff(c_319,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_304])).

tff(c_360,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_319])).

tff(c_980,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_789,c_360])).

tff(c_984,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_561,c_980])).

tff(c_985,plain,(
    k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_319])).

tff(c_1253,plain,(
    ! [F_185,D_188,B_189,C_186,E_187,A_184] :
      ( k1_partfun1(A_184,B_189,C_186,D_188,E_187,F_185) = k5_relat_1(E_187,F_185)
      | ~ m1_subset_1(F_185,k1_zfmisc_1(k2_zfmisc_1(C_186,D_188)))
      | ~ v1_funct_1(F_185)
      | ~ m1_subset_1(E_187,k1_zfmisc_1(k2_zfmisc_1(A_184,B_189)))
      | ~ v1_funct_1(E_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1263,plain,(
    ! [A_184,B_189,E_187] :
      ( k1_partfun1(A_184,B_189,'#skF_1','#skF_2',E_187,'#skF_3') = k5_relat_1(E_187,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_187,k1_zfmisc_1(k2_zfmisc_1(A_184,B_189)))
      | ~ v1_funct_1(E_187) ) ),
    inference(resolution,[status(thm)],[c_50,c_1253])).

tff(c_1351,plain,(
    ! [A_190,B_191,E_192] :
      ( k1_partfun1(A_190,B_191,'#skF_1','#skF_2',E_192,'#skF_3') = k5_relat_1(E_192,'#skF_3')
      | ~ m1_subset_1(E_192,k1_zfmisc_1(k2_zfmisc_1(A_190,B_191)))
      | ~ v1_funct_1(E_192) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1263])).

tff(c_1375,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_1351])).

tff(c_1387,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_985,c_1375])).

tff(c_12,plain,(
    ! [A_5,B_7] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_5,B_7)),k2_relat_1(B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_142,plain,(
    ! [B_63,A_64] :
      ( r1_tarski(k2_relat_1(B_63),A_64)
      | ~ v5_relat_1(B_63,A_64)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_250,plain,(
    ! [B_83,A_84] :
      ( k2_relat_1(B_83) = A_84
      | ~ r1_tarski(A_84,k2_relat_1(B_83))
      | ~ v5_relat_1(B_83,A_84)
      | ~ v1_relat_1(B_83) ) ),
    inference(resolution,[status(thm)],[c_142,c_2])).

tff(c_270,plain,(
    ! [A_5,B_7] :
      ( k2_relat_1(k5_relat_1(A_5,B_7)) = k2_relat_1(B_7)
      | ~ v5_relat_1(B_7,k2_relat_1(k5_relat_1(A_5,B_7)))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(resolution,[status(thm)],[c_12,c_250])).

tff(c_1405,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_3')) = k2_relat_1('#skF_3')
    | ~ v5_relat_1('#skF_3',k2_relat_1(k6_partfun1('#skF_2')))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1387,c_270])).

tff(c_1418,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_99,c_140,c_56,c_56,c_1387,c_1405])).

tff(c_1420,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_1418])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:38:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.68/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.68/1.64  
% 3.68/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.68/1.64  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.68/1.64  
% 3.68/1.64  %Foreground sorts:
% 3.68/1.64  
% 3.68/1.64  
% 3.68/1.64  %Background operators:
% 3.68/1.64  
% 3.68/1.64  
% 3.68/1.64  %Foreground operators:
% 3.68/1.64  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.68/1.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.68/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.68/1.64  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.68/1.64  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.68/1.64  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.68/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.68/1.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.68/1.64  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.68/1.64  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.68/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.68/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.68/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.68/1.64  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.68/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.68/1.64  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.68/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.68/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.68/1.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.68/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.68/1.64  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.68/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.68/1.64  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.68/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.68/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.68/1.64  
% 3.96/1.66  tff(f_114, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 3.96/1.66  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.96/1.66  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.96/1.66  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.96/1.66  tff(f_96, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.96/1.66  tff(f_48, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.96/1.66  tff(f_74, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 3.96/1.66  tff(f_64, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 3.96/1.66  tff(f_94, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.96/1.66  tff(f_84, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 3.96/1.66  tff(f_82, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.96/1.66  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 3.96/1.66  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.96/1.66  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.96/1.66  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.96/1.66  tff(c_217, plain, (![A_78, B_79, C_80]: (k2_relset_1(A_78, B_79, C_80)=k2_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.96/1.66  tff(c_229, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_217])).
% 3.96/1.66  tff(c_40, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.96/1.66  tff(c_240, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_229, c_40])).
% 3.96/1.66  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.96/1.66  tff(c_88, plain, (![C_48, A_49, B_50]: (v1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.96/1.66  tff(c_100, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_88])).
% 3.96/1.66  tff(c_99, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_88])).
% 3.96/1.66  tff(c_128, plain, (![C_60, B_61, A_62]: (v5_relat_1(C_60, B_61) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_62, B_61))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.96/1.66  tff(c_140, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_50, c_128])).
% 3.96/1.66  tff(c_38, plain, (![A_41]: (k6_relat_1(A_41)=k6_partfun1(A_41))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.96/1.66  tff(c_16, plain, (![A_8]: (k2_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.96/1.66  tff(c_56, plain, (![A_8]: (k2_relat_1(k6_partfun1(A_8))=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_16])).
% 3.96/1.66  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.96/1.66  tff(c_420, plain, (![A_111, B_108, D_112, F_110, E_109, C_107]: (k4_relset_1(A_111, B_108, C_107, D_112, E_109, F_110)=k5_relat_1(E_109, F_110) | ~m1_subset_1(F_110, k1_zfmisc_1(k2_zfmisc_1(C_107, D_112))) | ~m1_subset_1(E_109, k1_zfmisc_1(k2_zfmisc_1(A_111, B_108))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.96/1.66  tff(c_430, plain, (![A_113, B_114, E_115]: (k4_relset_1(A_113, B_114, '#skF_1', '#skF_2', E_115, '#skF_3')=k5_relat_1(E_115, '#skF_3') | ~m1_subset_1(E_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(resolution, [status(thm)], [c_50, c_420])).
% 3.96/1.66  tff(c_442, plain, (k4_relset_1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_430])).
% 3.96/1.66  tff(c_500, plain, (![C_125, A_130, D_126, F_128, E_129, B_127]: (m1_subset_1(k4_relset_1(A_130, B_127, C_125, D_126, E_129, F_128), k1_zfmisc_1(k2_zfmisc_1(A_130, D_126))) | ~m1_subset_1(F_128, k1_zfmisc_1(k2_zfmisc_1(C_125, D_126))) | ~m1_subset_1(E_129, k1_zfmisc_1(k2_zfmisc_1(A_130, B_127))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.96/1.66  tff(c_539, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_442, c_500])).
% 3.96/1.66  tff(c_561, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_50, c_539])).
% 3.96/1.66  tff(c_54, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.96/1.66  tff(c_644, plain, (![B_137, A_132, D_136, C_134, E_135, F_133]: (k1_partfun1(A_132, B_137, C_134, D_136, E_135, F_133)=k5_relat_1(E_135, F_133) | ~m1_subset_1(F_133, k1_zfmisc_1(k2_zfmisc_1(C_134, D_136))) | ~v1_funct_1(F_133) | ~m1_subset_1(E_135, k1_zfmisc_1(k2_zfmisc_1(A_132, B_137))) | ~v1_funct_1(E_135))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.96/1.66  tff(c_654, plain, (![A_132, B_137, E_135]: (k1_partfun1(A_132, B_137, '#skF_1', '#skF_2', E_135, '#skF_3')=k5_relat_1(E_135, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_135, k1_zfmisc_1(k2_zfmisc_1(A_132, B_137))) | ~v1_funct_1(E_135))), inference(resolution, [status(thm)], [c_50, c_644])).
% 3.96/1.66  tff(c_753, plain, (![A_139, B_140, E_141]: (k1_partfun1(A_139, B_140, '#skF_1', '#skF_2', E_141, '#skF_3')=k5_relat_1(E_141, '#skF_3') | ~m1_subset_1(E_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))) | ~v1_funct_1(E_141))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_654])).
% 3.96/1.66  tff(c_777, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_753])).
% 3.96/1.66  tff(c_789, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_777])).
% 3.96/1.66  tff(c_34, plain, (![A_34]: (m1_subset_1(k6_relat_1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.96/1.66  tff(c_55, plain, (![A_34]: (m1_subset_1(k6_partfun1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34])).
% 3.96/1.66  tff(c_42, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.96/1.66  tff(c_296, plain, (![D_89, C_90, A_91, B_92]: (D_89=C_90 | ~r2_relset_1(A_91, B_92, C_90, D_89) | ~m1_subset_1(D_89, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.96/1.66  tff(c_304, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_42, c_296])).
% 3.96/1.66  tff(c_319, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_304])).
% 3.96/1.66  tff(c_360, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_319])).
% 3.96/1.66  tff(c_980, plain, (~m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_789, c_360])).
% 3.96/1.66  tff(c_984, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_561, c_980])).
% 3.96/1.66  tff(c_985, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_319])).
% 3.96/1.66  tff(c_1253, plain, (![F_185, D_188, B_189, C_186, E_187, A_184]: (k1_partfun1(A_184, B_189, C_186, D_188, E_187, F_185)=k5_relat_1(E_187, F_185) | ~m1_subset_1(F_185, k1_zfmisc_1(k2_zfmisc_1(C_186, D_188))) | ~v1_funct_1(F_185) | ~m1_subset_1(E_187, k1_zfmisc_1(k2_zfmisc_1(A_184, B_189))) | ~v1_funct_1(E_187))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.96/1.66  tff(c_1263, plain, (![A_184, B_189, E_187]: (k1_partfun1(A_184, B_189, '#skF_1', '#skF_2', E_187, '#skF_3')=k5_relat_1(E_187, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_187, k1_zfmisc_1(k2_zfmisc_1(A_184, B_189))) | ~v1_funct_1(E_187))), inference(resolution, [status(thm)], [c_50, c_1253])).
% 3.96/1.66  tff(c_1351, plain, (![A_190, B_191, E_192]: (k1_partfun1(A_190, B_191, '#skF_1', '#skF_2', E_192, '#skF_3')=k5_relat_1(E_192, '#skF_3') | ~m1_subset_1(E_192, k1_zfmisc_1(k2_zfmisc_1(A_190, B_191))) | ~v1_funct_1(E_192))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1263])).
% 3.96/1.66  tff(c_1375, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_1351])).
% 3.96/1.66  tff(c_1387, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_985, c_1375])).
% 3.96/1.66  tff(c_12, plain, (![A_5, B_7]: (r1_tarski(k2_relat_1(k5_relat_1(A_5, B_7)), k2_relat_1(B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.96/1.66  tff(c_142, plain, (![B_63, A_64]: (r1_tarski(k2_relat_1(B_63), A_64) | ~v5_relat_1(B_63, A_64) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.96/1.66  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.96/1.66  tff(c_250, plain, (![B_83, A_84]: (k2_relat_1(B_83)=A_84 | ~r1_tarski(A_84, k2_relat_1(B_83)) | ~v5_relat_1(B_83, A_84) | ~v1_relat_1(B_83))), inference(resolution, [status(thm)], [c_142, c_2])).
% 3.96/1.66  tff(c_270, plain, (![A_5, B_7]: (k2_relat_1(k5_relat_1(A_5, B_7))=k2_relat_1(B_7) | ~v5_relat_1(B_7, k2_relat_1(k5_relat_1(A_5, B_7))) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(resolution, [status(thm)], [c_12, c_250])).
% 3.96/1.66  tff(c_1405, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_3'))=k2_relat_1('#skF_3') | ~v5_relat_1('#skF_3', k2_relat_1(k6_partfun1('#skF_2'))) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1387, c_270])).
% 3.96/1.66  tff(c_1418, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_99, c_140, c_56, c_56, c_1387, c_1405])).
% 3.96/1.66  tff(c_1420, plain, $false, inference(negUnitSimplification, [status(thm)], [c_240, c_1418])).
% 3.96/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/1.66  
% 3.96/1.66  Inference rules
% 3.96/1.66  ----------------------
% 3.96/1.66  #Ref     : 0
% 3.96/1.66  #Sup     : 323
% 3.96/1.66  #Fact    : 0
% 3.96/1.66  #Define  : 0
% 3.96/1.66  #Split   : 1
% 3.96/1.66  #Chain   : 0
% 3.96/1.66  #Close   : 0
% 3.96/1.66  
% 3.96/1.66  Ordering : KBO
% 3.96/1.66  
% 3.96/1.66  Simplification rules
% 3.96/1.66  ----------------------
% 3.96/1.66  #Subsume      : 13
% 3.96/1.66  #Demod        : 138
% 3.96/1.66  #Tautology    : 79
% 3.96/1.66  #SimpNegUnit  : 2
% 3.96/1.66  #BackRed      : 10
% 3.96/1.66  
% 3.96/1.66  #Partial instantiations: 0
% 3.96/1.66  #Strategies tried      : 1
% 3.96/1.66  
% 3.96/1.66  Timing (in seconds)
% 3.96/1.66  ----------------------
% 3.96/1.66  Preprocessing        : 0.35
% 3.96/1.66  Parsing              : 0.18
% 3.96/1.66  CNF conversion       : 0.02
% 3.96/1.66  Main loop            : 0.54
% 3.96/1.66  Inferencing          : 0.19
% 3.96/1.66  Reduction            : 0.18
% 3.96/1.66  Demodulation         : 0.13
% 3.96/1.66  BG Simplification    : 0.03
% 3.96/1.66  Subsumption          : 0.09
% 3.96/1.66  Abstraction          : 0.04
% 3.96/1.66  MUC search           : 0.00
% 3.96/1.66  Cooper               : 0.00
% 3.96/1.66  Total                : 0.93
% 3.96/1.66  Index Insertion      : 0.00
% 3.96/1.66  Index Deletion       : 0.00
% 3.96/1.66  Index Matching       : 0.00
% 3.96/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
