%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1015+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:15 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 203 expanded)
%              Number of leaves         :   35 (  90 expanded)
%              Depth                    :    9
%              Number of atoms          :  176 ( 700 expanded)
%              Number of equality atoms :   44 (  74 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_149,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,C,B),B)
                & v2_funct_1(B) )
             => r2_relset_1(A,A,C,k6_partfun1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_funct_2)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_129,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_64,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_40,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_74,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_121,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( ( k1_relat_1(B) = A
              & k1_relat_1(C) = A
              & r1_tarski(k2_relat_1(C),A)
              & v2_funct_1(B)
              & k5_relat_1(C,B) = B )
           => C = k6_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_105,plain,(
    ! [A_65,B_66,D_67] :
      ( r2_relset_1(A_65,B_66,D_67,D_67)
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_115,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_105])).

tff(c_50,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_80,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_92,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_80])).

tff(c_54,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_93,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_80])).

tff(c_48,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_52,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_143,plain,(
    ! [A_74,B_75,C_76] :
      ( k1_relset_1(A_74,B_75,C_76) = k1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_155,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_143])).

tff(c_377,plain,(
    ! [A_101,B_102] :
      ( k1_relset_1(A_101,A_101,B_102) = A_101
      | ~ m1_subset_1(B_102,k1_zfmisc_1(k2_zfmisc_1(A_101,A_101)))
      | ~ v1_funct_2(B_102,A_101,A_101)
      | ~ v1_funct_1(B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_392,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_377])).

tff(c_401,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_155,c_392])).

tff(c_46,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_156,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_143])).

tff(c_395,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_377])).

tff(c_404,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_156,c_395])).

tff(c_125,plain,(
    ! [A_71,B_72,C_73] :
      ( k2_relset_1(A_71,B_72,C_73) = k2_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_138,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_125])).

tff(c_222,plain,(
    ! [A_83,B_84,C_85] :
      ( m1_subset_1(k2_relset_1(A_83,B_84,C_85),k1_zfmisc_1(B_84))
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_243,plain,
    ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_222])).

tff(c_253,plain,(
    m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_243])).

tff(c_30,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(A_43,B_44)
      | ~ m1_subset_1(A_43,k1_zfmisc_1(B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_259,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_253,c_30])).

tff(c_40,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_833,plain,(
    ! [F_163,E_162,C_161,A_160,B_165,D_164] :
      ( k1_partfun1(A_160,B_165,C_161,D_164,E_162,F_163) = k5_relat_1(E_162,F_163)
      | ~ m1_subset_1(F_163,k1_zfmisc_1(k2_zfmisc_1(C_161,D_164)))
      | ~ v1_funct_1(F_163)
      | ~ m1_subset_1(E_162,k1_zfmisc_1(k2_zfmisc_1(A_160,B_165)))
      | ~ v1_funct_1(E_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_844,plain,(
    ! [A_160,B_165,E_162] :
      ( k1_partfun1(A_160,B_165,'#skF_1','#skF_1',E_162,'#skF_2') = k5_relat_1(E_162,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_162,k1_zfmisc_1(k2_zfmisc_1(A_160,B_165)))
      | ~ v1_funct_1(E_162) ) ),
    inference(resolution,[status(thm)],[c_50,c_833])).

tff(c_899,plain,(
    ! [A_169,B_170,E_171] :
      ( k1_partfun1(A_169,B_170,'#skF_1','#skF_1',E_171,'#skF_2') = k5_relat_1(E_171,'#skF_2')
      | ~ m1_subset_1(E_171,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170)))
      | ~ v1_funct_1(E_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_844])).

tff(c_917,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_899])).

tff(c_926,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_917])).

tff(c_42,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_455,plain,(
    ! [D_103,C_104,A_105,B_106] :
      ( D_103 = C_104
      | ~ r2_relset_1(A_105,B_106,C_104,D_103)
      | ~ m1_subset_1(D_103,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106)))
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_461,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2'
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_42,c_455])).

tff(c_472,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2'
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_461])).

tff(c_511,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_472])).

tff(c_934,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_926,c_511])).

tff(c_993,plain,(
    ! [B_177,F_178,E_181,A_182,D_180,C_179] :
      ( m1_subset_1(k1_partfun1(A_182,B_177,C_179,D_180,E_181,F_178),k1_zfmisc_1(k2_zfmisc_1(A_182,D_180)))
      | ~ m1_subset_1(F_178,k1_zfmisc_1(k2_zfmisc_1(C_179,D_180)))
      | ~ v1_funct_1(F_178)
      | ~ m1_subset_1(E_181,k1_zfmisc_1(k2_zfmisc_1(A_182,B_177)))
      | ~ v1_funct_1(E_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1048,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_926,c_993])).

tff(c_1073,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_54,c_50,c_1048])).

tff(c_1075,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_934,c_1073])).

tff(c_1076,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_472])).

tff(c_1456,plain,(
    ! [A_235,B_240,D_239,C_236,F_238,E_237] :
      ( k1_partfun1(A_235,B_240,C_236,D_239,E_237,F_238) = k5_relat_1(E_237,F_238)
      | ~ m1_subset_1(F_238,k1_zfmisc_1(k2_zfmisc_1(C_236,D_239)))
      | ~ v1_funct_1(F_238)
      | ~ m1_subset_1(E_237,k1_zfmisc_1(k2_zfmisc_1(A_235,B_240)))
      | ~ v1_funct_1(E_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1467,plain,(
    ! [A_235,B_240,E_237] :
      ( k1_partfun1(A_235,B_240,'#skF_1','#skF_1',E_237,'#skF_2') = k5_relat_1(E_237,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_237,k1_zfmisc_1(k2_zfmisc_1(A_235,B_240)))
      | ~ v1_funct_1(E_237) ) ),
    inference(resolution,[status(thm)],[c_50,c_1456])).

tff(c_1479,plain,(
    ! [A_241,B_242,E_243] :
      ( k1_partfun1(A_241,B_242,'#skF_1','#skF_1',E_243,'#skF_2') = k5_relat_1(E_243,'#skF_2')
      | ~ m1_subset_1(E_243,k1_zfmisc_1(k2_zfmisc_1(A_241,B_242)))
      | ~ v1_funct_1(E_243) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1467])).

tff(c_1497,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_1479])).

tff(c_1506,plain,(
    k5_relat_1('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1076,c_1497])).

tff(c_20,plain,(
    ! [A_30] : k6_relat_1(A_30) = k6_partfun1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_34,plain,(
    ! [C_48,B_46] :
      ( k6_relat_1(k1_relat_1(C_48)) = C_48
      | k5_relat_1(C_48,B_46) != B_46
      | ~ v2_funct_1(B_46)
      | ~ r1_tarski(k2_relat_1(C_48),k1_relat_1(C_48))
      | k1_relat_1(C_48) != k1_relat_1(B_46)
      | ~ v1_funct_1(C_48)
      | ~ v1_relat_1(C_48)
      | ~ v1_funct_1(B_46)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1559,plain,(
    ! [C_247,B_248] :
      ( k6_partfun1(k1_relat_1(C_247)) = C_247
      | k5_relat_1(C_247,B_248) != B_248
      | ~ v2_funct_1(B_248)
      | ~ r1_tarski(k2_relat_1(C_247),k1_relat_1(C_247))
      | k1_relat_1(C_247) != k1_relat_1(B_248)
      | ~ v1_funct_1(C_247)
      | ~ v1_relat_1(C_247)
      | ~ v1_funct_1(B_248)
      | ~ v1_relat_1(B_248) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_34])).

tff(c_1561,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v2_funct_1('#skF_2')
    | ~ r1_tarski(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k1_relat_1('#skF_2') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1506,c_1559])).

tff(c_1564,plain,(
    k6_partfun1('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_54,c_93,c_48,c_401,c_404,c_259,c_404,c_40,c_404,c_1561])).

tff(c_38,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1565,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1564,c_38])).

tff(c_1568,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_1565])).

%------------------------------------------------------------------------------
