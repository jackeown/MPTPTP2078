%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:13 EST 2020

% Result     : Theorem 7.41s
% Output     : CNFRefutation 7.62s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 362 expanded)
%              Number of leaves         :   44 ( 151 expanded)
%              Depth                    :   13
%              Number of atoms          :  285 (1441 expanded)
%              Number of equality atoms :   95 ( 471 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_195,negated_conjecture,(
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

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_153,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_50,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_119,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_151,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_129,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_127,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_141,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_169,axiom,(
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

tff(f_86,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
          & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
           => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_113,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(A) = k1_relat_1(B)
              & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

tff(c_56,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_119,plain,(
    ! [B_54,A_55] :
      ( v1_relat_1(B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_55))
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_128,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_68,c_119])).

tff(c_137,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_128])).

tff(c_50,plain,(
    ! [A_42] : k6_relat_1(A_42) = k6_partfun1(A_42) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_16,plain,(
    ! [A_10] : k1_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_83,plain,(
    ! [A_10] : k1_relat_1(k6_partfun1(A_10)) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_16])).

tff(c_156,plain,(
    ! [C_63,A_64,B_65] :
      ( v4_relat_1(C_63,A_64)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_168,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_156])).

tff(c_78,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_74,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_669,plain,(
    ! [E_140,F_135,D_137,B_138,A_136,C_139] :
      ( k1_partfun1(A_136,B_138,C_139,D_137,E_140,F_135) = k5_relat_1(E_140,F_135)
      | ~ m1_subset_1(F_135,k1_zfmisc_1(k2_zfmisc_1(C_139,D_137)))
      | ~ v1_funct_1(F_135)
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1(A_136,B_138)))
      | ~ v1_funct_1(E_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_675,plain,(
    ! [A_136,B_138,E_140] :
      ( k1_partfun1(A_136,B_138,'#skF_2','#skF_1',E_140,'#skF_4') = k5_relat_1(E_140,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1(A_136,B_138)))
      | ~ v1_funct_1(E_140) ) ),
    inference(resolution,[status(thm)],[c_68,c_669])).

tff(c_711,plain,(
    ! [A_145,B_146,E_147] :
      ( k1_partfun1(A_145,B_146,'#skF_2','#skF_1',E_147,'#skF_4') = k5_relat_1(E_147,'#skF_4')
      | ~ m1_subset_1(E_147,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146)))
      | ~ v1_funct_1(E_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_675])).

tff(c_717,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_711])).

tff(c_724,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_717])).

tff(c_42,plain,(
    ! [A_29] : m1_subset_1(k6_relat_1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_79,plain,(
    ! [A_29] : m1_subset_1(k6_partfun1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_42])).

tff(c_64,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_364,plain,(
    ! [D_94,C_95,A_96,B_97] :
      ( D_94 = C_95
      | ~ r2_relset_1(A_96,B_97,C_95,D_94)
      | ~ m1_subset_1(D_94,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97)))
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_372,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_64,c_364])).

tff(c_387,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_372])).

tff(c_527,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_387])).

tff(c_729,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_724,c_527])).

tff(c_954,plain,(
    ! [F_158,D_161,A_159,C_156,B_157,E_160] :
      ( m1_subset_1(k1_partfun1(A_159,B_157,C_156,D_161,E_160,F_158),k1_zfmisc_1(k2_zfmisc_1(A_159,D_161)))
      | ~ m1_subset_1(F_158,k1_zfmisc_1(k2_zfmisc_1(C_156,D_161)))
      | ~ v1_funct_1(F_158)
      | ~ m1_subset_1(E_160,k1_zfmisc_1(k2_zfmisc_1(A_159,B_157)))
      | ~ v1_funct_1(E_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_988,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_724,c_954])).

tff(c_1010,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_68,c_988])).

tff(c_1012,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_729,c_1010])).

tff(c_1013,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_387])).

tff(c_1076,plain,(
    ! [B_180,A_178,D_179,C_181,F_177,E_182] :
      ( k1_partfun1(A_178,B_180,C_181,D_179,E_182,F_177) = k5_relat_1(E_182,F_177)
      | ~ m1_subset_1(F_177,k1_zfmisc_1(k2_zfmisc_1(C_181,D_179)))
      | ~ v1_funct_1(F_177)
      | ~ m1_subset_1(E_182,k1_zfmisc_1(k2_zfmisc_1(A_178,B_180)))
      | ~ v1_funct_1(E_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_1082,plain,(
    ! [A_178,B_180,E_182] :
      ( k1_partfun1(A_178,B_180,'#skF_2','#skF_1',E_182,'#skF_4') = k5_relat_1(E_182,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_182,k1_zfmisc_1(k2_zfmisc_1(A_178,B_180)))
      | ~ v1_funct_1(E_182) ) ),
    inference(resolution,[status(thm)],[c_68,c_1076])).

tff(c_1318,plain,(
    ! [A_197,B_198,E_199] :
      ( k1_partfun1(A_197,B_198,'#skF_2','#skF_1',E_199,'#skF_4') = k5_relat_1(E_199,'#skF_4')
      | ~ m1_subset_1(E_199,k1_zfmisc_1(k2_zfmisc_1(A_197,B_198)))
      | ~ v1_funct_1(E_199) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1082])).

tff(c_1324,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_1318])).

tff(c_1331,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1013,c_1324])).

tff(c_125,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_74,c_119])).

tff(c_134,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_125])).

tff(c_62,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_76,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_66,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_1122,plain,(
    ! [A_188,C_189,B_190] :
      ( k6_partfun1(A_188) = k5_relat_1(C_189,k2_funct_1(C_189))
      | k1_xboole_0 = B_190
      | ~ v2_funct_1(C_189)
      | k2_relset_1(A_188,B_190,C_189) != B_190
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_188,B_190)))
      | ~ v1_funct_2(C_189,A_188,B_190)
      | ~ v1_funct_1(C_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_1126,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_1122])).

tff(c_1132,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_66,c_62,c_1126])).

tff(c_1133,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1132])).

tff(c_26,plain,(
    ! [A_17] :
      ( k1_relat_1(k5_relat_1(A_17,k2_funct_1(A_17))) = k1_relat_1(A_17)
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1148,plain,
    ( k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1133,c_26])).

tff(c_1162,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_78,c_62,c_83,c_1148])).

tff(c_1263,plain,(
    ! [B_194,C_195,A_196] :
      ( k6_partfun1(B_194) = k5_relat_1(k2_funct_1(C_195),C_195)
      | k1_xboole_0 = B_194
      | ~ v2_funct_1(C_195)
      | k2_relset_1(A_196,B_194,C_195) != B_194
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_196,B_194)))
      | ~ v1_funct_2(C_195,A_196,B_194)
      | ~ v1_funct_1(C_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_1267,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_1263])).

tff(c_1273,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_66,c_62,c_1267])).

tff(c_1274,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1273])).

tff(c_30,plain,(
    ! [A_18] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(A_18),A_18)) = k2_relat_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1288,plain,
    ( k1_relat_1(k6_partfun1('#skF_2')) = k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1274,c_30])).

tff(c_1299,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_78,c_62,c_83,c_1288])).

tff(c_20,plain,(
    ! [B_13,A_11] :
      ( r1_tarski(k2_relat_1(B_13),k1_relat_1(A_11))
      | k1_relat_1(k5_relat_1(B_13,A_11)) != k1_relat_1(B_13)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1306,plain,(
    ! [A_11] :
      ( r1_tarski('#skF_2',k1_relat_1(A_11))
      | k1_relat_1(k5_relat_1('#skF_3',A_11)) != k1_relat_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1299,c_20])).

tff(c_1836,plain,(
    ! [A_220] :
      ( r1_tarski('#skF_2',k1_relat_1(A_220))
      | k1_relat_1(k5_relat_1('#skF_3',A_220)) != '#skF_1'
      | ~ v1_funct_1(A_220)
      | ~ v1_relat_1(A_220) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_78,c_1162,c_1306])).

tff(c_146,plain,(
    ! [B_59,A_60] :
      ( r1_tarski(k1_relat_1(B_59),A_60)
      | ~ v4_relat_1(B_59,A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_152,plain,(
    ! [B_59,A_60] :
      ( k1_relat_1(B_59) = A_60
      | ~ r1_tarski(A_60,k1_relat_1(B_59))
      | ~ v4_relat_1(B_59,A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(resolution,[status(thm)],[c_146,c_2])).

tff(c_2900,plain,(
    ! [A_267] :
      ( k1_relat_1(A_267) = '#skF_2'
      | ~ v4_relat_1(A_267,'#skF_2')
      | k1_relat_1(k5_relat_1('#skF_3',A_267)) != '#skF_1'
      | ~ v1_funct_1(A_267)
      | ~ v1_relat_1(A_267) ) ),
    inference(resolution,[status(thm)],[c_1836,c_152])).

tff(c_2903,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v4_relat_1('#skF_4','#skF_2')
    | k1_relat_1(k6_partfun1('#skF_1')) != '#skF_1'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1331,c_2900])).

tff(c_2912,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_72,c_83,c_168,c_2903])).

tff(c_32,plain,(
    ! [A_19,B_21] :
      ( k2_funct_1(A_19) = B_21
      | k6_relat_1(k1_relat_1(A_19)) != k5_relat_1(A_19,B_21)
      | k2_relat_1(A_19) != k1_relat_1(B_21)
      | ~ v2_funct_1(A_19)
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_80,plain,(
    ! [A_19,B_21] :
      ( k2_funct_1(A_19) = B_21
      | k6_partfun1(k1_relat_1(A_19)) != k5_relat_1(A_19,B_21)
      | k2_relat_1(A_19) != k1_relat_1(B_21)
      | ~ v2_funct_1(A_19)
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_32])).

tff(c_1168,plain,(
    ! [B_21] :
      ( k2_funct_1('#skF_3') = B_21
      | k5_relat_1('#skF_3',B_21) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_21)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1162,c_80])).

tff(c_1197,plain,(
    ! [B_21] :
      ( k2_funct_1('#skF_3') = B_21
      | k5_relat_1('#skF_3',B_21) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_21)
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_78,c_62,c_1168])).

tff(c_4261,plain,(
    ! [B_339] :
      ( k2_funct_1('#skF_3') = B_339
      | k5_relat_1('#skF_3',B_339) != k6_partfun1('#skF_1')
      | k1_relat_1(B_339) != '#skF_2'
      | ~ v1_funct_1(B_339)
      | ~ v1_relat_1(B_339) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1299,c_1197])).

tff(c_4354,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k1_relat_1('#skF_4') != '#skF_2'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_137,c_4261])).

tff(c_4448,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2912,c_1331,c_4354])).

tff(c_4450,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_4448])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:12:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.41/2.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.59/2.66  
% 7.59/2.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.59/2.66  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.59/2.66  
% 7.59/2.66  %Foreground sorts:
% 7.59/2.66  
% 7.59/2.66  
% 7.59/2.66  %Background operators:
% 7.59/2.66  
% 7.59/2.66  
% 7.59/2.66  %Foreground operators:
% 7.59/2.66  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.59/2.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.59/2.66  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.59/2.66  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.59/2.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.59/2.66  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.59/2.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.59/2.66  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.59/2.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.59/2.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.59/2.66  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.59/2.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.59/2.66  tff('#skF_2', type, '#skF_2': $i).
% 7.59/2.66  tff('#skF_3', type, '#skF_3': $i).
% 7.59/2.66  tff('#skF_1', type, '#skF_1': $i).
% 7.59/2.66  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.59/2.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.59/2.66  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.59/2.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.59/2.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.59/2.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.59/2.66  tff('#skF_4', type, '#skF_4': $i).
% 7.59/2.66  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.59/2.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.59/2.66  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.59/2.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.59/2.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.59/2.66  
% 7.62/2.68  tff(f_195, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 7.62/2.68  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.62/2.68  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.62/2.68  tff(f_153, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.62/2.68  tff(f_50, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 7.62/2.68  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.62/2.68  tff(f_151, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.62/2.68  tff(f_129, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 7.62/2.68  tff(f_127, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.62/2.68  tff(f_141, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.62/2.68  tff(f_169, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 7.62/2.68  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_funct_1)).
% 7.62/2.68  tff(f_96, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_funct_1)).
% 7.62/2.68  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_funct_1)).
% 7.62/2.68  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 7.62/2.68  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.62/2.68  tff(f_113, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_funct_1)).
% 7.62/2.68  tff(c_56, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_195])).
% 7.62/2.68  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_195])).
% 7.62/2.68  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.62/2.68  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_195])).
% 7.62/2.68  tff(c_119, plain, (![B_54, A_55]: (v1_relat_1(B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(A_55)) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.62/2.68  tff(c_128, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_68, c_119])).
% 7.62/2.68  tff(c_137, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_128])).
% 7.62/2.68  tff(c_50, plain, (![A_42]: (k6_relat_1(A_42)=k6_partfun1(A_42))), inference(cnfTransformation, [status(thm)], [f_153])).
% 7.62/2.68  tff(c_16, plain, (![A_10]: (k1_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.62/2.68  tff(c_83, plain, (![A_10]: (k1_relat_1(k6_partfun1(A_10))=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_16])).
% 7.62/2.68  tff(c_156, plain, (![C_63, A_64, B_65]: (v4_relat_1(C_63, A_64) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.62/2.68  tff(c_168, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_156])).
% 7.62/2.68  tff(c_78, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 7.62/2.68  tff(c_74, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_195])).
% 7.62/2.68  tff(c_669, plain, (![E_140, F_135, D_137, B_138, A_136, C_139]: (k1_partfun1(A_136, B_138, C_139, D_137, E_140, F_135)=k5_relat_1(E_140, F_135) | ~m1_subset_1(F_135, k1_zfmisc_1(k2_zfmisc_1(C_139, D_137))) | ~v1_funct_1(F_135) | ~m1_subset_1(E_140, k1_zfmisc_1(k2_zfmisc_1(A_136, B_138))) | ~v1_funct_1(E_140))), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.62/2.68  tff(c_675, plain, (![A_136, B_138, E_140]: (k1_partfun1(A_136, B_138, '#skF_2', '#skF_1', E_140, '#skF_4')=k5_relat_1(E_140, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_140, k1_zfmisc_1(k2_zfmisc_1(A_136, B_138))) | ~v1_funct_1(E_140))), inference(resolution, [status(thm)], [c_68, c_669])).
% 7.62/2.68  tff(c_711, plain, (![A_145, B_146, E_147]: (k1_partfun1(A_145, B_146, '#skF_2', '#skF_1', E_147, '#skF_4')=k5_relat_1(E_147, '#skF_4') | ~m1_subset_1(E_147, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))) | ~v1_funct_1(E_147))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_675])).
% 7.62/2.68  tff(c_717, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_711])).
% 7.62/2.68  tff(c_724, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_717])).
% 7.62/2.68  tff(c_42, plain, (![A_29]: (m1_subset_1(k6_relat_1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.62/2.68  tff(c_79, plain, (![A_29]: (m1_subset_1(k6_partfun1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_42])).
% 7.62/2.68  tff(c_64, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_195])).
% 7.62/2.68  tff(c_364, plain, (![D_94, C_95, A_96, B_97]: (D_94=C_95 | ~r2_relset_1(A_96, B_97, C_95, D_94) | ~m1_subset_1(D_94, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.62/2.68  tff(c_372, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_64, c_364])).
% 7.62/2.68  tff(c_387, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_372])).
% 7.62/2.68  tff(c_527, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_387])).
% 7.62/2.68  tff(c_729, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_724, c_527])).
% 7.62/2.68  tff(c_954, plain, (![F_158, D_161, A_159, C_156, B_157, E_160]: (m1_subset_1(k1_partfun1(A_159, B_157, C_156, D_161, E_160, F_158), k1_zfmisc_1(k2_zfmisc_1(A_159, D_161))) | ~m1_subset_1(F_158, k1_zfmisc_1(k2_zfmisc_1(C_156, D_161))) | ~v1_funct_1(F_158) | ~m1_subset_1(E_160, k1_zfmisc_1(k2_zfmisc_1(A_159, B_157))) | ~v1_funct_1(E_160))), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.62/2.68  tff(c_988, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_724, c_954])).
% 7.62/2.68  tff(c_1010, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_68, c_988])).
% 7.62/2.68  tff(c_1012, plain, $false, inference(negUnitSimplification, [status(thm)], [c_729, c_1010])).
% 7.62/2.68  tff(c_1013, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_387])).
% 7.62/2.68  tff(c_1076, plain, (![B_180, A_178, D_179, C_181, F_177, E_182]: (k1_partfun1(A_178, B_180, C_181, D_179, E_182, F_177)=k5_relat_1(E_182, F_177) | ~m1_subset_1(F_177, k1_zfmisc_1(k2_zfmisc_1(C_181, D_179))) | ~v1_funct_1(F_177) | ~m1_subset_1(E_182, k1_zfmisc_1(k2_zfmisc_1(A_178, B_180))) | ~v1_funct_1(E_182))), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.62/2.68  tff(c_1082, plain, (![A_178, B_180, E_182]: (k1_partfun1(A_178, B_180, '#skF_2', '#skF_1', E_182, '#skF_4')=k5_relat_1(E_182, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_182, k1_zfmisc_1(k2_zfmisc_1(A_178, B_180))) | ~v1_funct_1(E_182))), inference(resolution, [status(thm)], [c_68, c_1076])).
% 7.62/2.68  tff(c_1318, plain, (![A_197, B_198, E_199]: (k1_partfun1(A_197, B_198, '#skF_2', '#skF_1', E_199, '#skF_4')=k5_relat_1(E_199, '#skF_4') | ~m1_subset_1(E_199, k1_zfmisc_1(k2_zfmisc_1(A_197, B_198))) | ~v1_funct_1(E_199))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1082])).
% 7.62/2.68  tff(c_1324, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_1318])).
% 7.62/2.68  tff(c_1331, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1013, c_1324])).
% 7.62/2.68  tff(c_125, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_74, c_119])).
% 7.62/2.68  tff(c_134, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_125])).
% 7.62/2.68  tff(c_62, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 7.62/2.68  tff(c_58, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_195])).
% 7.62/2.68  tff(c_76, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_195])).
% 7.62/2.68  tff(c_66, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_195])).
% 7.62/2.68  tff(c_1122, plain, (![A_188, C_189, B_190]: (k6_partfun1(A_188)=k5_relat_1(C_189, k2_funct_1(C_189)) | k1_xboole_0=B_190 | ~v2_funct_1(C_189) | k2_relset_1(A_188, B_190, C_189)!=B_190 | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_188, B_190))) | ~v1_funct_2(C_189, A_188, B_190) | ~v1_funct_1(C_189))), inference(cnfTransformation, [status(thm)], [f_169])).
% 7.62/2.68  tff(c_1126, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_1122])).
% 7.62/2.68  tff(c_1132, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_66, c_62, c_1126])).
% 7.62/2.68  tff(c_1133, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_58, c_1132])).
% 7.62/2.68  tff(c_26, plain, (![A_17]: (k1_relat_1(k5_relat_1(A_17, k2_funct_1(A_17)))=k1_relat_1(A_17) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.62/2.68  tff(c_1148, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1133, c_26])).
% 7.62/2.68  tff(c_1162, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_134, c_78, c_62, c_83, c_1148])).
% 7.62/2.68  tff(c_1263, plain, (![B_194, C_195, A_196]: (k6_partfun1(B_194)=k5_relat_1(k2_funct_1(C_195), C_195) | k1_xboole_0=B_194 | ~v2_funct_1(C_195) | k2_relset_1(A_196, B_194, C_195)!=B_194 | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_196, B_194))) | ~v1_funct_2(C_195, A_196, B_194) | ~v1_funct_1(C_195))), inference(cnfTransformation, [status(thm)], [f_169])).
% 7.62/2.68  tff(c_1267, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_1263])).
% 7.62/2.68  tff(c_1273, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_66, c_62, c_1267])).
% 7.62/2.68  tff(c_1274, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_58, c_1273])).
% 7.62/2.68  tff(c_30, plain, (![A_18]: (k1_relat_1(k5_relat_1(k2_funct_1(A_18), A_18))=k2_relat_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.62/2.68  tff(c_1288, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1274, c_30])).
% 7.62/2.68  tff(c_1299, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_134, c_78, c_62, c_83, c_1288])).
% 7.62/2.68  tff(c_20, plain, (![B_13, A_11]: (r1_tarski(k2_relat_1(B_13), k1_relat_1(A_11)) | k1_relat_1(k5_relat_1(B_13, A_11))!=k1_relat_1(B_13) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.62/2.68  tff(c_1306, plain, (![A_11]: (r1_tarski('#skF_2', k1_relat_1(A_11)) | k1_relat_1(k5_relat_1('#skF_3', A_11))!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(superposition, [status(thm), theory('equality')], [c_1299, c_20])).
% 7.62/2.68  tff(c_1836, plain, (![A_220]: (r1_tarski('#skF_2', k1_relat_1(A_220)) | k1_relat_1(k5_relat_1('#skF_3', A_220))!='#skF_1' | ~v1_funct_1(A_220) | ~v1_relat_1(A_220))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_78, c_1162, c_1306])).
% 7.62/2.68  tff(c_146, plain, (![B_59, A_60]: (r1_tarski(k1_relat_1(B_59), A_60) | ~v4_relat_1(B_59, A_60) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.62/2.68  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.62/2.68  tff(c_152, plain, (![B_59, A_60]: (k1_relat_1(B_59)=A_60 | ~r1_tarski(A_60, k1_relat_1(B_59)) | ~v4_relat_1(B_59, A_60) | ~v1_relat_1(B_59))), inference(resolution, [status(thm)], [c_146, c_2])).
% 7.62/2.68  tff(c_2900, plain, (![A_267]: (k1_relat_1(A_267)='#skF_2' | ~v4_relat_1(A_267, '#skF_2') | k1_relat_1(k5_relat_1('#skF_3', A_267))!='#skF_1' | ~v1_funct_1(A_267) | ~v1_relat_1(A_267))), inference(resolution, [status(thm)], [c_1836, c_152])).
% 7.62/2.68  tff(c_2903, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v4_relat_1('#skF_4', '#skF_2') | k1_relat_1(k6_partfun1('#skF_1'))!='#skF_1' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1331, c_2900])).
% 7.62/2.68  tff(c_2912, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_137, c_72, c_83, c_168, c_2903])).
% 7.62/2.68  tff(c_32, plain, (![A_19, B_21]: (k2_funct_1(A_19)=B_21 | k6_relat_1(k1_relat_1(A_19))!=k5_relat_1(A_19, B_21) | k2_relat_1(A_19)!=k1_relat_1(B_21) | ~v2_funct_1(A_19) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.62/2.68  tff(c_80, plain, (![A_19, B_21]: (k2_funct_1(A_19)=B_21 | k6_partfun1(k1_relat_1(A_19))!=k5_relat_1(A_19, B_21) | k2_relat_1(A_19)!=k1_relat_1(B_21) | ~v2_funct_1(A_19) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_32])).
% 7.62/2.68  tff(c_1168, plain, (![B_21]: (k2_funct_1('#skF_3')=B_21 | k5_relat_1('#skF_3', B_21)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_21) | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_21) | ~v1_relat_1(B_21) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1162, c_80])).
% 7.62/2.68  tff(c_1197, plain, (![B_21]: (k2_funct_1('#skF_3')=B_21 | k5_relat_1('#skF_3', B_21)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_21) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_78, c_62, c_1168])).
% 7.62/2.68  tff(c_4261, plain, (![B_339]: (k2_funct_1('#skF_3')=B_339 | k5_relat_1('#skF_3', B_339)!=k6_partfun1('#skF_1') | k1_relat_1(B_339)!='#skF_2' | ~v1_funct_1(B_339) | ~v1_relat_1(B_339))), inference(demodulation, [status(thm), theory('equality')], [c_1299, c_1197])).
% 7.62/2.68  tff(c_4354, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k1_relat_1('#skF_4')!='#skF_2' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_137, c_4261])).
% 7.62/2.68  tff(c_4448, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2912, c_1331, c_4354])).
% 7.62/2.68  tff(c_4450, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_4448])).
% 7.62/2.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.62/2.68  
% 7.62/2.68  Inference rules
% 7.62/2.68  ----------------------
% 7.62/2.68  #Ref     : 0
% 7.62/2.68  #Sup     : 879
% 7.62/2.68  #Fact    : 0
% 7.62/2.68  #Define  : 0
% 7.62/2.68  #Split   : 21
% 7.62/2.68  #Chain   : 0
% 7.62/2.68  #Close   : 0
% 7.62/2.68  
% 7.62/2.68  Ordering : KBO
% 7.62/2.68  
% 7.62/2.68  Simplification rules
% 7.62/2.68  ----------------------
% 7.62/2.68  #Subsume      : 94
% 7.62/2.68  #Demod        : 1727
% 7.62/2.68  #Tautology    : 201
% 7.62/2.68  #SimpNegUnit  : 80
% 7.62/2.68  #BackRed      : 15
% 7.62/2.68  
% 7.62/2.68  #Partial instantiations: 0
% 7.62/2.68  #Strategies tried      : 1
% 7.62/2.68  
% 7.62/2.68  Timing (in seconds)
% 7.62/2.68  ----------------------
% 7.62/2.68  Preprocessing        : 0.37
% 7.62/2.68  Parsing              : 0.20
% 7.62/2.68  CNF conversion       : 0.03
% 7.62/2.68  Main loop            : 1.53
% 7.62/2.68  Inferencing          : 0.49
% 7.62/2.68  Reduction            : 0.64
% 7.62/2.68  Demodulation         : 0.49
% 7.62/2.68  BG Simplification    : 0.05
% 7.62/2.68  Subsumption          : 0.27
% 7.62/2.68  Abstraction          : 0.06
% 7.62/2.68  MUC search           : 0.00
% 7.62/2.68  Cooper               : 0.00
% 7.62/2.68  Total                : 1.94
% 7.62/2.69  Index Insertion      : 0.00
% 7.62/2.69  Index Deletion       : 0.00
% 7.62/2.69  Index Matching       : 0.00
% 7.62/2.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
