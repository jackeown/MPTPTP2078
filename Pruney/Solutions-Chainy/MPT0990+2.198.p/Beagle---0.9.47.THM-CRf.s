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
% DateTime   : Thu Dec  3 10:13:25 EST 2020

% Result     : Theorem 4.77s
% Output     : CNFRefutation 4.77s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 362 expanded)
%              Number of leaves         :   40 ( 148 expanded)
%              Depth                    :   11
%              Number of atoms          :  296 (1502 expanded)
%              Number of equality atoms :   97 ( 508 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_205,negated_conjecture,(
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_179,axiom,(
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
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_96,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_118,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_108,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_137,axiom,(
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

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_163,axiom,(
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

tff(f_38,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_82,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

tff(c_52,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_117,plain,(
    ! [B_59,A_60] :
      ( v1_relat_1(B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60))
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_126,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_64,c_117])).

tff(c_135,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_126])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_66,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_146,plain,(
    ! [A_64,B_65,C_66] :
      ( k2_relset_1(A_64,B_65,C_66) = k2_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_160,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_146])).

tff(c_642,plain,(
    ! [A_148,C_149,B_150] :
      ( k6_partfun1(A_148) = k5_relat_1(C_149,k2_funct_1(C_149))
      | k1_xboole_0 = B_150
      | ~ v2_funct_1(C_149)
      | k2_relset_1(A_148,B_150,C_149) != B_150
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_148,B_150)))
      | ~ v1_funct_2(C_149,A_148,B_150)
      | ~ v1_funct_1(C_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_648,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_642])).

tff(c_658,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_160,c_648])).

tff(c_659,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_658])).

tff(c_696,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_659])).

tff(c_74,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_72,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_70,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_36,plain,(
    ! [A_35] : k6_relat_1(A_35) = k6_partfun1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_28,plain,(
    ! [A_22] : m1_subset_1(k6_relat_1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_75,plain,(
    ! [A_22] : m1_subset_1(k6_partfun1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_28])).

tff(c_136,plain,(
    ! [A_61,B_62,D_63] :
      ( r2_relset_1(A_61,B_62,D_63,D_63)
      | ~ m1_subset_1(D_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_143,plain,(
    ! [A_22] : r2_relset_1(A_22,A_22,k6_partfun1(A_22),k6_partfun1(A_22)) ),
    inference(resolution,[status(thm)],[c_75,c_136])).

tff(c_287,plain,(
    ! [C_99,A_96,F_97,B_95,E_98,D_94] :
      ( k1_partfun1(A_96,B_95,C_99,D_94,E_98,F_97) = k5_relat_1(E_98,F_97)
      | ~ m1_subset_1(F_97,k1_zfmisc_1(k2_zfmisc_1(C_99,D_94)))
      | ~ v1_funct_1(F_97)
      | ~ m1_subset_1(E_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_95)))
      | ~ v1_funct_1(E_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_293,plain,(
    ! [A_96,B_95,E_98] :
      ( k1_partfun1(A_96,B_95,'#skF_2','#skF_1',E_98,'#skF_4') = k5_relat_1(E_98,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_95)))
      | ~ v1_funct_1(E_98) ) ),
    inference(resolution,[status(thm)],[c_64,c_287])).

tff(c_302,plain,(
    ! [A_101,B_102,E_103] :
      ( k1_partfun1(A_101,B_102,'#skF_2','#skF_1',E_103,'#skF_4') = k5_relat_1(E_103,'#skF_4')
      | ~ m1_subset_1(E_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102)))
      | ~ v1_funct_1(E_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_293])).

tff(c_308,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_302])).

tff(c_315,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_308])).

tff(c_60,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_204,plain,(
    ! [D_73,C_74,A_75,B_76] :
      ( D_73 = C_74
      | ~ r2_relset_1(A_75,B_76,C_74,D_73)
      | ~ m1_subset_1(D_73,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76)))
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_212,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_60,c_204])).

tff(c_227,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_212])).

tff(c_228,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_227])).

tff(c_320,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_228])).

tff(c_467,plain,(
    ! [A_121,F_117,B_119,D_120,C_116,E_118] :
      ( m1_subset_1(k1_partfun1(A_121,B_119,C_116,D_120,E_118,F_117),k1_zfmisc_1(k2_zfmisc_1(A_121,D_120)))
      | ~ m1_subset_1(F_117,k1_zfmisc_1(k2_zfmisc_1(C_116,D_120)))
      | ~ v1_funct_1(F_117)
      | ~ m1_subset_1(E_118,k1_zfmisc_1(k2_zfmisc_1(A_121,B_119)))
      | ~ v1_funct_1(E_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_507,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_467])).

tff(c_528,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_68,c_64,c_507])).

tff(c_530,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_320,c_528])).

tff(c_531,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_227])).

tff(c_1354,plain,(
    ! [A_183,B_184,C_185,D_186] :
      ( k2_relset_1(A_183,B_184,C_185) = B_184
      | ~ r2_relset_1(B_184,B_184,k1_partfun1(B_184,A_183,A_183,B_184,D_186,C_185),k6_partfun1(B_184))
      | ~ m1_subset_1(D_186,k1_zfmisc_1(k2_zfmisc_1(B_184,A_183)))
      | ~ v1_funct_2(D_186,B_184,A_183)
      | ~ v1_funct_1(D_186)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184)))
      | ~ v1_funct_2(C_185,A_183,B_184)
      | ~ v1_funct_1(C_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1360,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_531,c_1354])).

tff(c_1364,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_74,c_72,c_70,c_143,c_160,c_1360])).

tff(c_1366,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_696,c_1364])).

tff(c_1367,plain,
    ( ~ v2_funct_1('#skF_4')
    | k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_659])).

tff(c_1378,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1367])).

tff(c_12,plain,(
    ! [A_7] : v2_funct_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_78,plain,(
    ! [A_7] : v2_funct_1(k6_partfun1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_12])).

tff(c_62,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_2029,plain,(
    ! [B_222,D_221,E_218,C_220,A_219] :
      ( k1_xboole_0 = C_220
      | v2_funct_1(E_218)
      | k2_relset_1(A_219,B_222,D_221) != B_222
      | ~ v2_funct_1(k1_partfun1(A_219,B_222,B_222,C_220,D_221,E_218))
      | ~ m1_subset_1(E_218,k1_zfmisc_1(k2_zfmisc_1(B_222,C_220)))
      | ~ v1_funct_2(E_218,B_222,C_220)
      | ~ v1_funct_1(E_218)
      | ~ m1_subset_1(D_221,k1_zfmisc_1(k2_zfmisc_1(A_219,B_222)))
      | ~ v1_funct_2(D_221,A_219,B_222)
      | ~ v1_funct_1(D_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_2035,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_531,c_2029])).

tff(c_2043,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_66,c_64,c_78,c_62,c_2035])).

tff(c_2045,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1378,c_56,c_2043])).

tff(c_2047,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1367])).

tff(c_6,plain,(
    ! [A_6] : k1_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_81,plain,(
    ! [A_6] : k1_relat_1(k6_partfun1(A_6)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6])).

tff(c_2046,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1367])).

tff(c_18,plain,(
    ! [A_11] :
      ( k1_relat_1(k5_relat_1(A_11,k2_funct_1(A_11))) = k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2055,plain,
    ( k1_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2046,c_18])).

tff(c_2067,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_68,c_2047,c_81,c_2055])).

tff(c_596,plain,(
    ! [D_137,A_139,B_138,E_141,F_140,C_142] :
      ( k1_partfun1(A_139,B_138,C_142,D_137,E_141,F_140) = k5_relat_1(E_141,F_140)
      | ~ m1_subset_1(F_140,k1_zfmisc_1(k2_zfmisc_1(C_142,D_137)))
      | ~ v1_funct_1(F_140)
      | ~ m1_subset_1(E_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_138)))
      | ~ v1_funct_1(E_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_602,plain,(
    ! [A_139,B_138,E_141] :
      ( k1_partfun1(A_139,B_138,'#skF_2','#skF_1',E_141,'#skF_4') = k5_relat_1(E_141,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_138)))
      | ~ v1_funct_1(E_141) ) ),
    inference(resolution,[status(thm)],[c_64,c_596])).

tff(c_2083,plain,(
    ! [A_223,B_224,E_225] :
      ( k1_partfun1(A_223,B_224,'#skF_2','#skF_1',E_225,'#skF_4') = k5_relat_1(E_225,'#skF_4')
      | ~ m1_subset_1(E_225,k1_zfmisc_1(k2_zfmisc_1(A_223,B_224)))
      | ~ v1_funct_1(E_225) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_602])).

tff(c_2089,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_2083])).

tff(c_2096,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_531,c_2089])).

tff(c_123,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_70,c_117])).

tff(c_132,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_123])).

tff(c_58,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_152,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_146])).

tff(c_159,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_152])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_646,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_642])).

tff(c_654,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_62,c_58,c_646])).

tff(c_655,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_654])).

tff(c_667,plain,
    ( k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_655,c_18])).

tff(c_679,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_74,c_58,c_81,c_667])).

tff(c_20,plain,(
    ! [A_12,B_14] :
      ( k2_funct_1(A_12) = B_14
      | k6_relat_1(k1_relat_1(A_12)) != k5_relat_1(A_12,B_14)
      | k2_relat_1(A_12) != k1_relat_1(B_14)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_76,plain,(
    ! [A_12,B_14] :
      ( k2_funct_1(A_12) = B_14
      | k6_partfun1(k1_relat_1(A_12)) != k5_relat_1(A_12,B_14)
      | k2_relat_1(A_12) != k1_relat_1(B_14)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_20])).

tff(c_685,plain,(
    ! [B_14] :
      ( k2_funct_1('#skF_3') = B_14
      | k5_relat_1('#skF_3',B_14) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_14)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_679,c_76])).

tff(c_2158,plain,(
    ! [B_230] :
      ( k2_funct_1('#skF_3') = B_230
      | k5_relat_1('#skF_3',B_230) != k6_partfun1('#skF_1')
      | k1_relat_1(B_230) != '#skF_2'
      | ~ v1_funct_1(B_230)
      | ~ v1_relat_1(B_230) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_74,c_58,c_159,c_685])).

tff(c_2161,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k1_relat_1('#skF_4') != '#skF_2'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_135,c_2158])).

tff(c_2173,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2067,c_2096,c_2161])).

tff(c_2175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2173])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:15:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.77/1.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.77/1.87  
% 4.77/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.77/1.87  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.77/1.87  
% 4.77/1.87  %Foreground sorts:
% 4.77/1.87  
% 4.77/1.87  
% 4.77/1.87  %Background operators:
% 4.77/1.87  
% 4.77/1.87  
% 4.77/1.87  %Foreground operators:
% 4.77/1.87  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.77/1.87  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.77/1.87  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.77/1.87  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.77/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.77/1.87  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.77/1.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.77/1.87  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.77/1.87  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.77/1.87  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.77/1.87  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.77/1.87  tff('#skF_2', type, '#skF_2': $i).
% 4.77/1.87  tff('#skF_3', type, '#skF_3': $i).
% 4.77/1.87  tff('#skF_1', type, '#skF_1': $i).
% 4.77/1.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.77/1.87  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.77/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.77/1.87  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.77/1.87  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.77/1.87  tff('#skF_4', type, '#skF_4': $i).
% 4.77/1.87  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.77/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.77/1.87  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.77/1.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.77/1.87  
% 4.77/1.89  tff(f_205, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 4.77/1.89  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.77/1.89  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.77/1.89  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.77/1.89  tff(f_179, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 4.77/1.89  tff(f_120, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.77/1.89  tff(f_96, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 4.77/1.89  tff(f_94, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.77/1.89  tff(f_118, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.77/1.89  tff(f_108, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.77/1.89  tff(f_137, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 4.77/1.89  tff(f_42, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.77/1.89  tff(f_163, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 4.77/1.89  tff(f_38, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 4.77/1.89  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 4.77/1.89  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 4.77/1.89  tff(c_52, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.77/1.89  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.77/1.89  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.77/1.89  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.77/1.89  tff(c_117, plain, (![B_59, A_60]: (v1_relat_1(B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.77/1.89  tff(c_126, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_64, c_117])).
% 4.77/1.89  tff(c_135, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_126])).
% 4.77/1.89  tff(c_56, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.77/1.89  tff(c_66, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.77/1.89  tff(c_146, plain, (![A_64, B_65, C_66]: (k2_relset_1(A_64, B_65, C_66)=k2_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.77/1.89  tff(c_160, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_146])).
% 4.77/1.89  tff(c_642, plain, (![A_148, C_149, B_150]: (k6_partfun1(A_148)=k5_relat_1(C_149, k2_funct_1(C_149)) | k1_xboole_0=B_150 | ~v2_funct_1(C_149) | k2_relset_1(A_148, B_150, C_149)!=B_150 | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_148, B_150))) | ~v1_funct_2(C_149, A_148, B_150) | ~v1_funct_1(C_149))), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.77/1.89  tff(c_648, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_642])).
% 4.77/1.89  tff(c_658, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_160, c_648])).
% 4.77/1.89  tff(c_659, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_56, c_658])).
% 4.77/1.89  tff(c_696, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_659])).
% 4.77/1.89  tff(c_74, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.77/1.89  tff(c_72, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.77/1.89  tff(c_70, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.77/1.89  tff(c_36, plain, (![A_35]: (k6_relat_1(A_35)=k6_partfun1(A_35))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.77/1.89  tff(c_28, plain, (![A_22]: (m1_subset_1(k6_relat_1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.77/1.89  tff(c_75, plain, (![A_22]: (m1_subset_1(k6_partfun1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_28])).
% 4.77/1.89  tff(c_136, plain, (![A_61, B_62, D_63]: (r2_relset_1(A_61, B_62, D_63, D_63) | ~m1_subset_1(D_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.77/1.89  tff(c_143, plain, (![A_22]: (r2_relset_1(A_22, A_22, k6_partfun1(A_22), k6_partfun1(A_22)))), inference(resolution, [status(thm)], [c_75, c_136])).
% 4.77/1.89  tff(c_287, plain, (![C_99, A_96, F_97, B_95, E_98, D_94]: (k1_partfun1(A_96, B_95, C_99, D_94, E_98, F_97)=k5_relat_1(E_98, F_97) | ~m1_subset_1(F_97, k1_zfmisc_1(k2_zfmisc_1(C_99, D_94))) | ~v1_funct_1(F_97) | ~m1_subset_1(E_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_95))) | ~v1_funct_1(E_98))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.77/1.89  tff(c_293, plain, (![A_96, B_95, E_98]: (k1_partfun1(A_96, B_95, '#skF_2', '#skF_1', E_98, '#skF_4')=k5_relat_1(E_98, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_95))) | ~v1_funct_1(E_98))), inference(resolution, [status(thm)], [c_64, c_287])).
% 4.77/1.89  tff(c_302, plain, (![A_101, B_102, E_103]: (k1_partfun1(A_101, B_102, '#skF_2', '#skF_1', E_103, '#skF_4')=k5_relat_1(E_103, '#skF_4') | ~m1_subset_1(E_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))) | ~v1_funct_1(E_103))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_293])).
% 4.77/1.89  tff(c_308, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_302])).
% 4.77/1.89  tff(c_315, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_308])).
% 4.77/1.89  tff(c_60, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.77/1.89  tff(c_204, plain, (![D_73, C_74, A_75, B_76]: (D_73=C_74 | ~r2_relset_1(A_75, B_76, C_74, D_73) | ~m1_subset_1(D_73, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.77/1.89  tff(c_212, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_60, c_204])).
% 4.77/1.89  tff(c_227, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_212])).
% 4.77/1.89  tff(c_228, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_227])).
% 4.77/1.89  tff(c_320, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_315, c_228])).
% 4.77/1.89  tff(c_467, plain, (![A_121, F_117, B_119, D_120, C_116, E_118]: (m1_subset_1(k1_partfun1(A_121, B_119, C_116, D_120, E_118, F_117), k1_zfmisc_1(k2_zfmisc_1(A_121, D_120))) | ~m1_subset_1(F_117, k1_zfmisc_1(k2_zfmisc_1(C_116, D_120))) | ~v1_funct_1(F_117) | ~m1_subset_1(E_118, k1_zfmisc_1(k2_zfmisc_1(A_121, B_119))) | ~v1_funct_1(E_118))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.77/1.89  tff(c_507, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_315, c_467])).
% 4.77/1.89  tff(c_528, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_68, c_64, c_507])).
% 4.77/1.89  tff(c_530, plain, $false, inference(negUnitSimplification, [status(thm)], [c_320, c_528])).
% 4.77/1.89  tff(c_531, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_227])).
% 4.77/1.89  tff(c_1354, plain, (![A_183, B_184, C_185, D_186]: (k2_relset_1(A_183, B_184, C_185)=B_184 | ~r2_relset_1(B_184, B_184, k1_partfun1(B_184, A_183, A_183, B_184, D_186, C_185), k6_partfun1(B_184)) | ~m1_subset_1(D_186, k1_zfmisc_1(k2_zfmisc_1(B_184, A_183))) | ~v1_funct_2(D_186, B_184, A_183) | ~v1_funct_1(D_186) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))) | ~v1_funct_2(C_185, A_183, B_184) | ~v1_funct_1(C_185))), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.77/1.89  tff(c_1360, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_531, c_1354])).
% 4.77/1.89  tff(c_1364, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_74, c_72, c_70, c_143, c_160, c_1360])).
% 4.77/1.89  tff(c_1366, plain, $false, inference(negUnitSimplification, [status(thm)], [c_696, c_1364])).
% 4.77/1.89  tff(c_1367, plain, (~v2_funct_1('#skF_4') | k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_659])).
% 4.77/1.89  tff(c_1378, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1367])).
% 4.77/1.89  tff(c_12, plain, (![A_7]: (v2_funct_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.77/1.89  tff(c_78, plain, (![A_7]: (v2_funct_1(k6_partfun1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_12])).
% 4.77/1.89  tff(c_62, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.77/1.89  tff(c_2029, plain, (![B_222, D_221, E_218, C_220, A_219]: (k1_xboole_0=C_220 | v2_funct_1(E_218) | k2_relset_1(A_219, B_222, D_221)!=B_222 | ~v2_funct_1(k1_partfun1(A_219, B_222, B_222, C_220, D_221, E_218)) | ~m1_subset_1(E_218, k1_zfmisc_1(k2_zfmisc_1(B_222, C_220))) | ~v1_funct_2(E_218, B_222, C_220) | ~v1_funct_1(E_218) | ~m1_subset_1(D_221, k1_zfmisc_1(k2_zfmisc_1(A_219, B_222))) | ~v1_funct_2(D_221, A_219, B_222) | ~v1_funct_1(D_221))), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.77/1.89  tff(c_2035, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_531, c_2029])).
% 4.77/1.89  tff(c_2043, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_66, c_64, c_78, c_62, c_2035])).
% 4.77/1.89  tff(c_2045, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1378, c_56, c_2043])).
% 4.77/1.89  tff(c_2047, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_1367])).
% 4.77/1.89  tff(c_6, plain, (![A_6]: (k1_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.77/1.89  tff(c_81, plain, (![A_6]: (k1_relat_1(k6_partfun1(A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_6])).
% 4.77/1.89  tff(c_2046, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_1367])).
% 4.77/1.89  tff(c_18, plain, (![A_11]: (k1_relat_1(k5_relat_1(A_11, k2_funct_1(A_11)))=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.77/1.89  tff(c_2055, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2046, c_18])).
% 4.77/1.89  tff(c_2067, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_135, c_68, c_2047, c_81, c_2055])).
% 4.77/1.89  tff(c_596, plain, (![D_137, A_139, B_138, E_141, F_140, C_142]: (k1_partfun1(A_139, B_138, C_142, D_137, E_141, F_140)=k5_relat_1(E_141, F_140) | ~m1_subset_1(F_140, k1_zfmisc_1(k2_zfmisc_1(C_142, D_137))) | ~v1_funct_1(F_140) | ~m1_subset_1(E_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_138))) | ~v1_funct_1(E_141))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.77/1.89  tff(c_602, plain, (![A_139, B_138, E_141]: (k1_partfun1(A_139, B_138, '#skF_2', '#skF_1', E_141, '#skF_4')=k5_relat_1(E_141, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_138))) | ~v1_funct_1(E_141))), inference(resolution, [status(thm)], [c_64, c_596])).
% 4.77/1.89  tff(c_2083, plain, (![A_223, B_224, E_225]: (k1_partfun1(A_223, B_224, '#skF_2', '#skF_1', E_225, '#skF_4')=k5_relat_1(E_225, '#skF_4') | ~m1_subset_1(E_225, k1_zfmisc_1(k2_zfmisc_1(A_223, B_224))) | ~v1_funct_1(E_225))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_602])).
% 4.77/1.89  tff(c_2089, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_2083])).
% 4.77/1.89  tff(c_2096, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_531, c_2089])).
% 4.77/1.89  tff(c_123, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_70, c_117])).
% 4.77/1.89  tff(c_132, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_123])).
% 4.77/1.89  tff(c_58, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.77/1.89  tff(c_152, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_146])).
% 4.77/1.89  tff(c_159, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_152])).
% 4.77/1.89  tff(c_54, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.77/1.89  tff(c_646, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_642])).
% 4.77/1.89  tff(c_654, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_62, c_58, c_646])).
% 4.77/1.89  tff(c_655, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_54, c_654])).
% 4.77/1.89  tff(c_667, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_655, c_18])).
% 4.77/1.89  tff(c_679, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_132, c_74, c_58, c_81, c_667])).
% 4.77/1.89  tff(c_20, plain, (![A_12, B_14]: (k2_funct_1(A_12)=B_14 | k6_relat_1(k1_relat_1(A_12))!=k5_relat_1(A_12, B_14) | k2_relat_1(A_12)!=k1_relat_1(B_14) | ~v2_funct_1(A_12) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.77/1.89  tff(c_76, plain, (![A_12, B_14]: (k2_funct_1(A_12)=B_14 | k6_partfun1(k1_relat_1(A_12))!=k5_relat_1(A_12, B_14) | k2_relat_1(A_12)!=k1_relat_1(B_14) | ~v2_funct_1(A_12) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_20])).
% 4.77/1.89  tff(c_685, plain, (![B_14]: (k2_funct_1('#skF_3')=B_14 | k5_relat_1('#skF_3', B_14)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_14) | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_14) | ~v1_relat_1(B_14) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_679, c_76])).
% 4.77/1.89  tff(c_2158, plain, (![B_230]: (k2_funct_1('#skF_3')=B_230 | k5_relat_1('#skF_3', B_230)!=k6_partfun1('#skF_1') | k1_relat_1(B_230)!='#skF_2' | ~v1_funct_1(B_230) | ~v1_relat_1(B_230))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_74, c_58, c_159, c_685])).
% 4.77/1.89  tff(c_2161, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k1_relat_1('#skF_4')!='#skF_2' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_135, c_2158])).
% 4.77/1.89  tff(c_2173, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2067, c_2096, c_2161])).
% 4.77/1.89  tff(c_2175, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_2173])).
% 4.77/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.77/1.89  
% 4.77/1.89  Inference rules
% 4.77/1.89  ----------------------
% 4.77/1.89  #Ref     : 0
% 4.77/1.89  #Sup     : 451
% 4.77/1.89  #Fact    : 0
% 4.77/1.89  #Define  : 0
% 4.77/1.89  #Split   : 15
% 4.77/1.89  #Chain   : 0
% 4.77/1.89  #Close   : 0
% 4.77/1.89  
% 4.77/1.89  Ordering : KBO
% 4.77/1.89  
% 4.77/1.89  Simplification rules
% 4.77/1.89  ----------------------
% 4.77/1.89  #Subsume      : 11
% 4.77/1.89  #Demod        : 556
% 4.77/1.89  #Tautology    : 146
% 4.77/1.89  #SimpNegUnit  : 54
% 4.77/1.89  #BackRed      : 15
% 4.77/1.89  
% 4.77/1.89  #Partial instantiations: 0
% 4.77/1.89  #Strategies tried      : 1
% 4.77/1.89  
% 4.77/1.89  Timing (in seconds)
% 4.77/1.89  ----------------------
% 4.77/1.89  Preprocessing        : 0.36
% 4.77/1.90  Parsing              : 0.19
% 4.77/1.90  CNF conversion       : 0.03
% 4.77/1.90  Main loop            : 0.72
% 4.77/1.90  Inferencing          : 0.24
% 4.77/1.90  Reduction            : 0.26
% 4.77/1.90  Demodulation         : 0.19
% 4.77/1.90  BG Simplification    : 0.03
% 4.77/1.90  Subsumption          : 0.14
% 4.77/1.90  Abstraction          : 0.03
% 4.77/1.90  MUC search           : 0.00
% 4.77/1.90  Cooper               : 0.00
% 4.77/1.90  Total                : 1.12
% 4.77/1.90  Index Insertion      : 0.00
% 4.77/1.90  Index Deletion       : 0.00
% 4.77/1.90  Index Matching       : 0.00
% 4.77/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
