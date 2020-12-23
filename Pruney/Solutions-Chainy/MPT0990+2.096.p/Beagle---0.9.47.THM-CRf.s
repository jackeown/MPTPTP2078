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
% DateTime   : Thu Dec  3 10:13:10 EST 2020

% Result     : Theorem 5.35s
% Output     : CNFRefutation 5.72s
% Verified   : 
% Statistics : Number of formulae       :  174 (1188 expanded)
%              Number of leaves         :   43 ( 433 expanded)
%              Depth                    :   21
%              Number of atoms          :  441 (4814 expanded)
%              Number of equality atoms :  167 (1736 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_193,negated_conjecture,(
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

tff(f_106,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_108,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

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

tff(f_96,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_35,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_66,axiom,(
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

tff(f_31,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_167,axiom,(
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

tff(f_49,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_125,axiom,(
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

tff(f_151,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_68,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_315,plain,(
    ! [E_94,D_89,F_92,C_91,B_93,A_90] :
      ( k1_partfun1(A_90,B_93,C_91,D_89,E_94,F_92) = k5_relat_1(E_94,F_92)
      | ~ m1_subset_1(F_92,k1_zfmisc_1(k2_zfmisc_1(C_91,D_89)))
      | ~ v1_funct_1(F_92)
      | ~ m1_subset_1(E_94,k1_zfmisc_1(k2_zfmisc_1(A_90,B_93)))
      | ~ v1_funct_1(E_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_319,plain,(
    ! [A_90,B_93,E_94] :
      ( k1_partfun1(A_90,B_93,'#skF_3','#skF_2',E_94,'#skF_5') = k5_relat_1(E_94,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_94,k1_zfmisc_1(k2_zfmisc_1(A_90,B_93)))
      | ~ v1_funct_1(E_94) ) ),
    inference(resolution,[status(thm)],[c_64,c_315])).

tff(c_331,plain,(
    ! [A_96,B_97,E_98] :
      ( k1_partfun1(A_96,B_97,'#skF_3','#skF_2',E_98,'#skF_5') = k5_relat_1(E_98,'#skF_5')
      | ~ m1_subset_1(E_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97)))
      | ~ v1_funct_1(E_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_319])).

tff(c_340,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_331])).

tff(c_347,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_340])).

tff(c_36,plain,(
    ! [A_31] : k6_relat_1(A_31) = k6_partfun1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_28,plain,(
    ! [A_18] : m1_subset_1(k6_relat_1(A_18),k1_zfmisc_1(k2_zfmisc_1(A_18,A_18))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_75,plain,(
    ! [A_18] : m1_subset_1(k6_partfun1(A_18),k1_zfmisc_1(k2_zfmisc_1(A_18,A_18))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_28])).

tff(c_60,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_208,plain,(
    ! [D_68,C_69,A_70,B_71] :
      ( D_68 = C_69
      | ~ r2_relset_1(A_70,B_71,C_69,D_68)
      | ~ m1_subset_1(D_68,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71)))
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_212,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_60,c_208])).

tff(c_223,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_212])).

tff(c_232,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_223])).

tff(c_354,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_232])).

tff(c_486,plain,(
    ! [B_114,F_116,A_115,C_112,D_117,E_113] :
      ( m1_subset_1(k1_partfun1(A_115,B_114,C_112,D_117,E_113,F_116),k1_zfmisc_1(k2_zfmisc_1(A_115,D_117)))
      | ~ m1_subset_1(F_116,k1_zfmisc_1(k2_zfmisc_1(C_112,D_117)))
      | ~ v1_funct_1(F_116)
      | ~ m1_subset_1(E_113,k1_zfmisc_1(k2_zfmisc_1(A_115,B_114)))
      | ~ v1_funct_1(E_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_523,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_486])).

tff(c_543,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_68,c_64,c_523])).

tff(c_545,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_354,c_543])).

tff(c_546,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_223])).

tff(c_589,plain,(
    ! [D_127,C_122,E_123,B_124,F_126,A_125] :
      ( v1_funct_1(k1_partfun1(A_125,B_124,C_122,D_127,E_123,F_126))
      | ~ m1_subset_1(F_126,k1_zfmisc_1(k2_zfmisc_1(C_122,D_127)))
      | ~ v1_funct_1(F_126)
      | ~ m1_subset_1(E_123,k1_zfmisc_1(k2_zfmisc_1(A_125,B_124)))
      | ~ v1_funct_1(E_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_593,plain,(
    ! [A_125,B_124,E_123] :
      ( v1_funct_1(k1_partfun1(A_125,B_124,'#skF_3','#skF_2',E_123,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_123,k1_zfmisc_1(k2_zfmisc_1(A_125,B_124)))
      | ~ v1_funct_1(E_123) ) ),
    inference(resolution,[status(thm)],[c_64,c_589])).

tff(c_603,plain,(
    ! [A_128,B_129,E_130] :
      ( v1_funct_1(k1_partfun1(A_128,B_129,'#skF_3','#skF_2',E_130,'#skF_5'))
      | ~ m1_subset_1(E_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129)))
      | ~ v1_funct_1(E_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_593])).

tff(c_612,plain,
    ( v1_funct_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_603])).

tff(c_619,plain,(
    v1_funct_1(k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_546,c_612])).

tff(c_8,plain,(
    ! [A_2] : k2_relat_1(k6_relat_1(A_2)) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_79,plain,(
    ! [A_2] : k2_relat_1(k6_partfun1(A_2)) = A_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_8])).

tff(c_10,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_78,plain,(
    ! [A_3] : v1_relat_1(k6_partfun1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_10])).

tff(c_133,plain,(
    ! [C_55,A_56,B_57] :
      ( v1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_146,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_133])).

tff(c_58,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_62,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_158,plain,(
    ! [A_62,B_63,C_64] :
      ( k2_relset_1(A_62,B_63,C_64) = k2_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_167,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_158])).

tff(c_172,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_167])).

tff(c_18,plain,(
    ! [A_5,B_7] :
      ( k2_funct_1(A_5) = B_7
      | k6_relat_1(k2_relat_1(A_5)) != k5_relat_1(B_7,A_5)
      | k2_relat_1(B_7) != k1_relat_1(A_5)
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_555,plain,(
    ! [A_118,B_119] :
      ( k2_funct_1(A_118) = B_119
      | k6_partfun1(k2_relat_1(A_118)) != k5_relat_1(B_119,A_118)
      | k2_relat_1(B_119) != k1_relat_1(A_118)
      | ~ v2_funct_1(A_118)
      | ~ v1_funct_1(B_119)
      | ~ v1_relat_1(B_119)
      | ~ v1_funct_1(A_118)
      | ~ v1_relat_1(A_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_18])).

tff(c_559,plain,(
    ! [B_119] :
      ( k2_funct_1('#skF_4') = B_119
      | k5_relat_1(B_119,'#skF_4') != k6_partfun1('#skF_3')
      | k2_relat_1(B_119) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_119)
      | ~ v1_relat_1(B_119)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_555])).

tff(c_566,plain,(
    ! [B_120] :
      ( k2_funct_1('#skF_4') = B_120
      | k5_relat_1(B_120,'#skF_4') != k6_partfun1('#skF_3')
      | k2_relat_1(B_120) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_120)
      | ~ v1_relat_1(B_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_74,c_58,c_559])).

tff(c_575,plain,(
    ! [A_3] :
      ( k6_partfun1(A_3) = k2_funct_1('#skF_4')
      | k5_relat_1(k6_partfun1(A_3),'#skF_4') != k6_partfun1('#skF_3')
      | k2_relat_1(k6_partfun1(A_3)) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(k6_partfun1(A_3)) ) ),
    inference(resolution,[status(thm)],[c_78,c_566])).

tff(c_584,plain,(
    ! [A_3] :
      ( k6_partfun1(A_3) = k2_funct_1('#skF_4')
      | k5_relat_1(k6_partfun1(A_3),'#skF_4') != k6_partfun1('#skF_3')
      | k1_relat_1('#skF_4') != A_3
      | ~ v1_funct_1(k6_partfun1(A_3)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_575])).

tff(c_623,plain,
    ( k6_partfun1('#skF_2') = k2_funct_1('#skF_4')
    | k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') != k6_partfun1('#skF_3')
    | k1_relat_1('#skF_4') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_619,c_584])).

tff(c_643,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_623])).

tff(c_6,plain,(
    ! [A_2] : k1_relat_1(k6_relat_1(A_2)) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_80,plain,(
    ! [A_2] : k1_relat_1(k6_partfun1(A_2)) = A_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6])).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_110,plain,(
    ! [A_52] :
      ( k1_xboole_0 = A_52
      | ~ v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_114,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_110])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_120,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_54])).

tff(c_72,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_50,plain,(
    ! [A_43,C_45,B_44] :
      ( k6_partfun1(A_43) = k5_relat_1(C_45,k2_funct_1(C_45))
      | k1_xboole_0 = B_44
      | ~ v2_funct_1(C_45)
      | k2_relset_1(A_43,B_44,C_45) != B_44
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44)))
      | ~ v1_funct_2(C_45,A_43,B_44)
      | ~ v1_funct_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_715,plain,(
    ! [A_149,C_150,B_151] :
      ( k6_partfun1(A_149) = k5_relat_1(C_150,k2_funct_1(C_150))
      | B_151 = '#skF_1'
      | ~ v2_funct_1(C_150)
      | k2_relset_1(A_149,B_151,C_150) != B_151
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_149,B_151)))
      | ~ v1_funct_2(C_150,A_149,B_151)
      | ~ v1_funct_1(C_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_50])).

tff(c_721,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | '#skF_3' = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_715])).

tff(c_731,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_62,c_58,c_721])).

tff(c_732,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_731])).

tff(c_16,plain,(
    ! [A_4] :
      ( k1_relat_1(k5_relat_1(A_4,k2_funct_1(A_4))) = k1_relat_1(A_4)
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_736,plain,
    ( k1_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_732,c_16])).

tff(c_743,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_74,c_58,c_80,c_736])).

tff(c_745,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_643,c_743])).

tff(c_747,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_623])).

tff(c_52,plain,(
    k2_funct_1('#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_145,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_133])).

tff(c_572,plain,
    ( k2_funct_1('#skF_4') = '#skF_5'
    | k5_relat_1('#skF_5','#skF_4') != k6_partfun1('#skF_3')
    | k2_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_145,c_566])).

tff(c_581,plain,
    ( k2_funct_1('#skF_4') = '#skF_5'
    | k5_relat_1('#skF_5','#skF_4') != k6_partfun1('#skF_3')
    | k2_relat_1('#skF_5') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_572])).

tff(c_582,plain,
    ( k5_relat_1('#skF_5','#skF_4') != k6_partfun1('#skF_3')
    | k2_relat_1('#skF_5') != k1_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_581])).

tff(c_585,plain,(
    k2_relat_1('#skF_5') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_582])).

tff(c_750,plain,(
    k2_relat_1('#skF_5') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_747,c_585])).

tff(c_66,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_147,plain,(
    ! [A_58,B_59,D_60] :
      ( r2_relset_1(A_58,B_59,D_60,D_60)
      | ~ m1_subset_1(D_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_154,plain,(
    ! [A_18] : r2_relset_1(A_18,A_18,k6_partfun1(A_18),k6_partfun1(A_18)) ),
    inference(resolution,[status(thm)],[c_75,c_147])).

tff(c_170,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_158])).

tff(c_1533,plain,(
    ! [A_207,B_208,C_209,D_210] :
      ( k2_relset_1(A_207,B_208,C_209) = B_208
      | ~ r2_relset_1(B_208,B_208,k1_partfun1(B_208,A_207,A_207,B_208,D_210,C_209),k6_partfun1(B_208))
      | ~ m1_subset_1(D_210,k1_zfmisc_1(k2_zfmisc_1(B_208,A_207)))
      | ~ v1_funct_2(D_210,B_208,A_207)
      | ~ v1_funct_1(D_210)
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208)))
      | ~ v1_funct_2(C_209,A_207,B_208)
      | ~ v1_funct_1(C_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1539,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_546,c_1533])).

tff(c_1543,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_74,c_72,c_70,c_154,c_170,c_1539])).

tff(c_1545,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_750,c_1543])).

tff(c_1546,plain,(
    k5_relat_1('#skF_5','#skF_4') != k6_partfun1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_582])).

tff(c_2812,plain,(
    ! [E_339,B_338,F_337,D_334,C_336,A_335] :
      ( k1_partfun1(A_335,B_338,C_336,D_334,E_339,F_337) = k5_relat_1(E_339,F_337)
      | ~ m1_subset_1(F_337,k1_zfmisc_1(k2_zfmisc_1(C_336,D_334)))
      | ~ v1_funct_1(F_337)
      | ~ m1_subset_1(E_339,k1_zfmisc_1(k2_zfmisc_1(A_335,B_338)))
      | ~ v1_funct_1(E_339) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2816,plain,(
    ! [A_335,B_338,E_339] :
      ( k1_partfun1(A_335,B_338,'#skF_3','#skF_2',E_339,'#skF_5') = k5_relat_1(E_339,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_339,k1_zfmisc_1(k2_zfmisc_1(A_335,B_338)))
      | ~ v1_funct_1(E_339) ) ),
    inference(resolution,[status(thm)],[c_64,c_2812])).

tff(c_2828,plain,(
    ! [A_341,B_342,E_343] :
      ( k1_partfun1(A_341,B_342,'#skF_3','#skF_2',E_343,'#skF_5') = k5_relat_1(E_343,'#skF_5')
      | ~ m1_subset_1(E_343,k1_zfmisc_1(k2_zfmisc_1(A_341,B_342)))
      | ~ v1_funct_1(E_343) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2816])).

tff(c_2837,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_2828])).

tff(c_2844,plain,(
    k5_relat_1('#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_546,c_2837])).

tff(c_1547,plain,(
    k2_relat_1('#skF_5') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_582])).

tff(c_76,plain,(
    ! [A_5,B_7] :
      ( k2_funct_1(A_5) = B_7
      | k6_partfun1(k2_relat_1(A_5)) != k5_relat_1(B_7,A_5)
      | k2_relat_1(B_7) != k1_relat_1(A_5)
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_18])).

tff(c_1551,plain,(
    ! [B_7] :
      ( k2_funct_1('#skF_5') = B_7
      | k6_partfun1(k1_relat_1('#skF_4')) != k5_relat_1(B_7,'#skF_5')
      | k2_relat_1(B_7) != k1_relat_1('#skF_5')
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1547,c_76])).

tff(c_1555,plain,(
    ! [B_7] :
      ( k2_funct_1('#skF_5') = B_7
      | k6_partfun1(k1_relat_1('#skF_4')) != k5_relat_1(B_7,'#skF_5')
      | k2_relat_1(B_7) != k1_relat_1('#skF_5')
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_68,c_1551])).

tff(c_1563,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1555])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_121,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_56])).

tff(c_12,plain,(
    ! [A_3] : v2_funct_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_77,plain,(
    ! [A_3] : v2_funct_1(k6_partfun1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_12])).

tff(c_42,plain,(
    ! [C_39,B_38,A_37,D_40,E_42] :
      ( k1_xboole_0 = C_39
      | v2_funct_1(E_42)
      | k2_relset_1(A_37,B_38,D_40) != B_38
      | ~ v2_funct_1(k1_partfun1(A_37,B_38,B_38,C_39,D_40,E_42))
      | ~ m1_subset_1(E_42,k1_zfmisc_1(k2_zfmisc_1(B_38,C_39)))
      | ~ v1_funct_2(E_42,B_38,C_39)
      | ~ v1_funct_1(E_42)
      | ~ m1_subset_1(D_40,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38)))
      | ~ v1_funct_2(D_40,A_37,B_38)
      | ~ v1_funct_1(D_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2617,plain,(
    ! [C_301,D_299,B_298,E_300,A_297] :
      ( C_301 = '#skF_1'
      | v2_funct_1(E_300)
      | k2_relset_1(A_297,B_298,D_299) != B_298
      | ~ v2_funct_1(k1_partfun1(A_297,B_298,B_298,C_301,D_299,E_300))
      | ~ m1_subset_1(E_300,k1_zfmisc_1(k2_zfmisc_1(B_298,C_301)))
      | ~ v1_funct_2(E_300,B_298,C_301)
      | ~ v1_funct_1(E_300)
      | ~ m1_subset_1(D_299,k1_zfmisc_1(k2_zfmisc_1(A_297,B_298)))
      | ~ v1_funct_2(D_299,A_297,B_298)
      | ~ v1_funct_1(D_299) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_42])).

tff(c_2625,plain,
    ( '#skF_2' = '#skF_1'
    | v2_funct_1('#skF_5')
    | k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3'
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_546,c_2617])).

tff(c_2636,plain,
    ( '#skF_2' = '#skF_1'
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_66,c_64,c_77,c_62,c_2625])).

tff(c_2638,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1563,c_121,c_2636])).

tff(c_2640,plain,(
    v2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1555])).

tff(c_2643,plain,(
    ! [A_308,C_305,B_307,E_306,D_310,F_309] :
      ( v1_funct_1(k1_partfun1(A_308,B_307,C_305,D_310,E_306,F_309))
      | ~ m1_subset_1(F_309,k1_zfmisc_1(k2_zfmisc_1(C_305,D_310)))
      | ~ v1_funct_1(F_309)
      | ~ m1_subset_1(E_306,k1_zfmisc_1(k2_zfmisc_1(A_308,B_307)))
      | ~ v1_funct_1(E_306) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2647,plain,(
    ! [A_308,B_307,E_306] :
      ( v1_funct_1(k1_partfun1(A_308,B_307,'#skF_3','#skF_2',E_306,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_306,k1_zfmisc_1(k2_zfmisc_1(A_308,B_307)))
      | ~ v1_funct_1(E_306) ) ),
    inference(resolution,[status(thm)],[c_64,c_2643])).

tff(c_2657,plain,(
    ! [A_311,B_312,E_313] :
      ( v1_funct_1(k1_partfun1(A_311,B_312,'#skF_3','#skF_2',E_313,'#skF_5'))
      | ~ m1_subset_1(E_313,k1_zfmisc_1(k2_zfmisc_1(A_311,B_312)))
      | ~ v1_funct_1(E_313) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2647])).

tff(c_2666,plain,
    ( v1_funct_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_2657])).

tff(c_2673,plain,(
    v1_funct_1(k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_546,c_2666])).

tff(c_2677,plain,
    ( k6_partfun1('#skF_2') = k2_funct_1('#skF_4')
    | k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') != k6_partfun1('#skF_3')
    | k1_relat_1('#skF_4') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_2673,c_584])).

tff(c_2679,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2677])).

tff(c_2740,plain,(
    ! [A_328,C_329,B_330] :
      ( k6_partfun1(A_328) = k5_relat_1(C_329,k2_funct_1(C_329))
      | B_330 = '#skF_1'
      | ~ v2_funct_1(C_329)
      | k2_relset_1(A_328,B_330,C_329) != B_330
      | ~ m1_subset_1(C_329,k1_zfmisc_1(k2_zfmisc_1(A_328,B_330)))
      | ~ v1_funct_2(C_329,A_328,B_330)
      | ~ v1_funct_1(C_329) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_50])).

tff(c_2746,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | '#skF_3' = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_2740])).

tff(c_2756,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_62,c_58,c_2746])).

tff(c_2757,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_2756])).

tff(c_2761,plain,
    ( k1_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2757,c_16])).

tff(c_2768,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_74,c_58,c_80,c_2761])).

tff(c_2770,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2679,c_2768])).

tff(c_2772,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2677])).

tff(c_1548,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1547,c_170])).

tff(c_2776,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2772,c_1548])).

tff(c_2868,plain,(
    ! [A_345,C_346,B_347] :
      ( k6_partfun1(A_345) = k5_relat_1(C_346,k2_funct_1(C_346))
      | B_347 = '#skF_1'
      | ~ v2_funct_1(C_346)
      | k2_relset_1(A_345,B_347,C_346) != B_347
      | ~ m1_subset_1(C_346,k1_zfmisc_1(k2_zfmisc_1(A_345,B_347)))
      | ~ v1_funct_2(C_346,A_345,B_347)
      | ~ v1_funct_1(C_346) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_50])).

tff(c_2872,plain,
    ( k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3')
    | '#skF_2' = '#skF_1'
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1('#skF_3','#skF_2','#skF_5') != '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_2868])).

tff(c_2880,plain,
    ( k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3')
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_2776,c_2640,c_2872])).

tff(c_2881,plain,(
    k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_2880])).

tff(c_2903,plain,
    ( k1_relat_1(k6_partfun1('#skF_3')) = k1_relat_1('#skF_5')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2881,c_16])).

tff(c_2910,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_68,c_2640,c_80,c_2903])).

tff(c_2639,plain,(
    ! [B_7] :
      ( k2_funct_1('#skF_5') = B_7
      | k6_partfun1(k1_relat_1('#skF_4')) != k5_relat_1(B_7,'#skF_5')
      | k2_relat_1(B_7) != k1_relat_1('#skF_5')
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(splitRight,[status(thm)],[c_1555])).

tff(c_2773,plain,(
    ! [B_7] :
      ( k2_funct_1('#skF_5') = B_7
      | k5_relat_1(B_7,'#skF_5') != k6_partfun1('#skF_2')
      | k2_relat_1(B_7) != k1_relat_1('#skF_5')
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2772,c_2639])).

tff(c_3022,plain,(
    ! [B_357] :
      ( k2_funct_1('#skF_5') = B_357
      | k5_relat_1(B_357,'#skF_5') != k6_partfun1('#skF_2')
      | k2_relat_1(B_357) != '#skF_3'
      | ~ v1_funct_1(B_357)
      | ~ v1_relat_1(B_357) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2910,c_2773])).

tff(c_3025,plain,
    ( k2_funct_1('#skF_5') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_5') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_3'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_146,c_3022])).

tff(c_3034,plain,(
    k2_funct_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_172,c_2844,c_3025])).

tff(c_3112,plain,(
    k5_relat_1('#skF_5','#skF_4') = k6_partfun1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3034,c_2881])).

tff(c_3115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1546,c_3112])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:35:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.35/2.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.35/2.04  
% 5.35/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.35/2.05  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.35/2.05  
% 5.35/2.05  %Foreground sorts:
% 5.35/2.05  
% 5.35/2.05  
% 5.35/2.05  %Background operators:
% 5.35/2.05  
% 5.35/2.05  
% 5.35/2.05  %Foreground operators:
% 5.35/2.05  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.35/2.05  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.35/2.05  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.35/2.05  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.35/2.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.35/2.05  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.35/2.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.35/2.05  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.35/2.05  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.35/2.05  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.35/2.05  tff('#skF_5', type, '#skF_5': $i).
% 5.35/2.05  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.35/2.05  tff('#skF_2', type, '#skF_2': $i).
% 5.35/2.05  tff('#skF_3', type, '#skF_3': $i).
% 5.35/2.05  tff('#skF_1', type, '#skF_1': $i).
% 5.35/2.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.35/2.05  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.35/2.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.35/2.05  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.35/2.05  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.35/2.05  tff('#skF_4', type, '#skF_4': $i).
% 5.35/2.05  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.35/2.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.35/2.05  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.35/2.05  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.35/2.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.35/2.05  
% 5.72/2.07  tff(f_193, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 5.72/2.07  tff(f_106, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.72/2.07  tff(f_108, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.72/2.07  tff(f_84, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 5.72/2.07  tff(f_82, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.72/2.07  tff(f_96, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.72/2.07  tff(f_35, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 5.72/2.07  tff(f_39, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.72/2.07  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.72/2.07  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.72/2.07  tff(f_66, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 5.72/2.07  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 5.72/2.07  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.72/2.07  tff(f_167, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 5.72/2.07  tff(f_49, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_funct_1)).
% 5.72/2.07  tff(f_125, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 5.72/2.07  tff(f_151, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 5.72/2.07  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_193])).
% 5.72/2.07  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_193])).
% 5.72/2.07  tff(c_68, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_193])).
% 5.72/2.07  tff(c_64, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_193])).
% 5.72/2.07  tff(c_315, plain, (![E_94, D_89, F_92, C_91, B_93, A_90]: (k1_partfun1(A_90, B_93, C_91, D_89, E_94, F_92)=k5_relat_1(E_94, F_92) | ~m1_subset_1(F_92, k1_zfmisc_1(k2_zfmisc_1(C_91, D_89))) | ~v1_funct_1(F_92) | ~m1_subset_1(E_94, k1_zfmisc_1(k2_zfmisc_1(A_90, B_93))) | ~v1_funct_1(E_94))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.72/2.07  tff(c_319, plain, (![A_90, B_93, E_94]: (k1_partfun1(A_90, B_93, '#skF_3', '#skF_2', E_94, '#skF_5')=k5_relat_1(E_94, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_94, k1_zfmisc_1(k2_zfmisc_1(A_90, B_93))) | ~v1_funct_1(E_94))), inference(resolution, [status(thm)], [c_64, c_315])).
% 5.72/2.07  tff(c_331, plain, (![A_96, B_97, E_98]: (k1_partfun1(A_96, B_97, '#skF_3', '#skF_2', E_98, '#skF_5')=k5_relat_1(E_98, '#skF_5') | ~m1_subset_1(E_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))) | ~v1_funct_1(E_98))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_319])).
% 5.72/2.07  tff(c_340, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_331])).
% 5.72/2.07  tff(c_347, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_340])).
% 5.72/2.07  tff(c_36, plain, (![A_31]: (k6_relat_1(A_31)=k6_partfun1(A_31))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.72/2.07  tff(c_28, plain, (![A_18]: (m1_subset_1(k6_relat_1(A_18), k1_zfmisc_1(k2_zfmisc_1(A_18, A_18))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.72/2.07  tff(c_75, plain, (![A_18]: (m1_subset_1(k6_partfun1(A_18), k1_zfmisc_1(k2_zfmisc_1(A_18, A_18))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_28])).
% 5.72/2.07  tff(c_60, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_193])).
% 5.72/2.07  tff(c_208, plain, (![D_68, C_69, A_70, B_71]: (D_68=C_69 | ~r2_relset_1(A_70, B_71, C_69, D_68) | ~m1_subset_1(D_68, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.72/2.07  tff(c_212, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_60, c_208])).
% 5.72/2.07  tff(c_223, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_212])).
% 5.72/2.07  tff(c_232, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_223])).
% 5.72/2.07  tff(c_354, plain, (~m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_347, c_232])).
% 5.72/2.07  tff(c_486, plain, (![B_114, F_116, A_115, C_112, D_117, E_113]: (m1_subset_1(k1_partfun1(A_115, B_114, C_112, D_117, E_113, F_116), k1_zfmisc_1(k2_zfmisc_1(A_115, D_117))) | ~m1_subset_1(F_116, k1_zfmisc_1(k2_zfmisc_1(C_112, D_117))) | ~v1_funct_1(F_116) | ~m1_subset_1(E_113, k1_zfmisc_1(k2_zfmisc_1(A_115, B_114))) | ~v1_funct_1(E_113))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.72/2.07  tff(c_523, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_347, c_486])).
% 5.72/2.07  tff(c_543, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_68, c_64, c_523])).
% 5.72/2.07  tff(c_545, plain, $false, inference(negUnitSimplification, [status(thm)], [c_354, c_543])).
% 5.72/2.07  tff(c_546, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_223])).
% 5.72/2.07  tff(c_589, plain, (![D_127, C_122, E_123, B_124, F_126, A_125]: (v1_funct_1(k1_partfun1(A_125, B_124, C_122, D_127, E_123, F_126)) | ~m1_subset_1(F_126, k1_zfmisc_1(k2_zfmisc_1(C_122, D_127))) | ~v1_funct_1(F_126) | ~m1_subset_1(E_123, k1_zfmisc_1(k2_zfmisc_1(A_125, B_124))) | ~v1_funct_1(E_123))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.72/2.07  tff(c_593, plain, (![A_125, B_124, E_123]: (v1_funct_1(k1_partfun1(A_125, B_124, '#skF_3', '#skF_2', E_123, '#skF_5')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_123, k1_zfmisc_1(k2_zfmisc_1(A_125, B_124))) | ~v1_funct_1(E_123))), inference(resolution, [status(thm)], [c_64, c_589])).
% 5.72/2.07  tff(c_603, plain, (![A_128, B_129, E_130]: (v1_funct_1(k1_partfun1(A_128, B_129, '#skF_3', '#skF_2', E_130, '#skF_5')) | ~m1_subset_1(E_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))) | ~v1_funct_1(E_130))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_593])).
% 5.72/2.07  tff(c_612, plain, (v1_funct_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_603])).
% 5.72/2.07  tff(c_619, plain, (v1_funct_1(k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_546, c_612])).
% 5.72/2.07  tff(c_8, plain, (![A_2]: (k2_relat_1(k6_relat_1(A_2))=A_2)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.72/2.07  tff(c_79, plain, (![A_2]: (k2_relat_1(k6_partfun1(A_2))=A_2)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_8])).
% 5.72/2.07  tff(c_10, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.72/2.07  tff(c_78, plain, (![A_3]: (v1_relat_1(k6_partfun1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_10])).
% 5.72/2.07  tff(c_133, plain, (![C_55, A_56, B_57]: (v1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.72/2.07  tff(c_146, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_133])).
% 5.72/2.07  tff(c_58, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_193])).
% 5.72/2.07  tff(c_62, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_193])).
% 5.72/2.07  tff(c_158, plain, (![A_62, B_63, C_64]: (k2_relset_1(A_62, B_63, C_64)=k2_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.72/2.07  tff(c_167, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_158])).
% 5.72/2.07  tff(c_172, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_167])).
% 5.72/2.07  tff(c_18, plain, (![A_5, B_7]: (k2_funct_1(A_5)=B_7 | k6_relat_1(k2_relat_1(A_5))!=k5_relat_1(B_7, A_5) | k2_relat_1(B_7)!=k1_relat_1(A_5) | ~v2_funct_1(A_5) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.72/2.07  tff(c_555, plain, (![A_118, B_119]: (k2_funct_1(A_118)=B_119 | k6_partfun1(k2_relat_1(A_118))!=k5_relat_1(B_119, A_118) | k2_relat_1(B_119)!=k1_relat_1(A_118) | ~v2_funct_1(A_118) | ~v1_funct_1(B_119) | ~v1_relat_1(B_119) | ~v1_funct_1(A_118) | ~v1_relat_1(A_118))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_18])).
% 5.72/2.07  tff(c_559, plain, (![B_119]: (k2_funct_1('#skF_4')=B_119 | k5_relat_1(B_119, '#skF_4')!=k6_partfun1('#skF_3') | k2_relat_1(B_119)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_119) | ~v1_relat_1(B_119) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_172, c_555])).
% 5.72/2.07  tff(c_566, plain, (![B_120]: (k2_funct_1('#skF_4')=B_120 | k5_relat_1(B_120, '#skF_4')!=k6_partfun1('#skF_3') | k2_relat_1(B_120)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_120) | ~v1_relat_1(B_120))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_74, c_58, c_559])).
% 5.72/2.07  tff(c_575, plain, (![A_3]: (k6_partfun1(A_3)=k2_funct_1('#skF_4') | k5_relat_1(k6_partfun1(A_3), '#skF_4')!=k6_partfun1('#skF_3') | k2_relat_1(k6_partfun1(A_3))!=k1_relat_1('#skF_4') | ~v1_funct_1(k6_partfun1(A_3)))), inference(resolution, [status(thm)], [c_78, c_566])).
% 5.72/2.07  tff(c_584, plain, (![A_3]: (k6_partfun1(A_3)=k2_funct_1('#skF_4') | k5_relat_1(k6_partfun1(A_3), '#skF_4')!=k6_partfun1('#skF_3') | k1_relat_1('#skF_4')!=A_3 | ~v1_funct_1(k6_partfun1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_575])).
% 5.72/2.07  tff(c_623, plain, (k6_partfun1('#skF_2')=k2_funct_1('#skF_4') | k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')!=k6_partfun1('#skF_3') | k1_relat_1('#skF_4')!='#skF_2'), inference(resolution, [status(thm)], [c_619, c_584])).
% 5.72/2.07  tff(c_643, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitLeft, [status(thm)], [c_623])).
% 5.72/2.07  tff(c_6, plain, (![A_2]: (k1_relat_1(k6_relat_1(A_2))=A_2)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.72/2.07  tff(c_80, plain, (![A_2]: (k1_relat_1(k6_partfun1(A_2))=A_2)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_6])).
% 5.72/2.07  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.72/2.07  tff(c_110, plain, (![A_52]: (k1_xboole_0=A_52 | ~v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.72/2.07  tff(c_114, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_110])).
% 5.72/2.07  tff(c_54, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_193])).
% 5.72/2.07  tff(c_120, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_114, c_54])).
% 5.72/2.07  tff(c_72, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_193])).
% 5.72/2.07  tff(c_50, plain, (![A_43, C_45, B_44]: (k6_partfun1(A_43)=k5_relat_1(C_45, k2_funct_1(C_45)) | k1_xboole_0=B_44 | ~v2_funct_1(C_45) | k2_relset_1(A_43, B_44, C_45)!=B_44 | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))) | ~v1_funct_2(C_45, A_43, B_44) | ~v1_funct_1(C_45))), inference(cnfTransformation, [status(thm)], [f_167])).
% 5.72/2.07  tff(c_715, plain, (![A_149, C_150, B_151]: (k6_partfun1(A_149)=k5_relat_1(C_150, k2_funct_1(C_150)) | B_151='#skF_1' | ~v2_funct_1(C_150) | k2_relset_1(A_149, B_151, C_150)!=B_151 | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_149, B_151))) | ~v1_funct_2(C_150, A_149, B_151) | ~v1_funct_1(C_150))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_50])).
% 5.72/2.07  tff(c_721, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | '#skF_3'='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_715])).
% 5.72/2.07  tff(c_731, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_62, c_58, c_721])).
% 5.72/2.07  tff(c_732, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_120, c_731])).
% 5.72/2.07  tff(c_16, plain, (![A_4]: (k1_relat_1(k5_relat_1(A_4, k2_funct_1(A_4)))=k1_relat_1(A_4) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.72/2.07  tff(c_736, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_732, c_16])).
% 5.72/2.07  tff(c_743, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_146, c_74, c_58, c_80, c_736])).
% 5.72/2.07  tff(c_745, plain, $false, inference(negUnitSimplification, [status(thm)], [c_643, c_743])).
% 5.72/2.07  tff(c_747, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_623])).
% 5.72/2.07  tff(c_52, plain, (k2_funct_1('#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_193])).
% 5.72/2.07  tff(c_145, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_133])).
% 5.72/2.07  tff(c_572, plain, (k2_funct_1('#skF_4')='#skF_5' | k5_relat_1('#skF_5', '#skF_4')!=k6_partfun1('#skF_3') | k2_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_145, c_566])).
% 5.72/2.07  tff(c_581, plain, (k2_funct_1('#skF_4')='#skF_5' | k5_relat_1('#skF_5', '#skF_4')!=k6_partfun1('#skF_3') | k2_relat_1('#skF_5')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_572])).
% 5.72/2.07  tff(c_582, plain, (k5_relat_1('#skF_5', '#skF_4')!=k6_partfun1('#skF_3') | k2_relat_1('#skF_5')!=k1_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_52, c_581])).
% 5.72/2.07  tff(c_585, plain, (k2_relat_1('#skF_5')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_582])).
% 5.72/2.07  tff(c_750, plain, (k2_relat_1('#skF_5')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_747, c_585])).
% 5.72/2.07  tff(c_66, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_193])).
% 5.72/2.07  tff(c_147, plain, (![A_58, B_59, D_60]: (r2_relset_1(A_58, B_59, D_60, D_60) | ~m1_subset_1(D_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.72/2.07  tff(c_154, plain, (![A_18]: (r2_relset_1(A_18, A_18, k6_partfun1(A_18), k6_partfun1(A_18)))), inference(resolution, [status(thm)], [c_75, c_147])).
% 5.72/2.07  tff(c_170, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_158])).
% 5.72/2.07  tff(c_1533, plain, (![A_207, B_208, C_209, D_210]: (k2_relset_1(A_207, B_208, C_209)=B_208 | ~r2_relset_1(B_208, B_208, k1_partfun1(B_208, A_207, A_207, B_208, D_210, C_209), k6_partfun1(B_208)) | ~m1_subset_1(D_210, k1_zfmisc_1(k2_zfmisc_1(B_208, A_207))) | ~v1_funct_2(D_210, B_208, A_207) | ~v1_funct_1(D_210) | ~m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))) | ~v1_funct_2(C_209, A_207, B_208) | ~v1_funct_1(C_209))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.72/2.07  tff(c_1539, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_546, c_1533])).
% 5.72/2.07  tff(c_1543, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_74, c_72, c_70, c_154, c_170, c_1539])).
% 5.72/2.07  tff(c_1545, plain, $false, inference(negUnitSimplification, [status(thm)], [c_750, c_1543])).
% 5.72/2.07  tff(c_1546, plain, (k5_relat_1('#skF_5', '#skF_4')!=k6_partfun1('#skF_3')), inference(splitRight, [status(thm)], [c_582])).
% 5.72/2.07  tff(c_2812, plain, (![E_339, B_338, F_337, D_334, C_336, A_335]: (k1_partfun1(A_335, B_338, C_336, D_334, E_339, F_337)=k5_relat_1(E_339, F_337) | ~m1_subset_1(F_337, k1_zfmisc_1(k2_zfmisc_1(C_336, D_334))) | ~v1_funct_1(F_337) | ~m1_subset_1(E_339, k1_zfmisc_1(k2_zfmisc_1(A_335, B_338))) | ~v1_funct_1(E_339))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.72/2.07  tff(c_2816, plain, (![A_335, B_338, E_339]: (k1_partfun1(A_335, B_338, '#skF_3', '#skF_2', E_339, '#skF_5')=k5_relat_1(E_339, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_339, k1_zfmisc_1(k2_zfmisc_1(A_335, B_338))) | ~v1_funct_1(E_339))), inference(resolution, [status(thm)], [c_64, c_2812])).
% 5.72/2.07  tff(c_2828, plain, (![A_341, B_342, E_343]: (k1_partfun1(A_341, B_342, '#skF_3', '#skF_2', E_343, '#skF_5')=k5_relat_1(E_343, '#skF_5') | ~m1_subset_1(E_343, k1_zfmisc_1(k2_zfmisc_1(A_341, B_342))) | ~v1_funct_1(E_343))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2816])).
% 5.72/2.07  tff(c_2837, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_2828])).
% 5.72/2.07  tff(c_2844, plain, (k5_relat_1('#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_546, c_2837])).
% 5.72/2.07  tff(c_1547, plain, (k2_relat_1('#skF_5')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_582])).
% 5.72/2.07  tff(c_76, plain, (![A_5, B_7]: (k2_funct_1(A_5)=B_7 | k6_partfun1(k2_relat_1(A_5))!=k5_relat_1(B_7, A_5) | k2_relat_1(B_7)!=k1_relat_1(A_5) | ~v2_funct_1(A_5) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_18])).
% 5.72/2.07  tff(c_1551, plain, (![B_7]: (k2_funct_1('#skF_5')=B_7 | k6_partfun1(k1_relat_1('#skF_4'))!=k5_relat_1(B_7, '#skF_5') | k2_relat_1(B_7)!=k1_relat_1('#skF_5') | ~v2_funct_1('#skF_5') | ~v1_funct_1(B_7) | ~v1_relat_1(B_7) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1547, c_76])).
% 5.72/2.07  tff(c_1555, plain, (![B_7]: (k2_funct_1('#skF_5')=B_7 | k6_partfun1(k1_relat_1('#skF_4'))!=k5_relat_1(B_7, '#skF_5') | k2_relat_1(B_7)!=k1_relat_1('#skF_5') | ~v2_funct_1('#skF_5') | ~v1_funct_1(B_7) | ~v1_relat_1(B_7))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_68, c_1551])).
% 5.72/2.07  tff(c_1563, plain, (~v2_funct_1('#skF_5')), inference(splitLeft, [status(thm)], [c_1555])).
% 5.72/2.07  tff(c_56, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_193])).
% 5.72/2.07  tff(c_121, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_114, c_56])).
% 5.72/2.07  tff(c_12, plain, (![A_3]: (v2_funct_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.72/2.07  tff(c_77, plain, (![A_3]: (v2_funct_1(k6_partfun1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_12])).
% 5.72/2.07  tff(c_42, plain, (![C_39, B_38, A_37, D_40, E_42]: (k1_xboole_0=C_39 | v2_funct_1(E_42) | k2_relset_1(A_37, B_38, D_40)!=B_38 | ~v2_funct_1(k1_partfun1(A_37, B_38, B_38, C_39, D_40, E_42)) | ~m1_subset_1(E_42, k1_zfmisc_1(k2_zfmisc_1(B_38, C_39))) | ~v1_funct_2(E_42, B_38, C_39) | ~v1_funct_1(E_42) | ~m1_subset_1(D_40, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))) | ~v1_funct_2(D_40, A_37, B_38) | ~v1_funct_1(D_40))), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.72/2.07  tff(c_2617, plain, (![C_301, D_299, B_298, E_300, A_297]: (C_301='#skF_1' | v2_funct_1(E_300) | k2_relset_1(A_297, B_298, D_299)!=B_298 | ~v2_funct_1(k1_partfun1(A_297, B_298, B_298, C_301, D_299, E_300)) | ~m1_subset_1(E_300, k1_zfmisc_1(k2_zfmisc_1(B_298, C_301))) | ~v1_funct_2(E_300, B_298, C_301) | ~v1_funct_1(E_300) | ~m1_subset_1(D_299, k1_zfmisc_1(k2_zfmisc_1(A_297, B_298))) | ~v1_funct_2(D_299, A_297, B_298) | ~v1_funct_1(D_299))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_42])).
% 5.72/2.07  tff(c_2625, plain, ('#skF_2'='#skF_1' | v2_funct_1('#skF_5') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_546, c_2617])).
% 5.72/2.07  tff(c_2636, plain, ('#skF_2'='#skF_1' | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_66, c_64, c_77, c_62, c_2625])).
% 5.72/2.07  tff(c_2638, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1563, c_121, c_2636])).
% 5.72/2.07  tff(c_2640, plain, (v2_funct_1('#skF_5')), inference(splitRight, [status(thm)], [c_1555])).
% 5.72/2.07  tff(c_2643, plain, (![A_308, C_305, B_307, E_306, D_310, F_309]: (v1_funct_1(k1_partfun1(A_308, B_307, C_305, D_310, E_306, F_309)) | ~m1_subset_1(F_309, k1_zfmisc_1(k2_zfmisc_1(C_305, D_310))) | ~v1_funct_1(F_309) | ~m1_subset_1(E_306, k1_zfmisc_1(k2_zfmisc_1(A_308, B_307))) | ~v1_funct_1(E_306))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.72/2.07  tff(c_2647, plain, (![A_308, B_307, E_306]: (v1_funct_1(k1_partfun1(A_308, B_307, '#skF_3', '#skF_2', E_306, '#skF_5')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_306, k1_zfmisc_1(k2_zfmisc_1(A_308, B_307))) | ~v1_funct_1(E_306))), inference(resolution, [status(thm)], [c_64, c_2643])).
% 5.72/2.07  tff(c_2657, plain, (![A_311, B_312, E_313]: (v1_funct_1(k1_partfun1(A_311, B_312, '#skF_3', '#skF_2', E_313, '#skF_5')) | ~m1_subset_1(E_313, k1_zfmisc_1(k2_zfmisc_1(A_311, B_312))) | ~v1_funct_1(E_313))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2647])).
% 5.72/2.07  tff(c_2666, plain, (v1_funct_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_2657])).
% 5.72/2.07  tff(c_2673, plain, (v1_funct_1(k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_546, c_2666])).
% 5.72/2.07  tff(c_2677, plain, (k6_partfun1('#skF_2')=k2_funct_1('#skF_4') | k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')!=k6_partfun1('#skF_3') | k1_relat_1('#skF_4')!='#skF_2'), inference(resolution, [status(thm)], [c_2673, c_584])).
% 5.72/2.07  tff(c_2679, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitLeft, [status(thm)], [c_2677])).
% 5.72/2.07  tff(c_2740, plain, (![A_328, C_329, B_330]: (k6_partfun1(A_328)=k5_relat_1(C_329, k2_funct_1(C_329)) | B_330='#skF_1' | ~v2_funct_1(C_329) | k2_relset_1(A_328, B_330, C_329)!=B_330 | ~m1_subset_1(C_329, k1_zfmisc_1(k2_zfmisc_1(A_328, B_330))) | ~v1_funct_2(C_329, A_328, B_330) | ~v1_funct_1(C_329))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_50])).
% 5.72/2.07  tff(c_2746, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | '#skF_3'='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_2740])).
% 5.72/2.07  tff(c_2756, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_62, c_58, c_2746])).
% 5.72/2.07  tff(c_2757, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_120, c_2756])).
% 5.72/2.07  tff(c_2761, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2757, c_16])).
% 5.72/2.07  tff(c_2768, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_146, c_74, c_58, c_80, c_2761])).
% 5.72/2.07  tff(c_2770, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2679, c_2768])).
% 5.72/2.07  tff(c_2772, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_2677])).
% 5.72/2.07  tff(c_1548, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1547, c_170])).
% 5.72/2.07  tff(c_2776, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2772, c_1548])).
% 5.72/2.07  tff(c_2868, plain, (![A_345, C_346, B_347]: (k6_partfun1(A_345)=k5_relat_1(C_346, k2_funct_1(C_346)) | B_347='#skF_1' | ~v2_funct_1(C_346) | k2_relset_1(A_345, B_347, C_346)!=B_347 | ~m1_subset_1(C_346, k1_zfmisc_1(k2_zfmisc_1(A_345, B_347))) | ~v1_funct_2(C_346, A_345, B_347) | ~v1_funct_1(C_346))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_50])).
% 5.72/2.07  tff(c_2872, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3') | '#skF_2'='#skF_1' | ~v2_funct_1('#skF_5') | k2_relset_1('#skF_3', '#skF_2', '#skF_5')!='#skF_2' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_2868])).
% 5.72/2.07  tff(c_2880, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3') | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_2776, c_2640, c_2872])).
% 5.72/2.07  tff(c_2881, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_121, c_2880])).
% 5.72/2.07  tff(c_2903, plain, (k1_relat_1(k6_partfun1('#skF_3'))=k1_relat_1('#skF_5') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2881, c_16])).
% 5.72/2.07  tff(c_2910, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_145, c_68, c_2640, c_80, c_2903])).
% 5.72/2.07  tff(c_2639, plain, (![B_7]: (k2_funct_1('#skF_5')=B_7 | k6_partfun1(k1_relat_1('#skF_4'))!=k5_relat_1(B_7, '#skF_5') | k2_relat_1(B_7)!=k1_relat_1('#skF_5') | ~v1_funct_1(B_7) | ~v1_relat_1(B_7))), inference(splitRight, [status(thm)], [c_1555])).
% 5.72/2.07  tff(c_2773, plain, (![B_7]: (k2_funct_1('#skF_5')=B_7 | k5_relat_1(B_7, '#skF_5')!=k6_partfun1('#skF_2') | k2_relat_1(B_7)!=k1_relat_1('#skF_5') | ~v1_funct_1(B_7) | ~v1_relat_1(B_7))), inference(demodulation, [status(thm), theory('equality')], [c_2772, c_2639])).
% 5.72/2.07  tff(c_3022, plain, (![B_357]: (k2_funct_1('#skF_5')=B_357 | k5_relat_1(B_357, '#skF_5')!=k6_partfun1('#skF_2') | k2_relat_1(B_357)!='#skF_3' | ~v1_funct_1(B_357) | ~v1_relat_1(B_357))), inference(demodulation, [status(thm), theory('equality')], [c_2910, c_2773])).
% 5.72/2.07  tff(c_3025, plain, (k2_funct_1('#skF_5')='#skF_4' | k5_relat_1('#skF_4', '#skF_5')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_3' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_146, c_3022])).
% 5.72/2.07  tff(c_3034, plain, (k2_funct_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_172, c_2844, c_3025])).
% 5.72/2.07  tff(c_3112, plain, (k5_relat_1('#skF_5', '#skF_4')=k6_partfun1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3034, c_2881])).
% 5.72/2.07  tff(c_3115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1546, c_3112])).
% 5.72/2.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.72/2.07  
% 5.72/2.07  Inference rules
% 5.72/2.07  ----------------------
% 5.72/2.07  #Ref     : 0
% 5.72/2.07  #Sup     : 648
% 5.72/2.07  #Fact    : 0
% 5.72/2.07  #Define  : 0
% 5.72/2.07  #Split   : 19
% 5.72/2.07  #Chain   : 0
% 5.72/2.07  #Close   : 0
% 5.72/2.07  
% 5.72/2.07  Ordering : KBO
% 5.72/2.07  
% 5.72/2.07  Simplification rules
% 5.72/2.07  ----------------------
% 5.72/2.07  #Subsume      : 29
% 5.72/2.07  #Demod        : 776
% 5.72/2.07  #Tautology    : 184
% 5.72/2.07  #SimpNegUnit  : 70
% 5.72/2.07  #BackRed      : 47
% 5.72/2.07  
% 5.72/2.07  #Partial instantiations: 0
% 5.72/2.07  #Strategies tried      : 1
% 5.72/2.07  
% 5.72/2.07  Timing (in seconds)
% 5.72/2.07  ----------------------
% 5.72/2.08  Preprocessing        : 0.37
% 5.72/2.08  Parsing              : 0.20
% 5.72/2.08  CNF conversion       : 0.03
% 5.72/2.08  Main loop            : 0.86
% 5.72/2.08  Inferencing          : 0.30
% 5.72/2.08  Reduction            : 0.31
% 5.72/2.08  Demodulation         : 0.23
% 5.72/2.08  BG Simplification    : 0.04
% 5.72/2.08  Subsumption          : 0.15
% 5.72/2.08  Abstraction          : 0.04
% 5.72/2.08  MUC search           : 0.00
% 5.72/2.08  Cooper               : 0.00
% 5.72/2.08  Total                : 1.28
% 5.72/2.08  Index Insertion      : 0.00
% 5.72/2.08  Index Deletion       : 0.00
% 5.72/2.08  Index Matching       : 0.00
% 5.72/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
