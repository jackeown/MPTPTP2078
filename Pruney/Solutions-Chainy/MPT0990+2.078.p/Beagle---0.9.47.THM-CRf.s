%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:07 EST 2020

% Result     : Theorem 40.20s
% Output     : CNFRefutation 40.37s
% Verified   : 
% Statistics : Number of formulae       :  194 (2082 expanded)
%              Number of leaves         :   45 ( 744 expanded)
%              Depth                    :   22
%              Number of atoms          :  484 (8716 expanded)
%              Number of equality atoms :  167 (3037 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_204,negated_conjecture,(
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

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_48,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_117,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_107,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_103,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_119,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_40,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_75,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_178,axiom,(
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

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_136,axiom,(
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

tff(f_58,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_162,axiom,(
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

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_130,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_141,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_130])).

tff(c_76,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_12,plain,(
    ! [A_6] :
      ( v1_relat_1(k2_funct_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_498,plain,(
    ! [A_119,F_118,D_121,C_116,E_120,B_117] :
      ( k1_partfun1(A_119,B_117,C_116,D_121,E_120,F_118) = k5_relat_1(E_120,F_118)
      | ~ m1_subset_1(F_118,k1_zfmisc_1(k2_zfmisc_1(C_116,D_121)))
      | ~ v1_funct_1(F_118)
      | ~ m1_subset_1(E_120,k1_zfmisc_1(k2_zfmisc_1(A_119,B_117)))
      | ~ v1_funct_1(E_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_504,plain,(
    ! [A_119,B_117,E_120] :
      ( k1_partfun1(A_119,B_117,'#skF_2','#skF_1',E_120,'#skF_4') = k5_relat_1(E_120,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_120,k1_zfmisc_1(k2_zfmisc_1(A_119,B_117)))
      | ~ v1_funct_1(E_120) ) ),
    inference(resolution,[status(thm)],[c_66,c_498])).

tff(c_571,plain,(
    ! [A_133,B_134,E_135] :
      ( k1_partfun1(A_133,B_134,'#skF_2','#skF_1',E_135,'#skF_4') = k5_relat_1(E_135,'#skF_4')
      | ~ m1_subset_1(E_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134)))
      | ~ v1_funct_1(E_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_504])).

tff(c_577,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_571])).

tff(c_584,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_577])).

tff(c_34,plain,(
    ! [A_29] : m1_subset_1(k6_partfun1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_62,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_286,plain,(
    ! [D_82,C_83,A_84,B_85] :
      ( D_82 = C_83
      | ~ r2_relset_1(A_84,B_85,C_83,D_82)
      | ~ m1_subset_1(D_82,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85)))
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_294,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_62,c_286])).

tff(c_309,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_294])).

tff(c_428,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_309])).

tff(c_589,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_584,c_428])).

tff(c_670,plain,(
    ! [A_144,B_142,D_143,E_141,F_140,C_139] :
      ( m1_subset_1(k1_partfun1(A_144,B_142,C_139,D_143,E_141,F_140),k1_zfmisc_1(k2_zfmisc_1(A_144,D_143)))
      | ~ m1_subset_1(F_140,k1_zfmisc_1(k2_zfmisc_1(C_139,D_143)))
      | ~ v1_funct_1(F_140)
      | ~ m1_subset_1(E_141,k1_zfmisc_1(k2_zfmisc_1(A_144,B_142)))
      | ~ v1_funct_1(E_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_706,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_584,c_670])).

tff(c_728,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_70,c_66,c_706])).

tff(c_730,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_589,c_728])).

tff(c_731,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_309])).

tff(c_774,plain,(
    ! [E_155,D_157,F_154,B_156,A_158,C_153] :
      ( v1_funct_1(k1_partfun1(A_158,B_156,C_153,D_157,E_155,F_154))
      | ~ m1_subset_1(F_154,k1_zfmisc_1(k2_zfmisc_1(C_153,D_157)))
      | ~ v1_funct_1(F_154)
      | ~ m1_subset_1(E_155,k1_zfmisc_1(k2_zfmisc_1(A_158,B_156)))
      | ~ v1_funct_1(E_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_780,plain,(
    ! [A_158,B_156,E_155] :
      ( v1_funct_1(k1_partfun1(A_158,B_156,'#skF_2','#skF_1',E_155,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_155,k1_zfmisc_1(k2_zfmisc_1(A_158,B_156)))
      | ~ v1_funct_1(E_155) ) ),
    inference(resolution,[status(thm)],[c_66,c_774])).

tff(c_805,plain,(
    ! [A_162,B_163,E_164] :
      ( v1_funct_1(k1_partfun1(A_162,B_163,'#skF_2','#skF_1',E_164,'#skF_4'))
      | ~ m1_subset_1(E_164,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163)))
      | ~ v1_funct_1(E_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_780])).

tff(c_811,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_805])).

tff(c_818,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_731,c_811])).

tff(c_38,plain,(
    ! [A_36] : k6_relat_1(A_36) = k6_partfun1(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_8,plain,(
    ! [A_5] : k2_relat_1(k6_relat_1(A_5)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_79,plain,(
    ! [A_5] : k2_relat_1(k6_partfun1(A_5)) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_8])).

tff(c_140,plain,(
    ! [A_29] : v1_relat_1(k6_partfun1(A_29)) ),
    inference(resolution,[status(thm)],[c_34,c_130])).

tff(c_60,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_64,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_155,plain,(
    ! [A_69,B_70,C_71] :
      ( k2_relset_1(A_69,B_70,C_71) = k2_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_161,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_155])).

tff(c_168,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_161])).

tff(c_18,plain,(
    ! [A_10,B_12] :
      ( k2_funct_1(A_10) = B_12
      | k6_relat_1(k2_relat_1(A_10)) != k5_relat_1(B_12,A_10)
      | k2_relat_1(B_12) != k1_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_387,plain,(
    ! [A_92,B_93] :
      ( k2_funct_1(A_92) = B_93
      | k6_partfun1(k2_relat_1(A_92)) != k5_relat_1(B_93,A_92)
      | k2_relat_1(B_93) != k1_relat_1(A_92)
      | ~ v2_funct_1(A_92)
      | ~ v1_funct_1(B_93)
      | ~ v1_relat_1(B_93)
      | ~ v1_funct_1(A_92)
      | ~ v1_relat_1(A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_18])).

tff(c_397,plain,(
    ! [B_93] :
      ( k2_funct_1('#skF_3') = B_93
      | k5_relat_1(B_93,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_93) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_93)
      | ~ v1_relat_1(B_93)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_387])).

tff(c_404,plain,(
    ! [B_94] :
      ( k2_funct_1('#skF_3') = B_94
      | k5_relat_1(B_94,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_94) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_94)
      | ~ v1_relat_1(B_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_76,c_60,c_397])).

tff(c_407,plain,(
    ! [A_29] :
      ( k6_partfun1(A_29) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_29),'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(k6_partfun1(A_29)) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(k6_partfun1(A_29)) ) ),
    inference(resolution,[status(thm)],[c_140,c_404])).

tff(c_418,plain,(
    ! [A_29] :
      ( k6_partfun1(A_29) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_29),'#skF_3') != k6_partfun1('#skF_2')
      | k1_relat_1('#skF_3') != A_29
      | ~ v1_funct_1(k6_partfun1(A_29)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_407])).

tff(c_825,plain,
    ( k6_partfun1('#skF_1') = k2_funct_1('#skF_3')
    | k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_818,c_418])).

tff(c_828,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_825])).

tff(c_4,plain,(
    ! [A_4] :
      ( k10_relat_1(A_4,k2_relat_1(A_4)) = k1_relat_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_173,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_4])).

tff(c_177,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_173])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_74,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_883,plain,(
    ! [A_177,C_178,B_179] :
      ( k6_partfun1(A_177) = k5_relat_1(C_178,k2_funct_1(C_178))
      | k1_xboole_0 = B_179
      | ~ v2_funct_1(C_178)
      | k2_relset_1(A_177,B_179,C_178) != B_179
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(A_177,B_179)))
      | ~ v1_funct_2(C_178,A_177,B_179)
      | ~ v1_funct_1(C_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_887,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_883])).

tff(c_895,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_64,c_60,c_887])).

tff(c_896,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_895])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( k9_relat_1(B_3,k2_relat_1(A_1)) = k2_relat_1(k5_relat_1(A_1,B_3))
      | ~ v1_relat_1(B_3)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_256,plain,(
    ! [B_79,A_80] :
      ( k9_relat_1(k2_funct_1(B_79),A_80) = k10_relat_1(B_79,A_80)
      | ~ v2_funct_1(B_79)
      | ~ v1_funct_1(B_79)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_270,plain,(
    ! [A_1,B_79] :
      ( k2_relat_1(k5_relat_1(A_1,k2_funct_1(B_79))) = k10_relat_1(B_79,k2_relat_1(A_1))
      | ~ v2_funct_1(B_79)
      | ~ v1_funct_1(B_79)
      | ~ v1_relat_1(B_79)
      | ~ v1_relat_1(k2_funct_1(B_79))
      | ~ v1_relat_1(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_256])).

tff(c_904,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k2_relat_1(k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_896,c_270])).

tff(c_917,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_141,c_76,c_60,c_79,c_177,c_168,c_904])).

tff(c_918,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_828,c_917])).

tff(c_927,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_918])).

tff(c_931,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_76,c_927])).

tff(c_933,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_825])).

tff(c_54,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_142,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_130])).

tff(c_410,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_142,c_404])).

tff(c_421,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_410])).

tff(c_422,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_421])).

tff(c_427,plain,(
    k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_422])).

tff(c_937,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_933,c_427])).

tff(c_68,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_144,plain,(
    ! [A_65,B_66,D_67] :
      ( r2_relset_1(A_65,B_66,D_67,D_67)
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_151,plain,(
    ! [A_29] : r2_relset_1(A_29,A_29,k6_partfun1(A_29),k6_partfun1(A_29)) ),
    inference(resolution,[status(thm)],[c_34,c_144])).

tff(c_169,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_155])).

tff(c_1760,plain,(
    ! [A_226,B_227,C_228,D_229] :
      ( k2_relset_1(A_226,B_227,C_228) = B_227
      | ~ r2_relset_1(B_227,B_227,k1_partfun1(B_227,A_226,A_226,B_227,D_229,C_228),k6_partfun1(B_227))
      | ~ m1_subset_1(D_229,k1_zfmisc_1(k2_zfmisc_1(B_227,A_226)))
      | ~ v1_funct_2(D_229,B_227,A_226)
      | ~ v1_funct_1(D_229)
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(A_226,B_227)))
      | ~ v1_funct_2(C_228,A_226,B_227)
      | ~ v1_funct_1(C_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1766,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_731,c_1760])).

tff(c_1770,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_76,c_74,c_72,c_151,c_169,c_1766])).

tff(c_1772,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_937,c_1770])).

tff(c_1773,plain,(
    k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_422])).

tff(c_1875,plain,(
    ! [B_247,D_251,C_246,F_248,E_250,A_249] :
      ( k1_partfun1(A_249,B_247,C_246,D_251,E_250,F_248) = k5_relat_1(E_250,F_248)
      | ~ m1_subset_1(F_248,k1_zfmisc_1(k2_zfmisc_1(C_246,D_251)))
      | ~ v1_funct_1(F_248)
      | ~ m1_subset_1(E_250,k1_zfmisc_1(k2_zfmisc_1(A_249,B_247)))
      | ~ v1_funct_1(E_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1881,plain,(
    ! [A_249,B_247,E_250] :
      ( k1_partfun1(A_249,B_247,'#skF_2','#skF_1',E_250,'#skF_4') = k5_relat_1(E_250,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_250,k1_zfmisc_1(k2_zfmisc_1(A_249,B_247)))
      | ~ v1_funct_1(E_250) ) ),
    inference(resolution,[status(thm)],[c_66,c_1875])).

tff(c_1917,plain,(
    ! [A_256,B_257,E_258] :
      ( k1_partfun1(A_256,B_257,'#skF_2','#skF_1',E_258,'#skF_4') = k5_relat_1(E_258,'#skF_4')
      | ~ m1_subset_1(E_258,k1_zfmisc_1(k2_zfmisc_1(A_256,B_257)))
      | ~ v1_funct_1(E_258) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1881])).

tff(c_1923,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_1917])).

tff(c_1930,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1923])).

tff(c_1798,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_309])).

tff(c_1935,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1930,c_1798])).

tff(c_2155,plain,(
    ! [A_274,D_273,C_269,E_271,F_270,B_272] :
      ( m1_subset_1(k1_partfun1(A_274,B_272,C_269,D_273,E_271,F_270),k1_zfmisc_1(k2_zfmisc_1(A_274,D_273)))
      | ~ m1_subset_1(F_270,k1_zfmisc_1(k2_zfmisc_1(C_269,D_273)))
      | ~ v1_funct_1(F_270)
      | ~ m1_subset_1(E_271,k1_zfmisc_1(k2_zfmisc_1(A_274,B_272)))
      | ~ v1_funct_1(E_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2189,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1930,c_2155])).

tff(c_2210,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_70,c_66,c_2189])).

tff(c_2212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1935,c_2210])).

tff(c_2213,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_309])).

tff(c_2568,plain,(
    ! [C_312,A_315,D_317,F_314,E_316,B_313] :
      ( k1_partfun1(A_315,B_313,C_312,D_317,E_316,F_314) = k5_relat_1(E_316,F_314)
      | ~ m1_subset_1(F_314,k1_zfmisc_1(k2_zfmisc_1(C_312,D_317)))
      | ~ v1_funct_1(F_314)
      | ~ m1_subset_1(E_316,k1_zfmisc_1(k2_zfmisc_1(A_315,B_313)))
      | ~ v1_funct_1(E_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2574,plain,(
    ! [A_315,B_313,E_316] :
      ( k1_partfun1(A_315,B_313,'#skF_2','#skF_1',E_316,'#skF_4') = k5_relat_1(E_316,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_316,k1_zfmisc_1(k2_zfmisc_1(A_315,B_313)))
      | ~ v1_funct_1(E_316) ) ),
    inference(resolution,[status(thm)],[c_66,c_2568])).

tff(c_3464,plain,(
    ! [A_363,B_364,E_365] :
      ( k1_partfun1(A_363,B_364,'#skF_2','#skF_1',E_365,'#skF_4') = k5_relat_1(E_365,'#skF_4')
      | ~ m1_subset_1(E_365,k1_zfmisc_1(k2_zfmisc_1(A_363,B_364)))
      | ~ v1_funct_1(E_365) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2574])).

tff(c_3470,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_3464])).

tff(c_3477,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2213,c_3470])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_2276,plain,(
    ! [B_281,A_283,C_278,F_279,D_282,E_280] :
      ( v1_funct_1(k1_partfun1(A_283,B_281,C_278,D_282,E_280,F_279))
      | ~ m1_subset_1(F_279,k1_zfmisc_1(k2_zfmisc_1(C_278,D_282)))
      | ~ v1_funct_1(F_279)
      | ~ m1_subset_1(E_280,k1_zfmisc_1(k2_zfmisc_1(A_283,B_281)))
      | ~ v1_funct_1(E_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2282,plain,(
    ! [A_283,B_281,E_280] :
      ( v1_funct_1(k1_partfun1(A_283,B_281,'#skF_2','#skF_1',E_280,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_280,k1_zfmisc_1(k2_zfmisc_1(A_283,B_281)))
      | ~ v1_funct_1(E_280) ) ),
    inference(resolution,[status(thm)],[c_66,c_2276])).

tff(c_2307,plain,(
    ! [A_287,B_288,E_289] :
      ( v1_funct_1(k1_partfun1(A_287,B_288,'#skF_2','#skF_1',E_289,'#skF_4'))
      | ~ m1_subset_1(E_289,k1_zfmisc_1(k2_zfmisc_1(A_287,B_288)))
      | ~ v1_funct_1(E_289) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2282])).

tff(c_2313,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_2307])).

tff(c_2320,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2213,c_2313])).

tff(c_2327,plain,
    ( k6_partfun1('#skF_1') = k2_funct_1('#skF_3')
    | k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_2320,c_418])).

tff(c_2330,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2327])).

tff(c_2473,plain,(
    ! [A_309,C_310,B_311] :
      ( k6_partfun1(A_309) = k5_relat_1(C_310,k2_funct_1(C_310))
      | k1_xboole_0 = B_311
      | ~ v2_funct_1(C_310)
      | k2_relset_1(A_309,B_311,C_310) != B_311
      | ~ m1_subset_1(C_310,k1_zfmisc_1(k2_zfmisc_1(A_309,B_311)))
      | ~ v1_funct_2(C_310,A_309,B_311)
      | ~ v1_funct_1(C_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_2477,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_2473])).

tff(c_2485,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_64,c_60,c_2477])).

tff(c_2486,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2485])).

tff(c_2494,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k2_relat_1(k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2486,c_270])).

tff(c_2507,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_141,c_76,c_60,c_79,c_177,c_168,c_2494])).

tff(c_2508,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_2330,c_2507])).

tff(c_2517,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_2508])).

tff(c_2521,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_76,c_2517])).

tff(c_2523,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2327])).

tff(c_1774,plain,(
    k2_relat_1('#skF_4') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_422])).

tff(c_1775,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1774,c_169])).

tff(c_2529,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2523,c_1775])).

tff(c_2639,plain,(
    ! [A_322,C_323,B_324] :
      ( k6_partfun1(A_322) = k5_relat_1(C_323,k2_funct_1(C_323))
      | k1_xboole_0 = B_324
      | ~ v2_funct_1(C_323)
      | k2_relset_1(A_322,B_324,C_323) != B_324
      | ~ m1_subset_1(C_323,k1_zfmisc_1(k2_zfmisc_1(A_322,B_324)))
      | ~ v1_funct_2(C_323,A_322,B_324)
      | ~ v1_funct_1(C_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_2645,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_2639])).

tff(c_2655,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_2529,c_2645])).

tff(c_2656,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2655])).

tff(c_2690,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2656])).

tff(c_16,plain,(
    ! [A_9] : v2_funct_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_78,plain,(
    ! [A_9] : v2_funct_1(k6_partfun1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_16])).

tff(c_3327,plain,(
    ! [B_356,A_357,D_355,C_359,E_358] :
      ( k1_xboole_0 = C_359
      | v2_funct_1(E_358)
      | k2_relset_1(A_357,B_356,D_355) != B_356
      | ~ v2_funct_1(k1_partfun1(A_357,B_356,B_356,C_359,D_355,E_358))
      | ~ m1_subset_1(E_358,k1_zfmisc_1(k2_zfmisc_1(B_356,C_359)))
      | ~ v1_funct_2(E_358,B_356,C_359)
      | ~ v1_funct_1(E_358)
      | ~ m1_subset_1(D_355,k1_zfmisc_1(k2_zfmisc_1(A_357,B_356)))
      | ~ v1_funct_2(D_355,A_357,B_356)
      | ~ v1_funct_1(D_355) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_3335,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_2213,c_3327])).

tff(c_3346,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_68,c_66,c_78,c_64,c_3335])).

tff(c_3348,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2690,c_58,c_3346])).

tff(c_3350,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2656])).

tff(c_1784,plain,
    ( k10_relat_1('#skF_4',k1_relat_1('#skF_3')) = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1774,c_4])).

tff(c_1792,plain,(
    k10_relat_1('#skF_4',k1_relat_1('#skF_3')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_1784])).

tff(c_2528,plain,(
    k10_relat_1('#skF_4','#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2523,c_1792])).

tff(c_2530,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2523,c_1774])).

tff(c_3349,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2656])).

tff(c_3381,plain,
    ( k10_relat_1('#skF_4',k2_relat_1('#skF_4')) = k2_relat_1(k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3349,c_270])).

tff(c_3386,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_142,c_70,c_3350,c_79,c_2528,c_2530,c_3381])).

tff(c_3388,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3386])).

tff(c_3391,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_3388])).

tff(c_3395,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_70,c_3391])).

tff(c_3396,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3386])).

tff(c_77,plain,(
    ! [A_10,B_12] :
      ( k2_funct_1(A_10) = B_12
      | k6_partfun1(k2_relat_1(A_10)) != k5_relat_1(B_12,A_10)
      | k2_relat_1(B_12) != k1_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_18])).

tff(c_2539,plain,(
    ! [B_12] :
      ( k2_funct_1('#skF_4') = B_12
      | k5_relat_1(B_12,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_12) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2530,c_77])).

tff(c_2549,plain,(
    ! [B_12] :
      ( k2_funct_1('#skF_4') = B_12
      | k5_relat_1(B_12,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_12) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_70,c_2539])).

tff(c_48460,plain,(
    ! [B_1232] :
      ( k2_funct_1('#skF_4') = B_1232
      | k5_relat_1(B_1232,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_1232) != '#skF_2'
      | ~ v1_funct_1(B_1232)
      | ~ v1_relat_1(B_1232) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3350,c_3396,c_2549])).

tff(c_49234,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_141,c_48460])).

tff(c_49865,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_168,c_3477,c_49234])).

tff(c_49873,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49865,c_3349])).

tff(c_49878,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1773,c_49873])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:48:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 40.20/29.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 40.20/29.84  
% 40.20/29.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 40.20/29.84  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 40.20/29.84  
% 40.20/29.84  %Foreground sorts:
% 40.20/29.84  
% 40.20/29.84  
% 40.20/29.84  %Background operators:
% 40.20/29.84  
% 40.20/29.84  
% 40.20/29.84  %Foreground operators:
% 40.20/29.84  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 40.20/29.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 40.20/29.84  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 40.20/29.84  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 40.20/29.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 40.20/29.84  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 40.20/29.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 40.20/29.84  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 40.20/29.84  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 40.20/29.84  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 40.20/29.84  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 40.20/29.84  tff('#skF_2', type, '#skF_2': $i).
% 40.20/29.84  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 40.20/29.84  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 40.20/29.84  tff('#skF_3', type, '#skF_3': $i).
% 40.20/29.84  tff('#skF_1', type, '#skF_1': $i).
% 40.20/29.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 40.20/29.84  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 40.20/29.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 40.20/29.84  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 40.20/29.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 40.20/29.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 40.20/29.84  tff('#skF_4', type, '#skF_4': $i).
% 40.20/29.84  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 40.20/29.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 40.20/29.84  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 40.20/29.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 40.20/29.84  
% 40.37/29.87  tff(f_204, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 40.37/29.87  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 40.37/29.87  tff(f_48, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 40.37/29.87  tff(f_117, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 40.37/29.87  tff(f_107, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 40.37/29.87  tff(f_91, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 40.37/29.87  tff(f_103, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 40.37/29.87  tff(f_119, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 40.37/29.87  tff(f_40, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 40.37/29.87  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 40.37/29.87  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 40.37/29.87  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 40.37/29.87  tff(f_178, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 40.37/29.87  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 40.37/29.87  tff(f_56, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 40.37/29.87  tff(f_136, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 40.37/29.87  tff(f_58, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 40.37/29.87  tff(f_162, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 40.37/29.87  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_204])).
% 40.37/29.87  tff(c_130, plain, (![C_61, A_62, B_63]: (v1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 40.37/29.87  tff(c_141, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_130])).
% 40.37/29.87  tff(c_76, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_204])).
% 40.37/29.87  tff(c_12, plain, (![A_6]: (v1_relat_1(k2_funct_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 40.37/29.87  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_204])).
% 40.37/29.87  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_204])).
% 40.37/29.87  tff(c_498, plain, (![A_119, F_118, D_121, C_116, E_120, B_117]: (k1_partfun1(A_119, B_117, C_116, D_121, E_120, F_118)=k5_relat_1(E_120, F_118) | ~m1_subset_1(F_118, k1_zfmisc_1(k2_zfmisc_1(C_116, D_121))) | ~v1_funct_1(F_118) | ~m1_subset_1(E_120, k1_zfmisc_1(k2_zfmisc_1(A_119, B_117))) | ~v1_funct_1(E_120))), inference(cnfTransformation, [status(thm)], [f_117])).
% 40.37/29.87  tff(c_504, plain, (![A_119, B_117, E_120]: (k1_partfun1(A_119, B_117, '#skF_2', '#skF_1', E_120, '#skF_4')=k5_relat_1(E_120, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_120, k1_zfmisc_1(k2_zfmisc_1(A_119, B_117))) | ~v1_funct_1(E_120))), inference(resolution, [status(thm)], [c_66, c_498])).
% 40.37/29.87  tff(c_571, plain, (![A_133, B_134, E_135]: (k1_partfun1(A_133, B_134, '#skF_2', '#skF_1', E_135, '#skF_4')=k5_relat_1(E_135, '#skF_4') | ~m1_subset_1(E_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))) | ~v1_funct_1(E_135))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_504])).
% 40.37/29.87  tff(c_577, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_571])).
% 40.37/29.87  tff(c_584, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_577])).
% 40.37/29.87  tff(c_34, plain, (![A_29]: (m1_subset_1(k6_partfun1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 40.37/29.87  tff(c_62, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_204])).
% 40.37/29.87  tff(c_286, plain, (![D_82, C_83, A_84, B_85]: (D_82=C_83 | ~r2_relset_1(A_84, B_85, C_83, D_82) | ~m1_subset_1(D_82, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 40.37/29.87  tff(c_294, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_62, c_286])).
% 40.37/29.87  tff(c_309, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_294])).
% 40.37/29.87  tff(c_428, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_309])).
% 40.37/29.87  tff(c_589, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_584, c_428])).
% 40.37/29.87  tff(c_670, plain, (![A_144, B_142, D_143, E_141, F_140, C_139]: (m1_subset_1(k1_partfun1(A_144, B_142, C_139, D_143, E_141, F_140), k1_zfmisc_1(k2_zfmisc_1(A_144, D_143))) | ~m1_subset_1(F_140, k1_zfmisc_1(k2_zfmisc_1(C_139, D_143))) | ~v1_funct_1(F_140) | ~m1_subset_1(E_141, k1_zfmisc_1(k2_zfmisc_1(A_144, B_142))) | ~v1_funct_1(E_141))), inference(cnfTransformation, [status(thm)], [f_103])).
% 40.37/29.87  tff(c_706, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_584, c_670])).
% 40.37/29.87  tff(c_728, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_70, c_66, c_706])).
% 40.37/29.87  tff(c_730, plain, $false, inference(negUnitSimplification, [status(thm)], [c_589, c_728])).
% 40.37/29.87  tff(c_731, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_309])).
% 40.37/29.87  tff(c_774, plain, (![E_155, D_157, F_154, B_156, A_158, C_153]: (v1_funct_1(k1_partfun1(A_158, B_156, C_153, D_157, E_155, F_154)) | ~m1_subset_1(F_154, k1_zfmisc_1(k2_zfmisc_1(C_153, D_157))) | ~v1_funct_1(F_154) | ~m1_subset_1(E_155, k1_zfmisc_1(k2_zfmisc_1(A_158, B_156))) | ~v1_funct_1(E_155))), inference(cnfTransformation, [status(thm)], [f_103])).
% 40.37/29.87  tff(c_780, plain, (![A_158, B_156, E_155]: (v1_funct_1(k1_partfun1(A_158, B_156, '#skF_2', '#skF_1', E_155, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_155, k1_zfmisc_1(k2_zfmisc_1(A_158, B_156))) | ~v1_funct_1(E_155))), inference(resolution, [status(thm)], [c_66, c_774])).
% 40.37/29.87  tff(c_805, plain, (![A_162, B_163, E_164]: (v1_funct_1(k1_partfun1(A_162, B_163, '#skF_2', '#skF_1', E_164, '#skF_4')) | ~m1_subset_1(E_164, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))) | ~v1_funct_1(E_164))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_780])).
% 40.37/29.87  tff(c_811, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_805])).
% 40.37/29.87  tff(c_818, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_731, c_811])).
% 40.37/29.87  tff(c_38, plain, (![A_36]: (k6_relat_1(A_36)=k6_partfun1(A_36))), inference(cnfTransformation, [status(thm)], [f_119])).
% 40.37/29.87  tff(c_8, plain, (![A_5]: (k2_relat_1(k6_relat_1(A_5))=A_5)), inference(cnfTransformation, [status(thm)], [f_40])).
% 40.37/29.87  tff(c_79, plain, (![A_5]: (k2_relat_1(k6_partfun1(A_5))=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_8])).
% 40.37/29.87  tff(c_140, plain, (![A_29]: (v1_relat_1(k6_partfun1(A_29)))), inference(resolution, [status(thm)], [c_34, c_130])).
% 40.37/29.87  tff(c_60, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_204])).
% 40.37/29.87  tff(c_64, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_204])).
% 40.37/29.87  tff(c_155, plain, (![A_69, B_70, C_71]: (k2_relset_1(A_69, B_70, C_71)=k2_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 40.37/29.87  tff(c_161, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_155])).
% 40.37/29.87  tff(c_168, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_161])).
% 40.37/29.87  tff(c_18, plain, (![A_10, B_12]: (k2_funct_1(A_10)=B_12 | k6_relat_1(k2_relat_1(A_10))!=k5_relat_1(B_12, A_10) | k2_relat_1(B_12)!=k1_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_75])).
% 40.37/29.87  tff(c_387, plain, (![A_92, B_93]: (k2_funct_1(A_92)=B_93 | k6_partfun1(k2_relat_1(A_92))!=k5_relat_1(B_93, A_92) | k2_relat_1(B_93)!=k1_relat_1(A_92) | ~v2_funct_1(A_92) | ~v1_funct_1(B_93) | ~v1_relat_1(B_93) | ~v1_funct_1(A_92) | ~v1_relat_1(A_92))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_18])).
% 40.37/29.87  tff(c_397, plain, (![B_93]: (k2_funct_1('#skF_3')=B_93 | k5_relat_1(B_93, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_93)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_93) | ~v1_relat_1(B_93) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_168, c_387])).
% 40.37/29.87  tff(c_404, plain, (![B_94]: (k2_funct_1('#skF_3')=B_94 | k5_relat_1(B_94, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_94)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_94) | ~v1_relat_1(B_94))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_76, c_60, c_397])).
% 40.37/29.87  tff(c_407, plain, (![A_29]: (k6_partfun1(A_29)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_29), '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(k6_partfun1(A_29))!=k1_relat_1('#skF_3') | ~v1_funct_1(k6_partfun1(A_29)))), inference(resolution, [status(thm)], [c_140, c_404])).
% 40.37/29.87  tff(c_418, plain, (![A_29]: (k6_partfun1(A_29)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_29), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!=A_29 | ~v1_funct_1(k6_partfun1(A_29)))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_407])).
% 40.37/29.87  tff(c_825, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_818, c_418])).
% 40.37/29.87  tff(c_828, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_825])).
% 40.37/29.87  tff(c_4, plain, (![A_4]: (k10_relat_1(A_4, k2_relat_1(A_4))=k1_relat_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 40.37/29.87  tff(c_173, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_168, c_4])).
% 40.37/29.87  tff(c_177, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_173])).
% 40.37/29.87  tff(c_56, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_204])).
% 40.37/29.87  tff(c_74, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_204])).
% 40.37/29.87  tff(c_883, plain, (![A_177, C_178, B_179]: (k6_partfun1(A_177)=k5_relat_1(C_178, k2_funct_1(C_178)) | k1_xboole_0=B_179 | ~v2_funct_1(C_178) | k2_relset_1(A_177, B_179, C_178)!=B_179 | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(A_177, B_179))) | ~v1_funct_2(C_178, A_177, B_179) | ~v1_funct_1(C_178))), inference(cnfTransformation, [status(thm)], [f_178])).
% 40.37/29.87  tff(c_887, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_883])).
% 40.37/29.87  tff(c_895, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_64, c_60, c_887])).
% 40.37/29.87  tff(c_896, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_56, c_895])).
% 40.37/29.87  tff(c_2, plain, (![B_3, A_1]: (k9_relat_1(B_3, k2_relat_1(A_1))=k2_relat_1(k5_relat_1(A_1, B_3)) | ~v1_relat_1(B_3) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 40.37/29.87  tff(c_256, plain, (![B_79, A_80]: (k9_relat_1(k2_funct_1(B_79), A_80)=k10_relat_1(B_79, A_80) | ~v2_funct_1(B_79) | ~v1_funct_1(B_79) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_56])).
% 40.37/29.87  tff(c_270, plain, (![A_1, B_79]: (k2_relat_1(k5_relat_1(A_1, k2_funct_1(B_79)))=k10_relat_1(B_79, k2_relat_1(A_1)) | ~v2_funct_1(B_79) | ~v1_funct_1(B_79) | ~v1_relat_1(B_79) | ~v1_relat_1(k2_funct_1(B_79)) | ~v1_relat_1(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_256])).
% 40.37/29.87  tff(c_904, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k2_relat_1(k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_896, c_270])).
% 40.37/29.87  tff(c_917, plain, (k1_relat_1('#skF_3')='#skF_1' | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_141, c_76, c_60, c_79, c_177, c_168, c_904])).
% 40.37/29.87  tff(c_918, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_828, c_917])).
% 40.37/29.87  tff(c_927, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_918])).
% 40.37/29.87  tff(c_931, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141, c_76, c_927])).
% 40.37/29.87  tff(c_933, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_825])).
% 40.37/29.87  tff(c_54, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_204])).
% 40.37/29.87  tff(c_142, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_130])).
% 40.37/29.87  tff(c_410, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_142, c_404])).
% 40.37/29.87  tff(c_421, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_410])).
% 40.37/29.87  tff(c_422, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_421])).
% 40.37/29.87  tff(c_427, plain, (k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_422])).
% 40.37/29.87  tff(c_937, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_933, c_427])).
% 40.37/29.87  tff(c_68, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 40.37/29.87  tff(c_144, plain, (![A_65, B_66, D_67]: (r2_relset_1(A_65, B_66, D_67, D_67) | ~m1_subset_1(D_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 40.37/29.87  tff(c_151, plain, (![A_29]: (r2_relset_1(A_29, A_29, k6_partfun1(A_29), k6_partfun1(A_29)))), inference(resolution, [status(thm)], [c_34, c_144])).
% 40.37/29.87  tff(c_169, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_155])).
% 40.37/29.87  tff(c_1760, plain, (![A_226, B_227, C_228, D_229]: (k2_relset_1(A_226, B_227, C_228)=B_227 | ~r2_relset_1(B_227, B_227, k1_partfun1(B_227, A_226, A_226, B_227, D_229, C_228), k6_partfun1(B_227)) | ~m1_subset_1(D_229, k1_zfmisc_1(k2_zfmisc_1(B_227, A_226))) | ~v1_funct_2(D_229, B_227, A_226) | ~v1_funct_1(D_229) | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(A_226, B_227))) | ~v1_funct_2(C_228, A_226, B_227) | ~v1_funct_1(C_228))), inference(cnfTransformation, [status(thm)], [f_136])).
% 40.37/29.87  tff(c_1766, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_731, c_1760])).
% 40.37/29.87  tff(c_1770, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_76, c_74, c_72, c_151, c_169, c_1766])).
% 40.37/29.87  tff(c_1772, plain, $false, inference(negUnitSimplification, [status(thm)], [c_937, c_1770])).
% 40.37/29.87  tff(c_1773, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_422])).
% 40.37/29.87  tff(c_1875, plain, (![B_247, D_251, C_246, F_248, E_250, A_249]: (k1_partfun1(A_249, B_247, C_246, D_251, E_250, F_248)=k5_relat_1(E_250, F_248) | ~m1_subset_1(F_248, k1_zfmisc_1(k2_zfmisc_1(C_246, D_251))) | ~v1_funct_1(F_248) | ~m1_subset_1(E_250, k1_zfmisc_1(k2_zfmisc_1(A_249, B_247))) | ~v1_funct_1(E_250))), inference(cnfTransformation, [status(thm)], [f_117])).
% 40.37/29.87  tff(c_1881, plain, (![A_249, B_247, E_250]: (k1_partfun1(A_249, B_247, '#skF_2', '#skF_1', E_250, '#skF_4')=k5_relat_1(E_250, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_250, k1_zfmisc_1(k2_zfmisc_1(A_249, B_247))) | ~v1_funct_1(E_250))), inference(resolution, [status(thm)], [c_66, c_1875])).
% 40.37/29.87  tff(c_1917, plain, (![A_256, B_257, E_258]: (k1_partfun1(A_256, B_257, '#skF_2', '#skF_1', E_258, '#skF_4')=k5_relat_1(E_258, '#skF_4') | ~m1_subset_1(E_258, k1_zfmisc_1(k2_zfmisc_1(A_256, B_257))) | ~v1_funct_1(E_258))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1881])).
% 40.37/29.87  tff(c_1923, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_1917])).
% 40.37/29.87  tff(c_1930, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1923])).
% 40.37/29.87  tff(c_1798, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_309])).
% 40.37/29.87  tff(c_1935, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1930, c_1798])).
% 40.37/29.87  tff(c_2155, plain, (![A_274, D_273, C_269, E_271, F_270, B_272]: (m1_subset_1(k1_partfun1(A_274, B_272, C_269, D_273, E_271, F_270), k1_zfmisc_1(k2_zfmisc_1(A_274, D_273))) | ~m1_subset_1(F_270, k1_zfmisc_1(k2_zfmisc_1(C_269, D_273))) | ~v1_funct_1(F_270) | ~m1_subset_1(E_271, k1_zfmisc_1(k2_zfmisc_1(A_274, B_272))) | ~v1_funct_1(E_271))), inference(cnfTransformation, [status(thm)], [f_103])).
% 40.37/29.87  tff(c_2189, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1930, c_2155])).
% 40.37/29.87  tff(c_2210, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_70, c_66, c_2189])).
% 40.37/29.87  tff(c_2212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1935, c_2210])).
% 40.37/29.87  tff(c_2213, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_309])).
% 40.37/29.87  tff(c_2568, plain, (![C_312, A_315, D_317, F_314, E_316, B_313]: (k1_partfun1(A_315, B_313, C_312, D_317, E_316, F_314)=k5_relat_1(E_316, F_314) | ~m1_subset_1(F_314, k1_zfmisc_1(k2_zfmisc_1(C_312, D_317))) | ~v1_funct_1(F_314) | ~m1_subset_1(E_316, k1_zfmisc_1(k2_zfmisc_1(A_315, B_313))) | ~v1_funct_1(E_316))), inference(cnfTransformation, [status(thm)], [f_117])).
% 40.37/29.87  tff(c_2574, plain, (![A_315, B_313, E_316]: (k1_partfun1(A_315, B_313, '#skF_2', '#skF_1', E_316, '#skF_4')=k5_relat_1(E_316, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_316, k1_zfmisc_1(k2_zfmisc_1(A_315, B_313))) | ~v1_funct_1(E_316))), inference(resolution, [status(thm)], [c_66, c_2568])).
% 40.37/29.87  tff(c_3464, plain, (![A_363, B_364, E_365]: (k1_partfun1(A_363, B_364, '#skF_2', '#skF_1', E_365, '#skF_4')=k5_relat_1(E_365, '#skF_4') | ~m1_subset_1(E_365, k1_zfmisc_1(k2_zfmisc_1(A_363, B_364))) | ~v1_funct_1(E_365))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2574])).
% 40.37/29.87  tff(c_3470, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_3464])).
% 40.37/29.87  tff(c_3477, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2213, c_3470])).
% 40.37/29.87  tff(c_58, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_204])).
% 40.37/29.87  tff(c_2276, plain, (![B_281, A_283, C_278, F_279, D_282, E_280]: (v1_funct_1(k1_partfun1(A_283, B_281, C_278, D_282, E_280, F_279)) | ~m1_subset_1(F_279, k1_zfmisc_1(k2_zfmisc_1(C_278, D_282))) | ~v1_funct_1(F_279) | ~m1_subset_1(E_280, k1_zfmisc_1(k2_zfmisc_1(A_283, B_281))) | ~v1_funct_1(E_280))), inference(cnfTransformation, [status(thm)], [f_103])).
% 40.37/29.87  tff(c_2282, plain, (![A_283, B_281, E_280]: (v1_funct_1(k1_partfun1(A_283, B_281, '#skF_2', '#skF_1', E_280, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_280, k1_zfmisc_1(k2_zfmisc_1(A_283, B_281))) | ~v1_funct_1(E_280))), inference(resolution, [status(thm)], [c_66, c_2276])).
% 40.37/29.87  tff(c_2307, plain, (![A_287, B_288, E_289]: (v1_funct_1(k1_partfun1(A_287, B_288, '#skF_2', '#skF_1', E_289, '#skF_4')) | ~m1_subset_1(E_289, k1_zfmisc_1(k2_zfmisc_1(A_287, B_288))) | ~v1_funct_1(E_289))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2282])).
% 40.37/29.87  tff(c_2313, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_2307])).
% 40.37/29.87  tff(c_2320, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2213, c_2313])).
% 40.37/29.87  tff(c_2327, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_2320, c_418])).
% 40.37/29.87  tff(c_2330, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2327])).
% 40.37/29.87  tff(c_2473, plain, (![A_309, C_310, B_311]: (k6_partfun1(A_309)=k5_relat_1(C_310, k2_funct_1(C_310)) | k1_xboole_0=B_311 | ~v2_funct_1(C_310) | k2_relset_1(A_309, B_311, C_310)!=B_311 | ~m1_subset_1(C_310, k1_zfmisc_1(k2_zfmisc_1(A_309, B_311))) | ~v1_funct_2(C_310, A_309, B_311) | ~v1_funct_1(C_310))), inference(cnfTransformation, [status(thm)], [f_178])).
% 40.37/29.87  tff(c_2477, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_2473])).
% 40.37/29.87  tff(c_2485, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_64, c_60, c_2477])).
% 40.37/29.87  tff(c_2486, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_56, c_2485])).
% 40.37/29.87  tff(c_2494, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k2_relat_1(k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2486, c_270])).
% 40.37/29.87  tff(c_2507, plain, (k1_relat_1('#skF_3')='#skF_1' | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_141, c_76, c_60, c_79, c_177, c_168, c_2494])).
% 40.37/29.87  tff(c_2508, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_2330, c_2507])).
% 40.37/29.87  tff(c_2517, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_2508])).
% 40.37/29.87  tff(c_2521, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141, c_76, c_2517])).
% 40.37/29.87  tff(c_2523, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_2327])).
% 40.37/29.87  tff(c_1774, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_422])).
% 40.37/29.87  tff(c_1775, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1774, c_169])).
% 40.37/29.87  tff(c_2529, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2523, c_1775])).
% 40.37/29.87  tff(c_2639, plain, (![A_322, C_323, B_324]: (k6_partfun1(A_322)=k5_relat_1(C_323, k2_funct_1(C_323)) | k1_xboole_0=B_324 | ~v2_funct_1(C_323) | k2_relset_1(A_322, B_324, C_323)!=B_324 | ~m1_subset_1(C_323, k1_zfmisc_1(k2_zfmisc_1(A_322, B_324))) | ~v1_funct_2(C_323, A_322, B_324) | ~v1_funct_1(C_323))), inference(cnfTransformation, [status(thm)], [f_178])).
% 40.37/29.87  tff(c_2645, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_2639])).
% 40.37/29.87  tff(c_2655, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_2529, c_2645])).
% 40.37/29.87  tff(c_2656, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_58, c_2655])).
% 40.37/29.87  tff(c_2690, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_2656])).
% 40.37/29.87  tff(c_16, plain, (![A_9]: (v2_funct_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 40.37/29.87  tff(c_78, plain, (![A_9]: (v2_funct_1(k6_partfun1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_16])).
% 40.37/29.87  tff(c_3327, plain, (![B_356, A_357, D_355, C_359, E_358]: (k1_xboole_0=C_359 | v2_funct_1(E_358) | k2_relset_1(A_357, B_356, D_355)!=B_356 | ~v2_funct_1(k1_partfun1(A_357, B_356, B_356, C_359, D_355, E_358)) | ~m1_subset_1(E_358, k1_zfmisc_1(k2_zfmisc_1(B_356, C_359))) | ~v1_funct_2(E_358, B_356, C_359) | ~v1_funct_1(E_358) | ~m1_subset_1(D_355, k1_zfmisc_1(k2_zfmisc_1(A_357, B_356))) | ~v1_funct_2(D_355, A_357, B_356) | ~v1_funct_1(D_355))), inference(cnfTransformation, [status(thm)], [f_162])).
% 40.37/29.87  tff(c_3335, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2213, c_3327])).
% 40.37/29.87  tff(c_3346, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_70, c_68, c_66, c_78, c_64, c_3335])).
% 40.37/29.87  tff(c_3348, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2690, c_58, c_3346])).
% 40.37/29.87  tff(c_3350, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_2656])).
% 40.37/29.87  tff(c_1784, plain, (k10_relat_1('#skF_4', k1_relat_1('#skF_3'))=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1774, c_4])).
% 40.37/29.87  tff(c_1792, plain, (k10_relat_1('#skF_4', k1_relat_1('#skF_3'))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_1784])).
% 40.37/29.87  tff(c_2528, plain, (k10_relat_1('#skF_4', '#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2523, c_1792])).
% 40.37/29.87  tff(c_2530, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2523, c_1774])).
% 40.37/29.87  tff(c_3349, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_2656])).
% 40.37/29.87  tff(c_3381, plain, (k10_relat_1('#skF_4', k2_relat_1('#skF_4'))=k2_relat_1(k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3349, c_270])).
% 40.37/29.87  tff(c_3386, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_142, c_70, c_3350, c_79, c_2528, c_2530, c_3381])).
% 40.37/29.87  tff(c_3388, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_3386])).
% 40.37/29.87  tff(c_3391, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_3388])).
% 40.37/29.87  tff(c_3395, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_70, c_3391])).
% 40.37/29.87  tff(c_3396, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_3386])).
% 40.37/29.87  tff(c_77, plain, (![A_10, B_12]: (k2_funct_1(A_10)=B_12 | k6_partfun1(k2_relat_1(A_10))!=k5_relat_1(B_12, A_10) | k2_relat_1(B_12)!=k1_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_18])).
% 40.37/29.87  tff(c_2539, plain, (![B_12]: (k2_funct_1('#skF_4')=B_12 | k5_relat_1(B_12, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_12)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2530, c_77])).
% 40.37/29.87  tff(c_2549, plain, (![B_12]: (k2_funct_1('#skF_4')=B_12 | k5_relat_1(B_12, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_12)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_12) | ~v1_relat_1(B_12))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_70, c_2539])).
% 40.37/29.87  tff(c_48460, plain, (![B_1232]: (k2_funct_1('#skF_4')=B_1232 | k5_relat_1(B_1232, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_1232)!='#skF_2' | ~v1_funct_1(B_1232) | ~v1_relat_1(B_1232))), inference(demodulation, [status(thm), theory('equality')], [c_3350, c_3396, c_2549])).
% 40.37/29.87  tff(c_49234, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_141, c_48460])).
% 40.37/29.87  tff(c_49865, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_168, c_3477, c_49234])).
% 40.37/29.87  tff(c_49873, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_49865, c_3349])).
% 40.37/29.87  tff(c_49878, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1773, c_49873])).
% 40.37/29.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 40.37/29.87  
% 40.37/29.87  Inference rules
% 40.37/29.87  ----------------------
% 40.37/29.87  #Ref     : 0
% 40.37/29.87  #Sup     : 10369
% 40.37/29.87  #Fact    : 0
% 40.37/29.87  #Define  : 0
% 40.37/29.87  #Split   : 95
% 40.37/29.87  #Chain   : 0
% 40.37/29.87  #Close   : 0
% 40.37/29.87  
% 40.37/29.87  Ordering : KBO
% 40.37/29.87  
% 40.37/29.87  Simplification rules
% 40.37/29.87  ----------------------
% 40.37/29.87  #Subsume      : 511
% 40.37/29.87  #Demod        : 29470
% 40.37/29.87  #Tautology    : 1110
% 40.37/29.87  #SimpNegUnit  : 765
% 40.37/29.87  #BackRed      : 104
% 40.37/29.87  
% 40.37/29.87  #Partial instantiations: 0
% 40.37/29.87  #Strategies tried      : 1
% 40.37/29.87  
% 40.37/29.87  Timing (in seconds)
% 40.37/29.87  ----------------------
% 40.37/29.87  Preprocessing        : 0.54
% 40.37/29.87  Parsing              : 0.30
% 40.37/29.87  CNF conversion       : 0.04
% 40.37/29.87  Main loop            : 28.42
% 40.37/29.87  Inferencing          : 4.16
% 40.37/29.87  Reduction            : 17.16
% 40.37/29.87  Demodulation         : 15.40
% 40.37/29.87  BG Simplification    : 0.27
% 40.37/29.87  Subsumption          : 5.81
% 40.37/29.87  Abstraction          : 0.53
% 40.37/29.87  MUC search           : 0.00
% 40.37/29.87  Cooper               : 0.00
% 40.37/29.87  Total                : 29.02
% 40.37/29.87  Index Insertion      : 0.00
% 40.37/29.87  Index Deletion       : 0.00
% 40.37/29.87  Index Matching       : 0.00
% 40.37/29.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
