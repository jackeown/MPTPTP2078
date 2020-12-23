%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:06 EST 2020

% Result     : Theorem 49.51s
% Output     : CNFRefutation 49.60s
% Verified   : 
% Statistics : Number of formulae       :  195 (2082 expanded)
%              Number of leaves         :   45 ( 744 expanded)
%              Depth                    :   22
%              Number of atoms          :  486 (8687 expanded)
%              Number of equality atoms :  167 (3067 expanded)
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

tff(f_206,negated_conjecture,(
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

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_48,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_119,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_109,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_105,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_121,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_40,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_77,axiom,(
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

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_180,axiom,(
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

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_138,axiom,(
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

tff(f_164,axiom,(
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
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_121,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_133,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_121])).

tff(c_78,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_12,plain,(
    ! [A_6] :
      ( v1_relat_1(k2_funct_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_501,plain,(
    ! [A_119,F_118,D_121,C_116,E_120,B_117] :
      ( k1_partfun1(A_119,B_117,C_116,D_121,E_120,F_118) = k5_relat_1(E_120,F_118)
      | ~ m1_subset_1(F_118,k1_zfmisc_1(k2_zfmisc_1(C_116,D_121)))
      | ~ v1_funct_1(F_118)
      | ~ m1_subset_1(E_120,k1_zfmisc_1(k2_zfmisc_1(A_119,B_117)))
      | ~ v1_funct_1(E_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_507,plain,(
    ! [A_119,B_117,E_120] :
      ( k1_partfun1(A_119,B_117,'#skF_2','#skF_1',E_120,'#skF_4') = k5_relat_1(E_120,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_120,k1_zfmisc_1(k2_zfmisc_1(A_119,B_117)))
      | ~ v1_funct_1(E_120) ) ),
    inference(resolution,[status(thm)],[c_68,c_501])).

tff(c_574,plain,(
    ! [A_133,B_134,E_135] :
      ( k1_partfun1(A_133,B_134,'#skF_2','#skF_1',E_135,'#skF_4') = k5_relat_1(E_135,'#skF_4')
      | ~ m1_subset_1(E_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134)))
      | ~ v1_funct_1(E_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_507])).

tff(c_580,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_574])).

tff(c_587,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_580])).

tff(c_36,plain,(
    ! [A_29] : m1_subset_1(k6_partfun1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_64,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_289,plain,(
    ! [D_82,C_83,A_84,B_85] :
      ( D_82 = C_83
      | ~ r2_relset_1(A_84,B_85,C_83,D_82)
      | ~ m1_subset_1(D_82,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85)))
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_297,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_64,c_289])).

tff(c_312,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_297])).

tff(c_431,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_312])).

tff(c_592,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_587,c_431])).

tff(c_673,plain,(
    ! [A_144,B_142,D_143,E_141,F_140,C_139] :
      ( m1_subset_1(k1_partfun1(A_144,B_142,C_139,D_143,E_141,F_140),k1_zfmisc_1(k2_zfmisc_1(A_144,D_143)))
      | ~ m1_subset_1(F_140,k1_zfmisc_1(k2_zfmisc_1(C_139,D_143)))
      | ~ v1_funct_1(F_140)
      | ~ m1_subset_1(E_141,k1_zfmisc_1(k2_zfmisc_1(A_144,B_142)))
      | ~ v1_funct_1(E_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_709,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_587,c_673])).

tff(c_731,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_68,c_709])).

tff(c_733,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_592,c_731])).

tff(c_734,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_312])).

tff(c_777,plain,(
    ! [E_155,D_157,F_154,B_156,A_158,C_153] :
      ( v1_funct_1(k1_partfun1(A_158,B_156,C_153,D_157,E_155,F_154))
      | ~ m1_subset_1(F_154,k1_zfmisc_1(k2_zfmisc_1(C_153,D_157)))
      | ~ v1_funct_1(F_154)
      | ~ m1_subset_1(E_155,k1_zfmisc_1(k2_zfmisc_1(A_158,B_156)))
      | ~ v1_funct_1(E_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_783,plain,(
    ! [A_158,B_156,E_155] :
      ( v1_funct_1(k1_partfun1(A_158,B_156,'#skF_2','#skF_1',E_155,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_155,k1_zfmisc_1(k2_zfmisc_1(A_158,B_156)))
      | ~ v1_funct_1(E_155) ) ),
    inference(resolution,[status(thm)],[c_68,c_777])).

tff(c_808,plain,(
    ! [A_162,B_163,E_164] :
      ( v1_funct_1(k1_partfun1(A_162,B_163,'#skF_2','#skF_1',E_164,'#skF_4'))
      | ~ m1_subset_1(E_164,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163)))
      | ~ v1_funct_1(E_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_783])).

tff(c_814,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_808])).

tff(c_821,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_734,c_814])).

tff(c_40,plain,(
    ! [A_36] : k6_relat_1(A_36) = k6_partfun1(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_8,plain,(
    ! [A_5] : k2_relat_1(k6_relat_1(A_5)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_82,plain,(
    ! [A_5] : k2_relat_1(k6_partfun1(A_5)) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_8])).

tff(c_14,plain,(
    ! [A_7] : v1_relat_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_81,plain,(
    ! [A_7] : v1_relat_1(k6_partfun1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_14])).

tff(c_62,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_66,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_168,plain,(
    ! [A_69,B_70,C_71] :
      ( k2_relset_1(A_69,B_70,C_71) = k2_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_174,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_168])).

tff(c_181,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_174])).

tff(c_20,plain,(
    ! [A_10,B_12] :
      ( k2_funct_1(A_10) = B_12
      | k6_relat_1(k2_relat_1(A_10)) != k5_relat_1(B_12,A_10)
      | k2_relat_1(B_12) != k1_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_390,plain,(
    ! [A_92,B_93] :
      ( k2_funct_1(A_92) = B_93
      | k6_partfun1(k2_relat_1(A_92)) != k5_relat_1(B_93,A_92)
      | k2_relat_1(B_93) != k1_relat_1(A_92)
      | ~ v2_funct_1(A_92)
      | ~ v1_funct_1(B_93)
      | ~ v1_relat_1(B_93)
      | ~ v1_funct_1(A_92)
      | ~ v1_relat_1(A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_20])).

tff(c_400,plain,(
    ! [B_93] :
      ( k2_funct_1('#skF_3') = B_93
      | k5_relat_1(B_93,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_93) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_93)
      | ~ v1_relat_1(B_93)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_390])).

tff(c_407,plain,(
    ! [B_94] :
      ( k2_funct_1('#skF_3') = B_94
      | k5_relat_1(B_94,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_94) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_94)
      | ~ v1_relat_1(B_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_78,c_62,c_400])).

tff(c_419,plain,(
    ! [A_7] :
      ( k6_partfun1(A_7) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_7),'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(k6_partfun1(A_7)) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(k6_partfun1(A_7)) ) ),
    inference(resolution,[status(thm)],[c_81,c_407])).

tff(c_429,plain,(
    ! [A_7] :
      ( k6_partfun1(A_7) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_7),'#skF_3') != k6_partfun1('#skF_2')
      | k1_relat_1('#skF_3') != A_7
      | ~ v1_funct_1(k6_partfun1(A_7)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_419])).

tff(c_828,plain,
    ( k6_partfun1('#skF_1') = k2_funct_1('#skF_3')
    | k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_821,c_429])).

tff(c_831,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_828])).

tff(c_4,plain,(
    ! [A_4] :
      ( k10_relat_1(A_4,k2_relat_1(A_4)) = k1_relat_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_186,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_4])).

tff(c_190,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_186])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_76,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_886,plain,(
    ! [A_177,C_178,B_179] :
      ( k6_partfun1(A_177) = k5_relat_1(C_178,k2_funct_1(C_178))
      | k1_xboole_0 = B_179
      | ~ v2_funct_1(C_178)
      | k2_relset_1(A_177,B_179,C_178) != B_179
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(A_177,B_179)))
      | ~ v1_funct_2(C_178,A_177,B_179)
      | ~ v1_funct_1(C_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_890,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_886])).

tff(c_898,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_66,c_62,c_890])).

tff(c_899,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_898])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( k9_relat_1(B_3,k2_relat_1(A_1)) = k2_relat_1(k5_relat_1(A_1,B_3))
      | ~ v1_relat_1(B_3)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_259,plain,(
    ! [B_79,A_80] :
      ( k9_relat_1(k2_funct_1(B_79),A_80) = k10_relat_1(B_79,A_80)
      | ~ v2_funct_1(B_79)
      | ~ v1_funct_1(B_79)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_273,plain,(
    ! [A_1,B_79] :
      ( k2_relat_1(k5_relat_1(A_1,k2_funct_1(B_79))) = k10_relat_1(B_79,k2_relat_1(A_1))
      | ~ v2_funct_1(B_79)
      | ~ v1_funct_1(B_79)
      | ~ v1_relat_1(B_79)
      | ~ v1_relat_1(k2_funct_1(B_79))
      | ~ v1_relat_1(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_259])).

tff(c_907,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k2_relat_1(k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_899,c_273])).

tff(c_920,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_133,c_78,c_62,c_82,c_190,c_181,c_907])).

tff(c_921,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_831,c_920])).

tff(c_930,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_921])).

tff(c_934,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_78,c_930])).

tff(c_936,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_828])).

tff(c_56,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_134,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_121])).

tff(c_410,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_134,c_407])).

tff(c_422,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_410])).

tff(c_423,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_422])).

tff(c_430,plain,(
    k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_423])).

tff(c_940,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_936,c_430])).

tff(c_70,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_149,plain,(
    ! [A_65,B_66,D_67] :
      ( r2_relset_1(A_65,B_66,D_67,D_67)
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_156,plain,(
    ! [A_29] : r2_relset_1(A_29,A_29,k6_partfun1(A_29),k6_partfun1(A_29)) ),
    inference(resolution,[status(thm)],[c_36,c_149])).

tff(c_182,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_168])).

tff(c_1763,plain,(
    ! [A_226,B_227,C_228,D_229] :
      ( k2_relset_1(A_226,B_227,C_228) = B_227
      | ~ r2_relset_1(B_227,B_227,k1_partfun1(B_227,A_226,A_226,B_227,D_229,C_228),k6_partfun1(B_227))
      | ~ m1_subset_1(D_229,k1_zfmisc_1(k2_zfmisc_1(B_227,A_226)))
      | ~ v1_funct_2(D_229,B_227,A_226)
      | ~ v1_funct_1(D_229)
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(A_226,B_227)))
      | ~ v1_funct_2(C_228,A_226,B_227)
      | ~ v1_funct_1(C_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1769,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_734,c_1763])).

tff(c_1773,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_78,c_76,c_74,c_156,c_182,c_1769])).

tff(c_1775,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_940,c_1773])).

tff(c_1776,plain,(
    k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_423])).

tff(c_1878,plain,(
    ! [B_247,D_251,C_246,F_248,E_250,A_249] :
      ( k1_partfun1(A_249,B_247,C_246,D_251,E_250,F_248) = k5_relat_1(E_250,F_248)
      | ~ m1_subset_1(F_248,k1_zfmisc_1(k2_zfmisc_1(C_246,D_251)))
      | ~ v1_funct_1(F_248)
      | ~ m1_subset_1(E_250,k1_zfmisc_1(k2_zfmisc_1(A_249,B_247)))
      | ~ v1_funct_1(E_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1884,plain,(
    ! [A_249,B_247,E_250] :
      ( k1_partfun1(A_249,B_247,'#skF_2','#skF_1',E_250,'#skF_4') = k5_relat_1(E_250,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_250,k1_zfmisc_1(k2_zfmisc_1(A_249,B_247)))
      | ~ v1_funct_1(E_250) ) ),
    inference(resolution,[status(thm)],[c_68,c_1878])).

tff(c_1920,plain,(
    ! [A_256,B_257,E_258] :
      ( k1_partfun1(A_256,B_257,'#skF_2','#skF_1',E_258,'#skF_4') = k5_relat_1(E_258,'#skF_4')
      | ~ m1_subset_1(E_258,k1_zfmisc_1(k2_zfmisc_1(A_256,B_257)))
      | ~ v1_funct_1(E_258) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1884])).

tff(c_1926,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_1920])).

tff(c_1933,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1926])).

tff(c_1801,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_312])).

tff(c_1938,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1933,c_1801])).

tff(c_2158,plain,(
    ! [A_274,D_273,C_269,E_271,F_270,B_272] :
      ( m1_subset_1(k1_partfun1(A_274,B_272,C_269,D_273,E_271,F_270),k1_zfmisc_1(k2_zfmisc_1(A_274,D_273)))
      | ~ m1_subset_1(F_270,k1_zfmisc_1(k2_zfmisc_1(C_269,D_273)))
      | ~ v1_funct_1(F_270)
      | ~ m1_subset_1(E_271,k1_zfmisc_1(k2_zfmisc_1(A_274,B_272)))
      | ~ v1_funct_1(E_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2192,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1933,c_2158])).

tff(c_2213,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_68,c_2192])).

tff(c_2215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1938,c_2213])).

tff(c_2216,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_312])).

tff(c_2571,plain,(
    ! [C_312,A_315,D_317,F_314,E_316,B_313] :
      ( k1_partfun1(A_315,B_313,C_312,D_317,E_316,F_314) = k5_relat_1(E_316,F_314)
      | ~ m1_subset_1(F_314,k1_zfmisc_1(k2_zfmisc_1(C_312,D_317)))
      | ~ v1_funct_1(F_314)
      | ~ m1_subset_1(E_316,k1_zfmisc_1(k2_zfmisc_1(A_315,B_313)))
      | ~ v1_funct_1(E_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2577,plain,(
    ! [A_315,B_313,E_316] :
      ( k1_partfun1(A_315,B_313,'#skF_2','#skF_1',E_316,'#skF_4') = k5_relat_1(E_316,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_316,k1_zfmisc_1(k2_zfmisc_1(A_315,B_313)))
      | ~ v1_funct_1(E_316) ) ),
    inference(resolution,[status(thm)],[c_68,c_2571])).

tff(c_3283,plain,(
    ! [A_354,B_355,E_356] :
      ( k1_partfun1(A_354,B_355,'#skF_2','#skF_1',E_356,'#skF_4') = k5_relat_1(E_356,'#skF_4')
      | ~ m1_subset_1(E_356,k1_zfmisc_1(k2_zfmisc_1(A_354,B_355)))
      | ~ v1_funct_1(E_356) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2577])).

tff(c_3289,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_3283])).

tff(c_3296,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2216,c_3289])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_2279,plain,(
    ! [B_281,A_283,C_278,F_279,D_282,E_280] :
      ( v1_funct_1(k1_partfun1(A_283,B_281,C_278,D_282,E_280,F_279))
      | ~ m1_subset_1(F_279,k1_zfmisc_1(k2_zfmisc_1(C_278,D_282)))
      | ~ v1_funct_1(F_279)
      | ~ m1_subset_1(E_280,k1_zfmisc_1(k2_zfmisc_1(A_283,B_281)))
      | ~ v1_funct_1(E_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2285,plain,(
    ! [A_283,B_281,E_280] :
      ( v1_funct_1(k1_partfun1(A_283,B_281,'#skF_2','#skF_1',E_280,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_280,k1_zfmisc_1(k2_zfmisc_1(A_283,B_281)))
      | ~ v1_funct_1(E_280) ) ),
    inference(resolution,[status(thm)],[c_68,c_2279])).

tff(c_2310,plain,(
    ! [A_287,B_288,E_289] :
      ( v1_funct_1(k1_partfun1(A_287,B_288,'#skF_2','#skF_1',E_289,'#skF_4'))
      | ~ m1_subset_1(E_289,k1_zfmisc_1(k2_zfmisc_1(A_287,B_288)))
      | ~ v1_funct_1(E_289) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2285])).

tff(c_2316,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_2310])).

tff(c_2323,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2216,c_2316])).

tff(c_2330,plain,
    ( k6_partfun1('#skF_1') = k2_funct_1('#skF_3')
    | k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_2323,c_429])).

tff(c_2333,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2330])).

tff(c_2476,plain,(
    ! [A_309,C_310,B_311] :
      ( k6_partfun1(A_309) = k5_relat_1(C_310,k2_funct_1(C_310))
      | k1_xboole_0 = B_311
      | ~ v2_funct_1(C_310)
      | k2_relset_1(A_309,B_311,C_310) != B_311
      | ~ m1_subset_1(C_310,k1_zfmisc_1(k2_zfmisc_1(A_309,B_311)))
      | ~ v1_funct_2(C_310,A_309,B_311)
      | ~ v1_funct_1(C_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_2480,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_2476])).

tff(c_2488,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_66,c_62,c_2480])).

tff(c_2489,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2488])).

tff(c_2497,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k2_relat_1(k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2489,c_273])).

tff(c_2510,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_133,c_78,c_62,c_82,c_190,c_181,c_2497])).

tff(c_2511,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_2333,c_2510])).

tff(c_2520,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_2511])).

tff(c_2524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_78,c_2520])).

tff(c_2526,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2330])).

tff(c_1777,plain,(
    k2_relat_1('#skF_4') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_423])).

tff(c_1778,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1777,c_182])).

tff(c_2532,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2526,c_1778])).

tff(c_2642,plain,(
    ! [A_322,C_323,B_324] :
      ( k6_partfun1(A_322) = k5_relat_1(C_323,k2_funct_1(C_323))
      | k1_xboole_0 = B_324
      | ~ v2_funct_1(C_323)
      | k2_relset_1(A_322,B_324,C_323) != B_324
      | ~ m1_subset_1(C_323,k1_zfmisc_1(k2_zfmisc_1(A_322,B_324)))
      | ~ v1_funct_2(C_323,A_322,B_324)
      | ~ v1_funct_1(C_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_2648,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_2642])).

tff(c_2658,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_2532,c_2648])).

tff(c_2659,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2658])).

tff(c_2693,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2659])).

tff(c_16,plain,(
    ! [A_7] : v2_funct_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_80,plain,(
    ! [A_7] : v2_funct_1(k6_partfun1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_16])).

tff(c_3151,plain,(
    ! [D_346,A_348,C_350,B_347,E_349] :
      ( k1_xboole_0 = C_350
      | v2_funct_1(E_349)
      | k2_relset_1(A_348,B_347,D_346) != B_347
      | ~ v2_funct_1(k1_partfun1(A_348,B_347,B_347,C_350,D_346,E_349))
      | ~ m1_subset_1(E_349,k1_zfmisc_1(k2_zfmisc_1(B_347,C_350)))
      | ~ v1_funct_2(E_349,B_347,C_350)
      | ~ v1_funct_1(E_349)
      | ~ m1_subset_1(D_346,k1_zfmisc_1(k2_zfmisc_1(A_348,B_347)))
      | ~ v1_funct_2(D_346,A_348,B_347)
      | ~ v1_funct_1(D_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_3157,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_2216,c_3151])).

tff(c_3165,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_72,c_70,c_68,c_80,c_66,c_3157])).

tff(c_3167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2693,c_60,c_3165])).

tff(c_3169,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2659])).

tff(c_1787,plain,
    ( k10_relat_1('#skF_4',k1_relat_1('#skF_3')) = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1777,c_4])).

tff(c_1795,plain,(
    k10_relat_1('#skF_4',k1_relat_1('#skF_3')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_1787])).

tff(c_2531,plain,(
    k10_relat_1('#skF_4','#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2526,c_1795])).

tff(c_2533,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2526,c_1777])).

tff(c_3168,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2659])).

tff(c_3200,plain,
    ( k10_relat_1('#skF_4',k2_relat_1('#skF_4')) = k2_relat_1(k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3168,c_273])).

tff(c_3205,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_134,c_72,c_3169,c_82,c_2531,c_2533,c_3200])).

tff(c_3207,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3205])).

tff(c_3210,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_3207])).

tff(c_3214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_72,c_3210])).

tff(c_3215,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3205])).

tff(c_79,plain,(
    ! [A_10,B_12] :
      ( k2_funct_1(A_10) = B_12
      | k6_partfun1(k2_relat_1(A_10)) != k5_relat_1(B_12,A_10)
      | k2_relat_1(B_12) != k1_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_20])).

tff(c_2542,plain,(
    ! [B_12] :
      ( k2_funct_1('#skF_4') = B_12
      | k5_relat_1(B_12,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_12) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2533,c_79])).

tff(c_2552,plain,(
    ! [B_12] :
      ( k2_funct_1('#skF_4') = B_12
      | k5_relat_1(B_12,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_12) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_72,c_2542])).

tff(c_59550,plain,(
    ! [B_1323] :
      ( k2_funct_1('#skF_4') = B_1323
      | k5_relat_1(B_1323,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_1323) != '#skF_2'
      | ~ v1_funct_1(B_1323)
      | ~ v1_relat_1(B_1323) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3169,c_3215,c_2552])).

tff(c_60399,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_133,c_59550])).

tff(c_61107,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_181,c_3296,c_60399])).

tff(c_61117,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61107,c_3168])).

tff(c_61122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1776,c_61117])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:27:00 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 49.51/38.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 49.60/38.31  
% 49.60/38.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 49.60/38.31  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 49.60/38.31  
% 49.60/38.31  %Foreground sorts:
% 49.60/38.31  
% 49.60/38.31  
% 49.60/38.31  %Background operators:
% 49.60/38.31  
% 49.60/38.31  
% 49.60/38.31  %Foreground operators:
% 49.60/38.31  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 49.60/38.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 49.60/38.31  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 49.60/38.31  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 49.60/38.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 49.60/38.31  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 49.60/38.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 49.60/38.31  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 49.60/38.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 49.60/38.31  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 49.60/38.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 49.60/38.31  tff('#skF_2', type, '#skF_2': $i).
% 49.60/38.31  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 49.60/38.31  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 49.60/38.31  tff('#skF_3', type, '#skF_3': $i).
% 49.60/38.31  tff('#skF_1', type, '#skF_1': $i).
% 49.60/38.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 49.60/38.31  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 49.60/38.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 49.60/38.31  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 49.60/38.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 49.60/38.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 49.60/38.31  tff('#skF_4', type, '#skF_4': $i).
% 49.60/38.31  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 49.60/38.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 49.60/38.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 49.60/38.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 49.60/38.31  
% 49.60/38.34  tff(f_206, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 49.60/38.34  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 49.60/38.34  tff(f_48, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 49.60/38.34  tff(f_119, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 49.60/38.34  tff(f_109, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 49.60/38.34  tff(f_93, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 49.60/38.34  tff(f_105, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 49.60/38.34  tff(f_121, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 49.60/38.34  tff(f_40, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 49.60/38.34  tff(f_52, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 49.60/38.34  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 49.60/38.34  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 49.60/38.34  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 49.60/38.34  tff(f_180, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 49.60/38.34  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 49.60/38.34  tff(f_60, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 49.60/38.34  tff(f_138, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 49.60/38.34  tff(f_164, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 49.60/38.34  tff(c_74, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_206])).
% 49.60/38.34  tff(c_121, plain, (![C_61, A_62, B_63]: (v1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 49.60/38.34  tff(c_133, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_121])).
% 49.60/38.34  tff(c_78, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_206])).
% 49.60/38.34  tff(c_12, plain, (![A_6]: (v1_relat_1(k2_funct_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 49.60/38.34  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_206])).
% 49.60/38.34  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_206])).
% 49.60/38.34  tff(c_501, plain, (![A_119, F_118, D_121, C_116, E_120, B_117]: (k1_partfun1(A_119, B_117, C_116, D_121, E_120, F_118)=k5_relat_1(E_120, F_118) | ~m1_subset_1(F_118, k1_zfmisc_1(k2_zfmisc_1(C_116, D_121))) | ~v1_funct_1(F_118) | ~m1_subset_1(E_120, k1_zfmisc_1(k2_zfmisc_1(A_119, B_117))) | ~v1_funct_1(E_120))), inference(cnfTransformation, [status(thm)], [f_119])).
% 49.60/38.34  tff(c_507, plain, (![A_119, B_117, E_120]: (k1_partfun1(A_119, B_117, '#skF_2', '#skF_1', E_120, '#skF_4')=k5_relat_1(E_120, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_120, k1_zfmisc_1(k2_zfmisc_1(A_119, B_117))) | ~v1_funct_1(E_120))), inference(resolution, [status(thm)], [c_68, c_501])).
% 49.60/38.34  tff(c_574, plain, (![A_133, B_134, E_135]: (k1_partfun1(A_133, B_134, '#skF_2', '#skF_1', E_135, '#skF_4')=k5_relat_1(E_135, '#skF_4') | ~m1_subset_1(E_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))) | ~v1_funct_1(E_135))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_507])).
% 49.60/38.34  tff(c_580, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_574])).
% 49.60/38.34  tff(c_587, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_580])).
% 49.60/38.34  tff(c_36, plain, (![A_29]: (m1_subset_1(k6_partfun1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 49.60/38.34  tff(c_64, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_206])).
% 49.60/38.34  tff(c_289, plain, (![D_82, C_83, A_84, B_85]: (D_82=C_83 | ~r2_relset_1(A_84, B_85, C_83, D_82) | ~m1_subset_1(D_82, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 49.60/38.34  tff(c_297, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_64, c_289])).
% 49.60/38.34  tff(c_312, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_297])).
% 49.60/38.34  tff(c_431, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_312])).
% 49.60/38.34  tff(c_592, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_587, c_431])).
% 49.60/38.34  tff(c_673, plain, (![A_144, B_142, D_143, E_141, F_140, C_139]: (m1_subset_1(k1_partfun1(A_144, B_142, C_139, D_143, E_141, F_140), k1_zfmisc_1(k2_zfmisc_1(A_144, D_143))) | ~m1_subset_1(F_140, k1_zfmisc_1(k2_zfmisc_1(C_139, D_143))) | ~v1_funct_1(F_140) | ~m1_subset_1(E_141, k1_zfmisc_1(k2_zfmisc_1(A_144, B_142))) | ~v1_funct_1(E_141))), inference(cnfTransformation, [status(thm)], [f_105])).
% 49.60/38.34  tff(c_709, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_587, c_673])).
% 49.60/38.34  tff(c_731, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_68, c_709])).
% 49.60/38.34  tff(c_733, plain, $false, inference(negUnitSimplification, [status(thm)], [c_592, c_731])).
% 49.60/38.34  tff(c_734, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_312])).
% 49.60/38.34  tff(c_777, plain, (![E_155, D_157, F_154, B_156, A_158, C_153]: (v1_funct_1(k1_partfun1(A_158, B_156, C_153, D_157, E_155, F_154)) | ~m1_subset_1(F_154, k1_zfmisc_1(k2_zfmisc_1(C_153, D_157))) | ~v1_funct_1(F_154) | ~m1_subset_1(E_155, k1_zfmisc_1(k2_zfmisc_1(A_158, B_156))) | ~v1_funct_1(E_155))), inference(cnfTransformation, [status(thm)], [f_105])).
% 49.60/38.34  tff(c_783, plain, (![A_158, B_156, E_155]: (v1_funct_1(k1_partfun1(A_158, B_156, '#skF_2', '#skF_1', E_155, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_155, k1_zfmisc_1(k2_zfmisc_1(A_158, B_156))) | ~v1_funct_1(E_155))), inference(resolution, [status(thm)], [c_68, c_777])).
% 49.60/38.34  tff(c_808, plain, (![A_162, B_163, E_164]: (v1_funct_1(k1_partfun1(A_162, B_163, '#skF_2', '#skF_1', E_164, '#skF_4')) | ~m1_subset_1(E_164, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))) | ~v1_funct_1(E_164))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_783])).
% 49.60/38.34  tff(c_814, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_808])).
% 49.60/38.34  tff(c_821, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_734, c_814])).
% 49.60/38.34  tff(c_40, plain, (![A_36]: (k6_relat_1(A_36)=k6_partfun1(A_36))), inference(cnfTransformation, [status(thm)], [f_121])).
% 49.60/38.34  tff(c_8, plain, (![A_5]: (k2_relat_1(k6_relat_1(A_5))=A_5)), inference(cnfTransformation, [status(thm)], [f_40])).
% 49.60/38.34  tff(c_82, plain, (![A_5]: (k2_relat_1(k6_partfun1(A_5))=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_8])).
% 49.60/38.34  tff(c_14, plain, (![A_7]: (v1_relat_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 49.60/38.34  tff(c_81, plain, (![A_7]: (v1_relat_1(k6_partfun1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_14])).
% 49.60/38.34  tff(c_62, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_206])).
% 49.60/38.34  tff(c_66, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_206])).
% 49.60/38.34  tff(c_168, plain, (![A_69, B_70, C_71]: (k2_relset_1(A_69, B_70, C_71)=k2_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 49.60/38.34  tff(c_174, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_168])).
% 49.60/38.34  tff(c_181, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_174])).
% 49.60/38.34  tff(c_20, plain, (![A_10, B_12]: (k2_funct_1(A_10)=B_12 | k6_relat_1(k2_relat_1(A_10))!=k5_relat_1(B_12, A_10) | k2_relat_1(B_12)!=k1_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_77])).
% 49.60/38.34  tff(c_390, plain, (![A_92, B_93]: (k2_funct_1(A_92)=B_93 | k6_partfun1(k2_relat_1(A_92))!=k5_relat_1(B_93, A_92) | k2_relat_1(B_93)!=k1_relat_1(A_92) | ~v2_funct_1(A_92) | ~v1_funct_1(B_93) | ~v1_relat_1(B_93) | ~v1_funct_1(A_92) | ~v1_relat_1(A_92))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_20])).
% 49.60/38.34  tff(c_400, plain, (![B_93]: (k2_funct_1('#skF_3')=B_93 | k5_relat_1(B_93, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_93)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_93) | ~v1_relat_1(B_93) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_181, c_390])).
% 49.60/38.34  tff(c_407, plain, (![B_94]: (k2_funct_1('#skF_3')=B_94 | k5_relat_1(B_94, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_94)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_94) | ~v1_relat_1(B_94))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_78, c_62, c_400])).
% 49.60/38.34  tff(c_419, plain, (![A_7]: (k6_partfun1(A_7)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_7), '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(k6_partfun1(A_7))!=k1_relat_1('#skF_3') | ~v1_funct_1(k6_partfun1(A_7)))), inference(resolution, [status(thm)], [c_81, c_407])).
% 49.60/38.34  tff(c_429, plain, (![A_7]: (k6_partfun1(A_7)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_7), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!=A_7 | ~v1_funct_1(k6_partfun1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_419])).
% 49.60/38.34  tff(c_828, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_821, c_429])).
% 49.60/38.34  tff(c_831, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_828])).
% 49.60/38.34  tff(c_4, plain, (![A_4]: (k10_relat_1(A_4, k2_relat_1(A_4))=k1_relat_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 49.60/38.34  tff(c_186, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_181, c_4])).
% 49.60/38.34  tff(c_190, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_186])).
% 49.60/38.34  tff(c_58, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_206])).
% 49.60/38.34  tff(c_76, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_206])).
% 49.60/38.34  tff(c_886, plain, (![A_177, C_178, B_179]: (k6_partfun1(A_177)=k5_relat_1(C_178, k2_funct_1(C_178)) | k1_xboole_0=B_179 | ~v2_funct_1(C_178) | k2_relset_1(A_177, B_179, C_178)!=B_179 | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(A_177, B_179))) | ~v1_funct_2(C_178, A_177, B_179) | ~v1_funct_1(C_178))), inference(cnfTransformation, [status(thm)], [f_180])).
% 49.60/38.34  tff(c_890, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_886])).
% 49.60/38.34  tff(c_898, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_66, c_62, c_890])).
% 49.60/38.34  tff(c_899, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_58, c_898])).
% 49.60/38.34  tff(c_2, plain, (![B_3, A_1]: (k9_relat_1(B_3, k2_relat_1(A_1))=k2_relat_1(k5_relat_1(A_1, B_3)) | ~v1_relat_1(B_3) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 49.60/38.34  tff(c_259, plain, (![B_79, A_80]: (k9_relat_1(k2_funct_1(B_79), A_80)=k10_relat_1(B_79, A_80) | ~v2_funct_1(B_79) | ~v1_funct_1(B_79) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_60])).
% 49.60/38.34  tff(c_273, plain, (![A_1, B_79]: (k2_relat_1(k5_relat_1(A_1, k2_funct_1(B_79)))=k10_relat_1(B_79, k2_relat_1(A_1)) | ~v2_funct_1(B_79) | ~v1_funct_1(B_79) | ~v1_relat_1(B_79) | ~v1_relat_1(k2_funct_1(B_79)) | ~v1_relat_1(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_259])).
% 49.60/38.34  tff(c_907, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k2_relat_1(k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_899, c_273])).
% 49.60/38.34  tff(c_920, plain, (k1_relat_1('#skF_3')='#skF_1' | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_133, c_78, c_62, c_82, c_190, c_181, c_907])).
% 49.60/38.34  tff(c_921, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_831, c_920])).
% 49.60/38.34  tff(c_930, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_921])).
% 49.60/38.34  tff(c_934, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_133, c_78, c_930])).
% 49.60/38.34  tff(c_936, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_828])).
% 49.60/38.34  tff(c_56, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_206])).
% 49.60/38.34  tff(c_134, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_121])).
% 49.60/38.34  tff(c_410, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_134, c_407])).
% 49.60/38.34  tff(c_422, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_410])).
% 49.60/38.34  tff(c_423, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_422])).
% 49.60/38.34  tff(c_430, plain, (k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_423])).
% 49.60/38.34  tff(c_940, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_936, c_430])).
% 49.60/38.34  tff(c_70, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_206])).
% 49.60/38.34  tff(c_149, plain, (![A_65, B_66, D_67]: (r2_relset_1(A_65, B_66, D_67, D_67) | ~m1_subset_1(D_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 49.60/38.34  tff(c_156, plain, (![A_29]: (r2_relset_1(A_29, A_29, k6_partfun1(A_29), k6_partfun1(A_29)))), inference(resolution, [status(thm)], [c_36, c_149])).
% 49.60/38.34  tff(c_182, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_168])).
% 49.60/38.34  tff(c_1763, plain, (![A_226, B_227, C_228, D_229]: (k2_relset_1(A_226, B_227, C_228)=B_227 | ~r2_relset_1(B_227, B_227, k1_partfun1(B_227, A_226, A_226, B_227, D_229, C_228), k6_partfun1(B_227)) | ~m1_subset_1(D_229, k1_zfmisc_1(k2_zfmisc_1(B_227, A_226))) | ~v1_funct_2(D_229, B_227, A_226) | ~v1_funct_1(D_229) | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(A_226, B_227))) | ~v1_funct_2(C_228, A_226, B_227) | ~v1_funct_1(C_228))), inference(cnfTransformation, [status(thm)], [f_138])).
% 49.60/38.34  tff(c_1769, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_734, c_1763])).
% 49.60/38.34  tff(c_1773, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_78, c_76, c_74, c_156, c_182, c_1769])).
% 49.60/38.34  tff(c_1775, plain, $false, inference(negUnitSimplification, [status(thm)], [c_940, c_1773])).
% 49.60/38.34  tff(c_1776, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_423])).
% 49.60/38.34  tff(c_1878, plain, (![B_247, D_251, C_246, F_248, E_250, A_249]: (k1_partfun1(A_249, B_247, C_246, D_251, E_250, F_248)=k5_relat_1(E_250, F_248) | ~m1_subset_1(F_248, k1_zfmisc_1(k2_zfmisc_1(C_246, D_251))) | ~v1_funct_1(F_248) | ~m1_subset_1(E_250, k1_zfmisc_1(k2_zfmisc_1(A_249, B_247))) | ~v1_funct_1(E_250))), inference(cnfTransformation, [status(thm)], [f_119])).
% 49.60/38.34  tff(c_1884, plain, (![A_249, B_247, E_250]: (k1_partfun1(A_249, B_247, '#skF_2', '#skF_1', E_250, '#skF_4')=k5_relat_1(E_250, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_250, k1_zfmisc_1(k2_zfmisc_1(A_249, B_247))) | ~v1_funct_1(E_250))), inference(resolution, [status(thm)], [c_68, c_1878])).
% 49.60/38.34  tff(c_1920, plain, (![A_256, B_257, E_258]: (k1_partfun1(A_256, B_257, '#skF_2', '#skF_1', E_258, '#skF_4')=k5_relat_1(E_258, '#skF_4') | ~m1_subset_1(E_258, k1_zfmisc_1(k2_zfmisc_1(A_256, B_257))) | ~v1_funct_1(E_258))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1884])).
% 49.60/38.34  tff(c_1926, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_1920])).
% 49.60/38.34  tff(c_1933, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1926])).
% 49.60/38.34  tff(c_1801, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_312])).
% 49.60/38.34  tff(c_1938, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1933, c_1801])).
% 49.60/38.34  tff(c_2158, plain, (![A_274, D_273, C_269, E_271, F_270, B_272]: (m1_subset_1(k1_partfun1(A_274, B_272, C_269, D_273, E_271, F_270), k1_zfmisc_1(k2_zfmisc_1(A_274, D_273))) | ~m1_subset_1(F_270, k1_zfmisc_1(k2_zfmisc_1(C_269, D_273))) | ~v1_funct_1(F_270) | ~m1_subset_1(E_271, k1_zfmisc_1(k2_zfmisc_1(A_274, B_272))) | ~v1_funct_1(E_271))), inference(cnfTransformation, [status(thm)], [f_105])).
% 49.60/38.34  tff(c_2192, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1933, c_2158])).
% 49.60/38.34  tff(c_2213, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_68, c_2192])).
% 49.60/38.34  tff(c_2215, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1938, c_2213])).
% 49.60/38.34  tff(c_2216, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_312])).
% 49.60/38.34  tff(c_2571, plain, (![C_312, A_315, D_317, F_314, E_316, B_313]: (k1_partfun1(A_315, B_313, C_312, D_317, E_316, F_314)=k5_relat_1(E_316, F_314) | ~m1_subset_1(F_314, k1_zfmisc_1(k2_zfmisc_1(C_312, D_317))) | ~v1_funct_1(F_314) | ~m1_subset_1(E_316, k1_zfmisc_1(k2_zfmisc_1(A_315, B_313))) | ~v1_funct_1(E_316))), inference(cnfTransformation, [status(thm)], [f_119])).
% 49.60/38.34  tff(c_2577, plain, (![A_315, B_313, E_316]: (k1_partfun1(A_315, B_313, '#skF_2', '#skF_1', E_316, '#skF_4')=k5_relat_1(E_316, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_316, k1_zfmisc_1(k2_zfmisc_1(A_315, B_313))) | ~v1_funct_1(E_316))), inference(resolution, [status(thm)], [c_68, c_2571])).
% 49.60/38.34  tff(c_3283, plain, (![A_354, B_355, E_356]: (k1_partfun1(A_354, B_355, '#skF_2', '#skF_1', E_356, '#skF_4')=k5_relat_1(E_356, '#skF_4') | ~m1_subset_1(E_356, k1_zfmisc_1(k2_zfmisc_1(A_354, B_355))) | ~v1_funct_1(E_356))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2577])).
% 49.60/38.34  tff(c_3289, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_3283])).
% 49.60/38.34  tff(c_3296, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2216, c_3289])).
% 49.60/38.34  tff(c_60, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_206])).
% 49.60/38.34  tff(c_2279, plain, (![B_281, A_283, C_278, F_279, D_282, E_280]: (v1_funct_1(k1_partfun1(A_283, B_281, C_278, D_282, E_280, F_279)) | ~m1_subset_1(F_279, k1_zfmisc_1(k2_zfmisc_1(C_278, D_282))) | ~v1_funct_1(F_279) | ~m1_subset_1(E_280, k1_zfmisc_1(k2_zfmisc_1(A_283, B_281))) | ~v1_funct_1(E_280))), inference(cnfTransformation, [status(thm)], [f_105])).
% 49.60/38.34  tff(c_2285, plain, (![A_283, B_281, E_280]: (v1_funct_1(k1_partfun1(A_283, B_281, '#skF_2', '#skF_1', E_280, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_280, k1_zfmisc_1(k2_zfmisc_1(A_283, B_281))) | ~v1_funct_1(E_280))), inference(resolution, [status(thm)], [c_68, c_2279])).
% 49.60/38.34  tff(c_2310, plain, (![A_287, B_288, E_289]: (v1_funct_1(k1_partfun1(A_287, B_288, '#skF_2', '#skF_1', E_289, '#skF_4')) | ~m1_subset_1(E_289, k1_zfmisc_1(k2_zfmisc_1(A_287, B_288))) | ~v1_funct_1(E_289))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2285])).
% 49.60/38.34  tff(c_2316, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_2310])).
% 49.60/38.34  tff(c_2323, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2216, c_2316])).
% 49.60/38.34  tff(c_2330, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_2323, c_429])).
% 49.60/38.34  tff(c_2333, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2330])).
% 49.60/38.34  tff(c_2476, plain, (![A_309, C_310, B_311]: (k6_partfun1(A_309)=k5_relat_1(C_310, k2_funct_1(C_310)) | k1_xboole_0=B_311 | ~v2_funct_1(C_310) | k2_relset_1(A_309, B_311, C_310)!=B_311 | ~m1_subset_1(C_310, k1_zfmisc_1(k2_zfmisc_1(A_309, B_311))) | ~v1_funct_2(C_310, A_309, B_311) | ~v1_funct_1(C_310))), inference(cnfTransformation, [status(thm)], [f_180])).
% 49.60/38.34  tff(c_2480, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_2476])).
% 49.60/38.34  tff(c_2488, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_66, c_62, c_2480])).
% 49.60/38.34  tff(c_2489, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_58, c_2488])).
% 49.60/38.34  tff(c_2497, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k2_relat_1(k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2489, c_273])).
% 49.60/38.34  tff(c_2510, plain, (k1_relat_1('#skF_3')='#skF_1' | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_133, c_78, c_62, c_82, c_190, c_181, c_2497])).
% 49.60/38.34  tff(c_2511, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_2333, c_2510])).
% 49.60/38.34  tff(c_2520, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_2511])).
% 49.60/38.34  tff(c_2524, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_133, c_78, c_2520])).
% 49.60/38.34  tff(c_2526, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_2330])).
% 49.60/38.34  tff(c_1777, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_423])).
% 49.60/38.34  tff(c_1778, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1777, c_182])).
% 49.60/38.34  tff(c_2532, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2526, c_1778])).
% 49.60/38.34  tff(c_2642, plain, (![A_322, C_323, B_324]: (k6_partfun1(A_322)=k5_relat_1(C_323, k2_funct_1(C_323)) | k1_xboole_0=B_324 | ~v2_funct_1(C_323) | k2_relset_1(A_322, B_324, C_323)!=B_324 | ~m1_subset_1(C_323, k1_zfmisc_1(k2_zfmisc_1(A_322, B_324))) | ~v1_funct_2(C_323, A_322, B_324) | ~v1_funct_1(C_323))), inference(cnfTransformation, [status(thm)], [f_180])).
% 49.60/38.34  tff(c_2648, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_2642])).
% 49.60/38.34  tff(c_2658, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_2532, c_2648])).
% 49.60/38.34  tff(c_2659, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_60, c_2658])).
% 49.60/38.34  tff(c_2693, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_2659])).
% 49.60/38.34  tff(c_16, plain, (![A_7]: (v2_funct_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 49.60/38.34  tff(c_80, plain, (![A_7]: (v2_funct_1(k6_partfun1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_16])).
% 49.60/38.34  tff(c_3151, plain, (![D_346, A_348, C_350, B_347, E_349]: (k1_xboole_0=C_350 | v2_funct_1(E_349) | k2_relset_1(A_348, B_347, D_346)!=B_347 | ~v2_funct_1(k1_partfun1(A_348, B_347, B_347, C_350, D_346, E_349)) | ~m1_subset_1(E_349, k1_zfmisc_1(k2_zfmisc_1(B_347, C_350))) | ~v1_funct_2(E_349, B_347, C_350) | ~v1_funct_1(E_349) | ~m1_subset_1(D_346, k1_zfmisc_1(k2_zfmisc_1(A_348, B_347))) | ~v1_funct_2(D_346, A_348, B_347) | ~v1_funct_1(D_346))), inference(cnfTransformation, [status(thm)], [f_164])).
% 49.60/38.34  tff(c_3157, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2216, c_3151])).
% 49.60/38.34  tff(c_3165, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_72, c_70, c_68, c_80, c_66, c_3157])).
% 49.60/38.34  tff(c_3167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2693, c_60, c_3165])).
% 49.60/38.34  tff(c_3169, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_2659])).
% 49.60/38.34  tff(c_1787, plain, (k10_relat_1('#skF_4', k1_relat_1('#skF_3'))=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1777, c_4])).
% 49.60/38.34  tff(c_1795, plain, (k10_relat_1('#skF_4', k1_relat_1('#skF_3'))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_1787])).
% 49.60/38.34  tff(c_2531, plain, (k10_relat_1('#skF_4', '#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2526, c_1795])).
% 49.60/38.34  tff(c_2533, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2526, c_1777])).
% 49.60/38.34  tff(c_3168, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_2659])).
% 49.60/38.34  tff(c_3200, plain, (k10_relat_1('#skF_4', k2_relat_1('#skF_4'))=k2_relat_1(k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3168, c_273])).
% 49.60/38.34  tff(c_3205, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_134, c_72, c_3169, c_82, c_2531, c_2533, c_3200])).
% 49.60/38.34  tff(c_3207, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_3205])).
% 49.60/38.34  tff(c_3210, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_3207])).
% 49.60/38.34  tff(c_3214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_72, c_3210])).
% 49.60/38.34  tff(c_3215, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_3205])).
% 49.60/38.34  tff(c_79, plain, (![A_10, B_12]: (k2_funct_1(A_10)=B_12 | k6_partfun1(k2_relat_1(A_10))!=k5_relat_1(B_12, A_10) | k2_relat_1(B_12)!=k1_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_20])).
% 49.60/38.34  tff(c_2542, plain, (![B_12]: (k2_funct_1('#skF_4')=B_12 | k5_relat_1(B_12, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_12)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2533, c_79])).
% 49.60/38.34  tff(c_2552, plain, (![B_12]: (k2_funct_1('#skF_4')=B_12 | k5_relat_1(B_12, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_12)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_12) | ~v1_relat_1(B_12))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_72, c_2542])).
% 49.60/38.34  tff(c_59550, plain, (![B_1323]: (k2_funct_1('#skF_4')=B_1323 | k5_relat_1(B_1323, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_1323)!='#skF_2' | ~v1_funct_1(B_1323) | ~v1_relat_1(B_1323))), inference(demodulation, [status(thm), theory('equality')], [c_3169, c_3215, c_2552])).
% 49.60/38.34  tff(c_60399, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_133, c_59550])).
% 49.60/38.34  tff(c_61107, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_181, c_3296, c_60399])).
% 49.60/38.34  tff(c_61117, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_61107, c_3168])).
% 49.60/38.34  tff(c_61122, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1776, c_61117])).
% 49.60/38.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 49.60/38.34  
% 49.60/38.34  Inference rules
% 49.60/38.34  ----------------------
% 49.60/38.34  #Ref     : 0
% 49.60/38.34  #Sup     : 12697
% 49.60/38.34  #Fact    : 0
% 49.60/38.34  #Define  : 0
% 49.60/38.34  #Split   : 106
% 49.60/38.34  #Chain   : 0
% 49.60/38.34  #Close   : 0
% 49.60/38.34  
% 49.60/38.34  Ordering : KBO
% 49.60/38.34  
% 49.60/38.34  Simplification rules
% 49.60/38.34  ----------------------
% 49.60/38.34  #Subsume      : 872
% 49.60/38.34  #Demod        : 43819
% 49.60/38.34  #Tautology    : 1230
% 49.60/38.34  #SimpNegUnit  : 1321
% 49.60/38.34  #BackRed      : 112
% 49.60/38.34  
% 49.60/38.34  #Partial instantiations: 0
% 49.60/38.34  #Strategies tried      : 1
% 49.60/38.34  
% 49.60/38.34  Timing (in seconds)
% 49.60/38.34  ----------------------
% 49.60/38.34  Preprocessing        : 0.40
% 49.60/38.34  Parsing              : 0.22
% 49.60/38.34  CNF conversion       : 0.03
% 49.60/38.34  Main loop            : 37.13
% 49.60/38.34  Inferencing          : 4.79
% 49.60/38.34  Reduction            : 23.68
% 49.60/38.34  Demodulation         : 21.59
% 49.60/38.34  BG Simplification    : 0.31
% 49.60/38.34  Subsumption          : 7.22
% 49.60/38.34  Abstraction          : 0.68
% 49.60/38.34  MUC search           : 0.00
% 49.60/38.34  Cooper               : 0.00
% 49.60/38.34  Total                : 37.59
% 49.60/38.34  Index Insertion      : 0.00
% 49.60/38.34  Index Deletion       : 0.00
% 49.60/38.34  Index Matching       : 0.00
% 49.60/38.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
