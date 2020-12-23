%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:57 EST 2020

% Result     : Theorem 9.21s
% Output     : CNFRefutation 9.41s
% Verified   : 
% Statistics : Number of formulae       :  142 (7113 expanded)
%              Number of leaves         :   44 (2521 expanded)
%              Depth                    :   27
%              Number of atoms          :  315 (29638 expanded)
%              Number of equality atoms :   71 (7163 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_157,negated_conjecture,(
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

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_119,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_129,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_103,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_115,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_131,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(c_48,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_92,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_103,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_92])).

tff(c_120,plain,(
    ! [C_58,A_59,B_60] :
      ( v4_relat_1(C_58,A_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_131,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_120])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_104,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_92])).

tff(c_132,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_120])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_relat_1(B_2),A_1)
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_54,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_14,plain,(
    ! [A_14] :
      ( v1_relat_1(k2_funct_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_42,plain,(
    ! [A_36] : m1_subset_1(k6_partfun1(A_36),k1_zfmisc_1(k2_zfmisc_1(A_36,A_36))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_102,plain,(
    ! [A_36] : v1_relat_1(k6_partfun1(A_36)) ),
    inference(resolution,[status(thm)],[c_42,c_92])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_650,plain,(
    ! [D_130,F_129,C_132,A_127,E_131,B_128] :
      ( k1_partfun1(A_127,B_128,C_132,D_130,E_131,F_129) = k5_relat_1(E_131,F_129)
      | ~ m1_subset_1(F_129,k1_zfmisc_1(k2_zfmisc_1(C_132,D_130)))
      | ~ v1_funct_1(F_129)
      | ~ m1_subset_1(E_131,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128)))
      | ~ v1_funct_1(E_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_654,plain,(
    ! [A_127,B_128,E_131] :
      ( k1_partfun1(A_127,B_128,'#skF_2','#skF_1',E_131,'#skF_4') = k5_relat_1(E_131,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_131,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128)))
      | ~ v1_funct_1(E_131) ) ),
    inference(resolution,[status(thm)],[c_60,c_650])).

tff(c_664,plain,(
    ! [A_133,B_134,E_135] :
      ( k1_partfun1(A_133,B_134,'#skF_2','#skF_1',E_135,'#skF_4') = k5_relat_1(E_135,'#skF_4')
      | ~ m1_subset_1(E_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134)))
      | ~ v1_funct_1(E_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_654])).

tff(c_673,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_664])).

tff(c_680,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_673])).

tff(c_56,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_483,plain,(
    ! [D_97,C_98,A_99,B_100] :
      ( D_97 = C_98
      | ~ r2_relset_1(A_99,B_100,C_98,D_97)
      | ~ m1_subset_1(D_97,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100)))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_491,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_56,c_483])).

tff(c_506,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_491])).

tff(c_518,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_506])).

tff(c_687,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_680,c_518])).

tff(c_699,plain,(
    ! [C_137,D_142,F_139,B_138,E_141,A_140] :
      ( m1_subset_1(k1_partfun1(A_140,B_138,C_137,D_142,E_141,F_139),k1_zfmisc_1(k2_zfmisc_1(A_140,D_142)))
      | ~ m1_subset_1(F_139,k1_zfmisc_1(k2_zfmisc_1(C_137,D_142)))
      | ~ v1_funct_1(F_139)
      | ~ m1_subset_1(E_141,k1_zfmisc_1(k2_zfmisc_1(A_140,B_138)))
      | ~ v1_funct_1(E_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_729,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_680,c_699])).

tff(c_744,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_729])).

tff(c_746,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_687,c_744])).

tff(c_747,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_506])).

tff(c_1221,plain,(
    ! [C_166,D_171,E_170,B_167,F_168,A_169] :
      ( v1_funct_1(k1_partfun1(A_169,B_167,C_166,D_171,E_170,F_168))
      | ~ m1_subset_1(F_168,k1_zfmisc_1(k2_zfmisc_1(C_166,D_171)))
      | ~ v1_funct_1(F_168)
      | ~ m1_subset_1(E_170,k1_zfmisc_1(k2_zfmisc_1(A_169,B_167)))
      | ~ v1_funct_1(E_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1225,plain,(
    ! [A_169,B_167,E_170] :
      ( v1_funct_1(k1_partfun1(A_169,B_167,'#skF_2','#skF_1',E_170,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_170,k1_zfmisc_1(k2_zfmisc_1(A_169,B_167)))
      | ~ v1_funct_1(E_170) ) ),
    inference(resolution,[status(thm)],[c_60,c_1221])).

tff(c_1235,plain,(
    ! [A_172,B_173,E_174] :
      ( v1_funct_1(k1_partfun1(A_172,B_173,'#skF_2','#skF_1',E_174,'#skF_4'))
      | ~ m1_subset_1(E_174,k1_zfmisc_1(k2_zfmisc_1(A_172,B_173)))
      | ~ v1_funct_1(E_174) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1225])).

tff(c_1244,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1235])).

tff(c_1251,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_747,c_1244])).

tff(c_1271,plain,(
    ! [E_184,D_183,C_185,A_180,B_181,F_182] :
      ( k1_partfun1(A_180,B_181,C_185,D_183,E_184,F_182) = k5_relat_1(E_184,F_182)
      | ~ m1_subset_1(F_182,k1_zfmisc_1(k2_zfmisc_1(C_185,D_183)))
      | ~ v1_funct_1(F_182)
      | ~ m1_subset_1(E_184,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181)))
      | ~ v1_funct_1(E_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1277,plain,(
    ! [A_180,B_181,E_184] :
      ( k1_partfun1(A_180,B_181,'#skF_1','#skF_2',E_184,'#skF_3') = k5_relat_1(E_184,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_184,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181)))
      | ~ v1_funct_1(E_184) ) ),
    inference(resolution,[status(thm)],[c_66,c_1271])).

tff(c_1326,plain,(
    ! [A_189,B_190,E_191] :
      ( k1_partfun1(A_189,B_190,'#skF_1','#skF_2',E_191,'#skF_3') = k5_relat_1(E_191,'#skF_3')
      | ~ m1_subset_1(E_191,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190)))
      | ~ v1_funct_1(E_191) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1277])).

tff(c_1468,plain,(
    ! [A_198] :
      ( k1_partfun1(A_198,A_198,'#skF_1','#skF_2',k6_partfun1(A_198),'#skF_3') = k5_relat_1(k6_partfun1(A_198),'#skF_3')
      | ~ v1_funct_1(k6_partfun1(A_198)) ) ),
    inference(resolution,[status(thm)],[c_42,c_1326])).

tff(c_1471,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3') = k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1251,c_1468])).

tff(c_36,plain,(
    ! [D_33,A_30,C_32,B_31,E_34,F_35] :
      ( m1_subset_1(k1_partfun1(A_30,B_31,C_32,D_33,E_34,F_35),k1_zfmisc_1(k2_zfmisc_1(A_30,D_33)))
      | ~ m1_subset_1(F_35,k1_zfmisc_1(k2_zfmisc_1(C_32,D_33)))
      | ~ v1_funct_1(F_35)
      | ~ m1_subset_1(E_34,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | ~ v1_funct_1(E_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2029,plain,
    ( m1_subset_1(k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1471,c_36])).

tff(c_2036,plain,(
    m1_subset_1(k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1251,c_42,c_70,c_66,c_2029])).

tff(c_46,plain,(
    ! [A_43] : k6_relat_1(A_43) = k6_partfun1(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_8,plain,(
    ! [A_10,B_11] :
      ( k5_relat_1(k6_relat_1(A_10),B_11) = B_11
      | ~ r1_tarski(k1_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_156,plain,(
    ! [A_69,B_70] :
      ( k5_relat_1(k6_partfun1(A_69),B_70) = B_70
      | ~ r1_tarski(k1_relat_1(B_70),A_69)
      | ~ v1_relat_1(B_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8])).

tff(c_163,plain,(
    ! [A_1,B_2] :
      ( k5_relat_1(k6_partfun1(A_1),B_2) = B_2
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_156])).

tff(c_32,plain,(
    ! [A_26,B_27,D_29] :
      ( r2_relset_1(A_26,B_27,D_29,D_29)
      | ~ m1_subset_1(D_29,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2139,plain,(
    r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),k5_relat_1(k6_partfun1('#skF_1'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_2036,c_32])).

tff(c_2598,plain,
    ( r2_relset_1('#skF_1','#skF_2','#skF_3',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'))
    | ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_2139])).

tff(c_2615,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_132,c_2598])).

tff(c_34,plain,(
    ! [D_29,C_28,A_26,B_27] :
      ( D_29 = C_28
      | ~ r2_relset_1(A_26,B_27,C_28,D_29)
      | ~ m1_subset_1(D_29,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2670,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3'
    | ~ m1_subset_1(k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_2615,c_34])).

tff(c_2682,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2036,c_2670])).

tff(c_271,plain,(
    ! [A_85,B_86,C_87] :
      ( k5_relat_1(k5_relat_1(A_85,B_86),C_87) = k5_relat_1(A_85,k5_relat_1(B_86,C_87))
      | ~ v1_relat_1(C_87)
      | ~ v1_relat_1(B_86)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [A_16] :
      ( k5_relat_1(A_16,k2_funct_1(A_16)) = k6_relat_1(k1_relat_1(A_16))
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_71,plain,(
    ! [A_16] :
      ( k5_relat_1(A_16,k2_funct_1(A_16)) = k6_partfun1(k1_relat_1(A_16))
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_22])).

tff(c_4120,plain,(
    ! [A_272,B_273] :
      ( k5_relat_1(A_272,k5_relat_1(B_273,k2_funct_1(k5_relat_1(A_272,B_273)))) = k6_partfun1(k1_relat_1(k5_relat_1(A_272,B_273)))
      | ~ v2_funct_1(k5_relat_1(A_272,B_273))
      | ~ v1_funct_1(k5_relat_1(A_272,B_273))
      | ~ v1_relat_1(k5_relat_1(A_272,B_273))
      | ~ v1_relat_1(k2_funct_1(k5_relat_1(A_272,B_273)))
      | ~ v1_relat_1(B_273)
      | ~ v1_relat_1(A_272) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_71])).

tff(c_6,plain,(
    ! [A_3,B_7,C_9] :
      ( k5_relat_1(k5_relat_1(A_3,B_7),C_9) = k5_relat_1(A_3,k5_relat_1(B_7,C_9))
      | ~ v1_relat_1(C_9)
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2725,plain,(
    ! [C_9] :
      ( k5_relat_1(k6_partfun1('#skF_1'),k5_relat_1('#skF_3',C_9)) = k5_relat_1('#skF_3',C_9)
      | ~ v1_relat_1(C_9)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k6_partfun1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2682,c_6])).

tff(c_2753,plain,(
    ! [C_9] :
      ( k5_relat_1(k6_partfun1('#skF_1'),k5_relat_1('#skF_3',C_9)) = k5_relat_1('#skF_3',C_9)
      | ~ v1_relat_1(C_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_104,c_2725])).

tff(c_4134,plain,
    ( k5_relat_1('#skF_3',k2_funct_1(k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'))) = k6_partfun1(k1_relat_1(k5_relat_1(k6_partfun1('#skF_1'),'#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k5_relat_1(k6_partfun1('#skF_1'),'#skF_3')))
    | ~ v2_funct_1(k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'))
    | ~ v1_funct_1(k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'))
    | ~ v1_relat_1(k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'))
    | ~ v1_relat_1(k2_funct_1(k5_relat_1(k6_partfun1('#skF_1'),'#skF_3')))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k6_partfun1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4120,c_2753])).

tff(c_4418,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_104,c_2682,c_104,c_2682,c_70,c_2682,c_54,c_2682,c_2682,c_2682,c_2682,c_4134])).

tff(c_4516,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_4418])).

tff(c_4519,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_4516])).

tff(c_4523,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_70,c_4519])).

tff(c_4525,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_4418])).

tff(c_1275,plain,(
    ! [A_180,B_181,E_184] :
      ( k1_partfun1(A_180,B_181,'#skF_2','#skF_1',E_184,'#skF_4') = k5_relat_1(E_184,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_184,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181)))
      | ~ v1_funct_1(E_184) ) ),
    inference(resolution,[status(thm)],[c_60,c_1271])).

tff(c_1285,plain,(
    ! [A_186,B_187,E_188] :
      ( k1_partfun1(A_186,B_187,'#skF_2','#skF_1',E_188,'#skF_4') = k5_relat_1(E_188,'#skF_4')
      | ~ m1_subset_1(E_188,k1_zfmisc_1(k2_zfmisc_1(A_186,B_187)))
      | ~ v1_funct_1(E_188) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1275])).

tff(c_1294,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1285])).

tff(c_1301,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_747,c_1294])).

tff(c_58,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_196,plain,(
    ! [A_78,B_79,C_80] :
      ( k2_relset_1(A_78,B_79,C_80) = k2_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_205,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_196])).

tff(c_209,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_205])).

tff(c_20,plain,(
    ! [A_16] :
      ( k5_relat_1(k2_funct_1(A_16),A_16) = k6_relat_1(k2_relat_1(A_16))
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_72,plain,(
    ! [A_16] :
      ( k5_relat_1(k2_funct_1(A_16),A_16) = k6_partfun1(k2_relat_1(A_16))
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_20])).

tff(c_2149,plain,(
    ! [A_214,C_215] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_214)),C_215) = k5_relat_1(k2_funct_1(A_214),k5_relat_1(A_214,C_215))
      | ~ v1_relat_1(C_215)
      | ~ v1_relat_1(A_214)
      | ~ v1_relat_1(k2_funct_1(A_214))
      | ~ v2_funct_1(A_214)
      | ~ v1_funct_1(A_214)
      | ~ v1_relat_1(A_214) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_271])).

tff(c_2310,plain,(
    ! [C_215] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_215)) = k5_relat_1(k6_partfun1('#skF_2'),C_215)
      | ~ v1_relat_1(C_215)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_2149])).

tff(c_2367,plain,(
    ! [C_215] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_215)) = k5_relat_1(k6_partfun1('#skF_2'),C_215)
      | ~ v1_relat_1(C_215)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_70,c_54,c_104,c_2310])).

tff(c_5281,plain,(
    ! [C_313] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_313)) = k5_relat_1(k6_partfun1('#skF_2'),C_313)
      | ~ v1_relat_1(C_313) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4525,c_2367])).

tff(c_5332,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1301,c_5281])).

tff(c_5383,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_5332])).

tff(c_184,plain,(
    ! [A_77] :
      ( k2_relat_1(k2_funct_1(A_77)) = k1_relat_1(A_77)
      | ~ v2_funct_1(A_77)
      | ~ v1_funct_1(A_77)
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_10,plain,(
    ! [B_13,A_12] :
      ( k5_relat_1(B_13,k6_relat_1(A_12)) = B_13
      | ~ r1_tarski(k2_relat_1(B_13),A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_73,plain,(
    ! [B_13,A_12] :
      ( k5_relat_1(B_13,k6_partfun1(A_12)) = B_13
      | ~ r1_tarski(k2_relat_1(B_13),A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_10])).

tff(c_190,plain,(
    ! [A_77,A_12] :
      ( k5_relat_1(k2_funct_1(A_77),k6_partfun1(A_12)) = k2_funct_1(A_77)
      | ~ r1_tarski(k1_relat_1(A_77),A_12)
      | ~ v1_relat_1(k2_funct_1(A_77))
      | ~ v2_funct_1(A_77)
      | ~ v1_funct_1(A_77)
      | ~ v1_relat_1(A_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_73])).

tff(c_5410,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = k2_funct_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5383,c_190])).

tff(c_5429,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = k2_funct_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_70,c_54,c_4525,c_5410])).

tff(c_6119,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_5429])).

tff(c_6122,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_6119])).

tff(c_6126,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_132,c_6122])).

tff(c_6127,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_5429])).

tff(c_6201,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6127,c_163])).

tff(c_6220,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_131,c_6201])).

tff(c_6222,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_6220])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:44:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.21/3.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.21/3.05  
% 9.21/3.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.21/3.05  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.21/3.05  
% 9.21/3.05  %Foreground sorts:
% 9.21/3.05  
% 9.21/3.05  
% 9.21/3.05  %Background operators:
% 9.21/3.05  
% 9.21/3.05  
% 9.21/3.05  %Foreground operators:
% 9.21/3.05  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.21/3.05  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.21/3.05  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.21/3.05  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.21/3.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.21/3.05  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.21/3.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.21/3.05  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.21/3.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.21/3.05  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.21/3.05  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.21/3.05  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.21/3.05  tff('#skF_2', type, '#skF_2': $i).
% 9.21/3.05  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.21/3.05  tff('#skF_3', type, '#skF_3': $i).
% 9.21/3.05  tff('#skF_1', type, '#skF_1': $i).
% 9.21/3.05  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.21/3.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.21/3.05  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.21/3.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.21/3.05  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.21/3.05  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.21/3.05  tff('#skF_4', type, '#skF_4': $i).
% 9.21/3.05  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.21/3.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.21/3.05  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.21/3.05  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.21/3.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.21/3.05  
% 9.41/3.07  tff(f_157, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 9.41/3.07  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.41/3.07  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.41/3.07  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 9.41/3.07  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 9.41/3.07  tff(f_119, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 9.41/3.07  tff(f_129, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 9.41/3.07  tff(f_103, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 9.41/3.07  tff(f_115, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 9.41/3.07  tff(f_131, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.41/3.07  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 9.41/3.07  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 9.41/3.07  tff(f_81, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 9.41/3.07  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.41/3.07  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 9.41/3.07  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 9.41/3.07  tff(c_48, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_157])).
% 9.41/3.07  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_157])).
% 9.41/3.07  tff(c_92, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.41/3.07  tff(c_103, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_92])).
% 9.41/3.07  tff(c_120, plain, (![C_58, A_59, B_60]: (v4_relat_1(C_58, A_59) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.41/3.07  tff(c_131, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_120])).
% 9.41/3.07  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_157])).
% 9.41/3.07  tff(c_104, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_92])).
% 9.41/3.07  tff(c_132, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_120])).
% 9.41/3.07  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k1_relat_1(B_2), A_1) | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.41/3.07  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 9.41/3.07  tff(c_54, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 9.41/3.07  tff(c_14, plain, (![A_14]: (v1_relat_1(k2_funct_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.41/3.07  tff(c_42, plain, (![A_36]: (m1_subset_1(k6_partfun1(A_36), k1_zfmisc_1(k2_zfmisc_1(A_36, A_36))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.41/3.07  tff(c_102, plain, (![A_36]: (v1_relat_1(k6_partfun1(A_36)))), inference(resolution, [status(thm)], [c_42, c_92])).
% 9.41/3.07  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_157])).
% 9.41/3.07  tff(c_650, plain, (![D_130, F_129, C_132, A_127, E_131, B_128]: (k1_partfun1(A_127, B_128, C_132, D_130, E_131, F_129)=k5_relat_1(E_131, F_129) | ~m1_subset_1(F_129, k1_zfmisc_1(k2_zfmisc_1(C_132, D_130))) | ~v1_funct_1(F_129) | ~m1_subset_1(E_131, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))) | ~v1_funct_1(E_131))), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.41/3.07  tff(c_654, plain, (![A_127, B_128, E_131]: (k1_partfun1(A_127, B_128, '#skF_2', '#skF_1', E_131, '#skF_4')=k5_relat_1(E_131, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_131, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))) | ~v1_funct_1(E_131))), inference(resolution, [status(thm)], [c_60, c_650])).
% 9.41/3.07  tff(c_664, plain, (![A_133, B_134, E_135]: (k1_partfun1(A_133, B_134, '#skF_2', '#skF_1', E_135, '#skF_4')=k5_relat_1(E_135, '#skF_4') | ~m1_subset_1(E_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))) | ~v1_funct_1(E_135))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_654])).
% 9.41/3.07  tff(c_673, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_664])).
% 9.41/3.07  tff(c_680, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_673])).
% 9.41/3.07  tff(c_56, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 9.41/3.07  tff(c_483, plain, (![D_97, C_98, A_99, B_100]: (D_97=C_98 | ~r2_relset_1(A_99, B_100, C_98, D_97) | ~m1_subset_1(D_97, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.41/3.07  tff(c_491, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_56, c_483])).
% 9.41/3.07  tff(c_506, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_491])).
% 9.41/3.07  tff(c_518, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_506])).
% 9.41/3.07  tff(c_687, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_680, c_518])).
% 9.41/3.07  tff(c_699, plain, (![C_137, D_142, F_139, B_138, E_141, A_140]: (m1_subset_1(k1_partfun1(A_140, B_138, C_137, D_142, E_141, F_139), k1_zfmisc_1(k2_zfmisc_1(A_140, D_142))) | ~m1_subset_1(F_139, k1_zfmisc_1(k2_zfmisc_1(C_137, D_142))) | ~v1_funct_1(F_139) | ~m1_subset_1(E_141, k1_zfmisc_1(k2_zfmisc_1(A_140, B_138))) | ~v1_funct_1(E_141))), inference(cnfTransformation, [status(thm)], [f_115])).
% 9.41/3.07  tff(c_729, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_680, c_699])).
% 9.41/3.07  tff(c_744, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_729])).
% 9.41/3.07  tff(c_746, plain, $false, inference(negUnitSimplification, [status(thm)], [c_687, c_744])).
% 9.41/3.07  tff(c_747, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_506])).
% 9.41/3.07  tff(c_1221, plain, (![C_166, D_171, E_170, B_167, F_168, A_169]: (v1_funct_1(k1_partfun1(A_169, B_167, C_166, D_171, E_170, F_168)) | ~m1_subset_1(F_168, k1_zfmisc_1(k2_zfmisc_1(C_166, D_171))) | ~v1_funct_1(F_168) | ~m1_subset_1(E_170, k1_zfmisc_1(k2_zfmisc_1(A_169, B_167))) | ~v1_funct_1(E_170))), inference(cnfTransformation, [status(thm)], [f_115])).
% 9.41/3.07  tff(c_1225, plain, (![A_169, B_167, E_170]: (v1_funct_1(k1_partfun1(A_169, B_167, '#skF_2', '#skF_1', E_170, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_170, k1_zfmisc_1(k2_zfmisc_1(A_169, B_167))) | ~v1_funct_1(E_170))), inference(resolution, [status(thm)], [c_60, c_1221])).
% 9.41/3.07  tff(c_1235, plain, (![A_172, B_173, E_174]: (v1_funct_1(k1_partfun1(A_172, B_173, '#skF_2', '#skF_1', E_174, '#skF_4')) | ~m1_subset_1(E_174, k1_zfmisc_1(k2_zfmisc_1(A_172, B_173))) | ~v1_funct_1(E_174))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1225])).
% 9.41/3.07  tff(c_1244, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_1235])).
% 9.41/3.07  tff(c_1251, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_747, c_1244])).
% 9.41/3.07  tff(c_1271, plain, (![E_184, D_183, C_185, A_180, B_181, F_182]: (k1_partfun1(A_180, B_181, C_185, D_183, E_184, F_182)=k5_relat_1(E_184, F_182) | ~m1_subset_1(F_182, k1_zfmisc_1(k2_zfmisc_1(C_185, D_183))) | ~v1_funct_1(F_182) | ~m1_subset_1(E_184, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))) | ~v1_funct_1(E_184))), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.41/3.07  tff(c_1277, plain, (![A_180, B_181, E_184]: (k1_partfun1(A_180, B_181, '#skF_1', '#skF_2', E_184, '#skF_3')=k5_relat_1(E_184, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_184, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))) | ~v1_funct_1(E_184))), inference(resolution, [status(thm)], [c_66, c_1271])).
% 9.41/3.07  tff(c_1326, plain, (![A_189, B_190, E_191]: (k1_partfun1(A_189, B_190, '#skF_1', '#skF_2', E_191, '#skF_3')=k5_relat_1(E_191, '#skF_3') | ~m1_subset_1(E_191, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))) | ~v1_funct_1(E_191))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1277])).
% 9.41/3.07  tff(c_1468, plain, (![A_198]: (k1_partfun1(A_198, A_198, '#skF_1', '#skF_2', k6_partfun1(A_198), '#skF_3')=k5_relat_1(k6_partfun1(A_198), '#skF_3') | ~v1_funct_1(k6_partfun1(A_198)))), inference(resolution, [status(thm)], [c_42, c_1326])).
% 9.41/3.07  tff(c_1471, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3')=k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_1251, c_1468])).
% 9.41/3.07  tff(c_36, plain, (![D_33, A_30, C_32, B_31, E_34, F_35]: (m1_subset_1(k1_partfun1(A_30, B_31, C_32, D_33, E_34, F_35), k1_zfmisc_1(k2_zfmisc_1(A_30, D_33))) | ~m1_subset_1(F_35, k1_zfmisc_1(k2_zfmisc_1(C_32, D_33))) | ~v1_funct_1(F_35) | ~m1_subset_1(E_34, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | ~v1_funct_1(E_34))), inference(cnfTransformation, [status(thm)], [f_115])).
% 9.41/3.07  tff(c_2029, plain, (m1_subset_1(k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1(k6_partfun1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1471, c_36])).
% 9.41/3.07  tff(c_2036, plain, (m1_subset_1(k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1251, c_42, c_70, c_66, c_2029])).
% 9.41/3.07  tff(c_46, plain, (![A_43]: (k6_relat_1(A_43)=k6_partfun1(A_43))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.41/3.07  tff(c_8, plain, (![A_10, B_11]: (k5_relat_1(k6_relat_1(A_10), B_11)=B_11 | ~r1_tarski(k1_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.41/3.07  tff(c_156, plain, (![A_69, B_70]: (k5_relat_1(k6_partfun1(A_69), B_70)=B_70 | ~r1_tarski(k1_relat_1(B_70), A_69) | ~v1_relat_1(B_70))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8])).
% 9.41/3.07  tff(c_163, plain, (![A_1, B_2]: (k5_relat_1(k6_partfun1(A_1), B_2)=B_2 | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(resolution, [status(thm)], [c_4, c_156])).
% 9.41/3.07  tff(c_32, plain, (![A_26, B_27, D_29]: (r2_relset_1(A_26, B_27, D_29, D_29) | ~m1_subset_1(D_29, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.41/3.07  tff(c_2139, plain, (r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'))), inference(resolution, [status(thm)], [c_2036, c_32])).
% 9.41/3.07  tff(c_2598, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')) | ~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_163, c_2139])).
% 9.41/3.07  tff(c_2615, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_132, c_2598])).
% 9.41/3.07  tff(c_34, plain, (![D_29, C_28, A_26, B_27]: (D_29=C_28 | ~r2_relset_1(A_26, B_27, C_28, D_29) | ~m1_subset_1(D_29, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.41/3.07  tff(c_2670, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3' | ~m1_subset_1(k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_2615, c_34])).
% 9.41/3.07  tff(c_2682, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2036, c_2670])).
% 9.41/3.07  tff(c_271, plain, (![A_85, B_86, C_87]: (k5_relat_1(k5_relat_1(A_85, B_86), C_87)=k5_relat_1(A_85, k5_relat_1(B_86, C_87)) | ~v1_relat_1(C_87) | ~v1_relat_1(B_86) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.41/3.07  tff(c_22, plain, (![A_16]: (k5_relat_1(A_16, k2_funct_1(A_16))=k6_relat_1(k1_relat_1(A_16)) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.41/3.07  tff(c_71, plain, (![A_16]: (k5_relat_1(A_16, k2_funct_1(A_16))=k6_partfun1(k1_relat_1(A_16)) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_22])).
% 9.41/3.07  tff(c_4120, plain, (![A_272, B_273]: (k5_relat_1(A_272, k5_relat_1(B_273, k2_funct_1(k5_relat_1(A_272, B_273))))=k6_partfun1(k1_relat_1(k5_relat_1(A_272, B_273))) | ~v2_funct_1(k5_relat_1(A_272, B_273)) | ~v1_funct_1(k5_relat_1(A_272, B_273)) | ~v1_relat_1(k5_relat_1(A_272, B_273)) | ~v1_relat_1(k2_funct_1(k5_relat_1(A_272, B_273))) | ~v1_relat_1(B_273) | ~v1_relat_1(A_272))), inference(superposition, [status(thm), theory('equality')], [c_271, c_71])).
% 9.41/3.07  tff(c_6, plain, (![A_3, B_7, C_9]: (k5_relat_1(k5_relat_1(A_3, B_7), C_9)=k5_relat_1(A_3, k5_relat_1(B_7, C_9)) | ~v1_relat_1(C_9) | ~v1_relat_1(B_7) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.41/3.07  tff(c_2725, plain, (![C_9]: (k5_relat_1(k6_partfun1('#skF_1'), k5_relat_1('#skF_3', C_9))=k5_relat_1('#skF_3', C_9) | ~v1_relat_1(C_9) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k6_partfun1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2682, c_6])).
% 9.41/3.07  tff(c_2753, plain, (![C_9]: (k5_relat_1(k6_partfun1('#skF_1'), k5_relat_1('#skF_3', C_9))=k5_relat_1('#skF_3', C_9) | ~v1_relat_1(C_9))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_104, c_2725])).
% 9.41/3.07  tff(c_4134, plain, (k5_relat_1('#skF_3', k2_funct_1(k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')))=k6_partfun1(k1_relat_1(k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'))) | ~v1_relat_1(k2_funct_1(k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'))) | ~v2_funct_1(k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')) | ~v1_funct_1(k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')) | ~v1_relat_1(k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')) | ~v1_relat_1(k2_funct_1(k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'))) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k6_partfun1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4120, c_2753])).
% 9.41/3.07  tff(c_4418, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_104, c_2682, c_104, c_2682, c_70, c_2682, c_54, c_2682, c_2682, c_2682, c_2682, c_4134])).
% 9.41/3.07  tff(c_4516, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_4418])).
% 9.41/3.07  tff(c_4519, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_4516])).
% 9.41/3.07  tff(c_4523, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_70, c_4519])).
% 9.41/3.07  tff(c_4525, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_4418])).
% 9.41/3.07  tff(c_1275, plain, (![A_180, B_181, E_184]: (k1_partfun1(A_180, B_181, '#skF_2', '#skF_1', E_184, '#skF_4')=k5_relat_1(E_184, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_184, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))) | ~v1_funct_1(E_184))), inference(resolution, [status(thm)], [c_60, c_1271])).
% 9.41/3.07  tff(c_1285, plain, (![A_186, B_187, E_188]: (k1_partfun1(A_186, B_187, '#skF_2', '#skF_1', E_188, '#skF_4')=k5_relat_1(E_188, '#skF_4') | ~m1_subset_1(E_188, k1_zfmisc_1(k2_zfmisc_1(A_186, B_187))) | ~v1_funct_1(E_188))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1275])).
% 9.41/3.07  tff(c_1294, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_1285])).
% 9.41/3.07  tff(c_1301, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_747, c_1294])).
% 9.41/3.07  tff(c_58, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_157])).
% 9.41/3.07  tff(c_196, plain, (![A_78, B_79, C_80]: (k2_relset_1(A_78, B_79, C_80)=k2_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.41/3.07  tff(c_205, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_196])).
% 9.41/3.07  tff(c_209, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_205])).
% 9.41/3.07  tff(c_20, plain, (![A_16]: (k5_relat_1(k2_funct_1(A_16), A_16)=k6_relat_1(k2_relat_1(A_16)) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.41/3.07  tff(c_72, plain, (![A_16]: (k5_relat_1(k2_funct_1(A_16), A_16)=k6_partfun1(k2_relat_1(A_16)) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_20])).
% 9.41/3.07  tff(c_2149, plain, (![A_214, C_215]: (k5_relat_1(k6_partfun1(k2_relat_1(A_214)), C_215)=k5_relat_1(k2_funct_1(A_214), k5_relat_1(A_214, C_215)) | ~v1_relat_1(C_215) | ~v1_relat_1(A_214) | ~v1_relat_1(k2_funct_1(A_214)) | ~v2_funct_1(A_214) | ~v1_funct_1(A_214) | ~v1_relat_1(A_214))), inference(superposition, [status(thm), theory('equality')], [c_72, c_271])).
% 9.41/3.07  tff(c_2310, plain, (![C_215]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_215))=k5_relat_1(k6_partfun1('#skF_2'), C_215) | ~v1_relat_1(C_215) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_209, c_2149])).
% 9.41/3.07  tff(c_2367, plain, (![C_215]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_215))=k5_relat_1(k6_partfun1('#skF_2'), C_215) | ~v1_relat_1(C_215) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_70, c_54, c_104, c_2310])).
% 9.41/3.07  tff(c_5281, plain, (![C_313]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_313))=k5_relat_1(k6_partfun1('#skF_2'), C_313) | ~v1_relat_1(C_313))), inference(demodulation, [status(thm), theory('equality')], [c_4525, c_2367])).
% 9.41/3.07  tff(c_5332, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1301, c_5281])).
% 9.41/3.07  tff(c_5383, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_5332])).
% 9.41/3.07  tff(c_184, plain, (![A_77]: (k2_relat_1(k2_funct_1(A_77))=k1_relat_1(A_77) | ~v2_funct_1(A_77) | ~v1_funct_1(A_77) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.41/3.07  tff(c_10, plain, (![B_13, A_12]: (k5_relat_1(B_13, k6_relat_1(A_12))=B_13 | ~r1_tarski(k2_relat_1(B_13), A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.41/3.07  tff(c_73, plain, (![B_13, A_12]: (k5_relat_1(B_13, k6_partfun1(A_12))=B_13 | ~r1_tarski(k2_relat_1(B_13), A_12) | ~v1_relat_1(B_13))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_10])).
% 9.41/3.07  tff(c_190, plain, (![A_77, A_12]: (k5_relat_1(k2_funct_1(A_77), k6_partfun1(A_12))=k2_funct_1(A_77) | ~r1_tarski(k1_relat_1(A_77), A_12) | ~v1_relat_1(k2_funct_1(A_77)) | ~v2_funct_1(A_77) | ~v1_funct_1(A_77) | ~v1_relat_1(A_77))), inference(superposition, [status(thm), theory('equality')], [c_184, c_73])).
% 9.41/3.07  tff(c_5410, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')=k2_funct_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5383, c_190])).
% 9.41/3.07  tff(c_5429, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')=k2_funct_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_70, c_54, c_4525, c_5410])).
% 9.41/3.07  tff(c_6119, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_5429])).
% 9.41/3.07  tff(c_6122, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4, c_6119])).
% 9.41/3.07  tff(c_6126, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_132, c_6122])).
% 9.41/3.07  tff(c_6127, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_5429])).
% 9.41/3.07  tff(c_6201, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6127, c_163])).
% 9.41/3.07  tff(c_6220, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_103, c_131, c_6201])).
% 9.41/3.07  tff(c_6222, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_6220])).
% 9.41/3.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.41/3.07  
% 9.41/3.07  Inference rules
% 9.41/3.07  ----------------------
% 9.41/3.07  #Ref     : 0
% 9.41/3.07  #Sup     : 1329
% 9.41/3.07  #Fact    : 0
% 9.41/3.07  #Define  : 0
% 9.41/3.07  #Split   : 9
% 9.41/3.07  #Chain   : 0
% 9.41/3.07  #Close   : 0
% 9.41/3.07  
% 9.41/3.07  Ordering : KBO
% 9.41/3.07  
% 9.41/3.07  Simplification rules
% 9.41/3.07  ----------------------
% 9.41/3.07  #Subsume      : 144
% 9.41/3.07  #Demod        : 1675
% 9.41/3.07  #Tautology    : 304
% 9.41/3.07  #SimpNegUnit  : 3
% 9.41/3.08  #BackRed      : 59
% 9.41/3.08  
% 9.41/3.08  #Partial instantiations: 0
% 9.41/3.08  #Strategies tried      : 1
% 9.41/3.08  
% 9.41/3.08  Timing (in seconds)
% 9.41/3.08  ----------------------
% 9.41/3.08  Preprocessing        : 0.49
% 9.41/3.08  Parsing              : 0.22
% 9.41/3.08  CNF conversion       : 0.05
% 9.41/3.08  Main loop            : 1.79
% 9.41/3.08  Inferencing          : 0.59
% 9.41/3.08  Reduction            : 0.70
% 9.41/3.08  Demodulation         : 0.54
% 9.41/3.08  BG Simplification    : 0.08
% 9.41/3.08  Subsumption          : 0.31
% 9.41/3.08  Abstraction          : 0.08
% 9.41/3.08  MUC search           : 0.00
% 9.41/3.08  Cooper               : 0.00
% 9.41/3.08  Total                : 2.32
% 9.41/3.08  Index Insertion      : 0.00
% 9.41/3.08  Index Deletion       : 0.00
% 9.41/3.08  Index Matching       : 0.00
% 9.41/3.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
