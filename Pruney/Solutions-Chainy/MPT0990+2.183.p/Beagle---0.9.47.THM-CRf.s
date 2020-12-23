%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:23 EST 2020

% Result     : Theorem 10.03s
% Output     : CNFRefutation 10.20s
% Verified   : 
% Statistics : Number of formulae       :  204 (31136 expanded)
%              Number of leaves         :   48 (11073 expanded)
%              Depth                    :   35
%              Number of atoms          :  540 (141390 expanded)
%              Number of equality atoms :  172 (52583 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_228,negated_conjecture,(
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

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_117,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_121,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_105,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_131,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_192,axiom,(
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

tff(f_150,axiom,(
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

tff(f_133,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_176,axiom,(
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

tff(f_46,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_202,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_93,axiom,(
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

tff(f_54,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(c_68,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_90,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_78,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_86,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_251,plain,(
    ! [A_78,B_79,C_80] :
      ( k2_relset_1(A_78,B_79,C_80) = k2_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_260,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_251])).

tff(c_265,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_260])).

tff(c_84,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_80,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_1065,plain,(
    ! [A_124,B_121,E_122,F_123,D_125,C_120] :
      ( m1_subset_1(k1_partfun1(A_124,B_121,C_120,D_125,E_122,F_123),k1_zfmisc_1(k2_zfmisc_1(A_124,D_125)))
      | ~ m1_subset_1(F_123,k1_zfmisc_1(k2_zfmisc_1(C_120,D_125)))
      | ~ v1_funct_1(F_123)
      | ~ m1_subset_1(E_122,k1_zfmisc_1(k2_zfmisc_1(A_124,B_121)))
      | ~ v1_funct_1(E_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_42,plain,(
    ! [A_30] : m1_subset_1(k6_partfun1(A_30),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_76,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_368,plain,(
    ! [D_86,C_87,A_88,B_89] :
      ( D_86 = C_87
      | ~ r2_relset_1(A_88,B_89,C_87,D_86)
      | ~ m1_subset_1(D_86,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89)))
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_378,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_76,c_368])).

tff(c_397,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_378])).

tff(c_569,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_397])).

tff(c_1077,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1065,c_569])).

tff(c_1098,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_84,c_80,c_1077])).

tff(c_1099,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_397])).

tff(c_1258,plain,(
    ! [C_140,A_138,B_136,E_137,F_139,D_135] :
      ( k1_partfun1(A_138,B_136,C_140,D_135,E_137,F_139) = k5_relat_1(E_137,F_139)
      | ~ m1_subset_1(F_139,k1_zfmisc_1(k2_zfmisc_1(C_140,D_135)))
      | ~ v1_funct_1(F_139)
      | ~ m1_subset_1(E_137,k1_zfmisc_1(k2_zfmisc_1(A_138,B_136)))
      | ~ v1_funct_1(E_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1270,plain,(
    ! [A_138,B_136,E_137] :
      ( k1_partfun1(A_138,B_136,'#skF_2','#skF_1',E_137,'#skF_4') = k5_relat_1(E_137,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_137,k1_zfmisc_1(k2_zfmisc_1(A_138,B_136)))
      | ~ v1_funct_1(E_137) ) ),
    inference(resolution,[status(thm)],[c_80,c_1258])).

tff(c_2833,plain,(
    ! [A_223,B_224,E_225] :
      ( k1_partfun1(A_223,B_224,'#skF_2','#skF_1',E_225,'#skF_4') = k5_relat_1(E_225,'#skF_4')
      | ~ m1_subset_1(E_225,k1_zfmisc_1(k2_zfmisc_1(A_223,B_224)))
      | ~ v1_funct_1(E_225) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1270])).

tff(c_2854,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_2833])).

tff(c_2871,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_1099,c_2854])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_157,plain,(
    ! [B_67,A_68] :
      ( v1_relat_1(B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_68))
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_166,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_86,c_157])).

tff(c_175,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_166])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_82,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_263,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_251])).

tff(c_1350,plain,(
    ! [B_145,C_146,A_147] :
      ( k6_partfun1(B_145) = k5_relat_1(k2_funct_1(C_146),C_146)
      | k1_xboole_0 = B_145
      | ~ v2_funct_1(C_146)
      | k2_relset_1(A_147,B_145,C_146) != B_145
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_147,B_145)))
      | ~ v1_funct_2(C_146,A_147,B_145)
      | ~ v1_funct_1(C_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_1362,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_1350])).

tff(c_1381,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_263,c_1362])).

tff(c_1382,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1381])).

tff(c_1397,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1382])).

tff(c_88,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_241,plain,(
    ! [A_75,B_76,D_77] :
      ( r2_relset_1(A_75,B_76,D_77,D_77)
      | ~ m1_subset_1(D_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_248,plain,(
    ! [A_30] : r2_relset_1(A_30,A_30,k6_partfun1(A_30),k6_partfun1(A_30)) ),
    inference(resolution,[status(thm)],[c_42,c_241])).

tff(c_2074,plain,(
    ! [A_182,B_183,C_184,D_185] :
      ( k2_relset_1(A_182,B_183,C_184) = B_183
      | ~ r2_relset_1(B_183,B_183,k1_partfun1(B_183,A_182,A_182,B_183,D_185,C_184),k6_partfun1(B_183))
      | ~ m1_subset_1(D_185,k1_zfmisc_1(k2_zfmisc_1(B_183,A_182)))
      | ~ v1_funct_2(D_185,B_183,A_182)
      | ~ v1_funct_1(D_185)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_182,B_183)))
      | ~ v1_funct_2(C_184,A_182,B_183)
      | ~ v1_funct_1(C_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_2077,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1099,c_2074])).

tff(c_2079,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_90,c_88,c_86,c_248,c_263,c_2077])).

tff(c_2081,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1397,c_2079])).

tff(c_2082,plain,
    ( ~ v2_funct_1('#skF_4')
    | k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1382])).

tff(c_2127,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2082])).

tff(c_46,plain,(
    ! [A_37] : k6_relat_1(A_37) = k6_partfun1(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_20,plain,(
    ! [A_10] : v2_funct_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_92,plain,(
    ! [A_10] : v2_funct_1(k6_partfun1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_20])).

tff(c_2806,plain,(
    ! [D_220,B_222,A_221,E_218,C_219] :
      ( k1_xboole_0 = C_219
      | v2_funct_1(E_218)
      | k2_relset_1(A_221,B_222,D_220) != B_222
      | ~ v2_funct_1(k1_partfun1(A_221,B_222,B_222,C_219,D_220,E_218))
      | ~ m1_subset_1(E_218,k1_zfmisc_1(k2_zfmisc_1(B_222,C_219)))
      | ~ v1_funct_2(E_218,B_222,C_219)
      | ~ v1_funct_1(E_218)
      | ~ m1_subset_1(D_220,k1_zfmisc_1(k2_zfmisc_1(A_221,B_222)))
      | ~ v1_funct_2(D_220,A_221,B_222)
      | ~ v1_funct_1(D_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_2810,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_1099,c_2806])).

tff(c_2815,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_84,c_82,c_80,c_92,c_78,c_2810])).

tff(c_2817,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2127,c_72,c_2815])).

tff(c_2819,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2082])).

tff(c_10,plain,(
    ! [A_8] : k1_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_95,plain,(
    ! [A_8] : k1_relat_1(k6_partfun1(A_8)) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_10])).

tff(c_2083,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1382])).

tff(c_2084,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2083,c_263])).

tff(c_2933,plain,(
    ! [A_226,C_227,B_228] :
      ( k6_partfun1(A_226) = k5_relat_1(C_227,k2_funct_1(C_227))
      | k1_xboole_0 = B_228
      | ~ v2_funct_1(C_227)
      | k2_relset_1(A_226,B_228,C_227) != B_228
      | ~ m1_subset_1(C_227,k1_zfmisc_1(k2_zfmisc_1(A_226,B_228)))
      | ~ v1_funct_2(C_227,A_226,B_228)
      | ~ v1_funct_1(C_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_2947,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_2933])).

tff(c_2970,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_2084,c_2819,c_2947])).

tff(c_2971,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2970])).

tff(c_163,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_80,c_157])).

tff(c_172,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_163])).

tff(c_64,plain,(
    ! [A_52] :
      ( v1_funct_2(A_52,k1_relat_1(A_52),k2_relat_1(A_52))
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_2102,plain,
    ( v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2083,c_64])).

tff(c_2119,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_84,c_2102])).

tff(c_298,plain,(
    ! [A_83] :
      ( m1_subset_1(A_83,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_83),k2_relat_1(A_83))))
      | ~ v1_funct_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_30,plain,(
    ! [A_17,B_18,C_19] :
      ( k2_relset_1(A_17,B_18,C_19) = k2_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_322,plain,(
    ! [A_83] :
      ( k2_relset_1(k1_relat_1(A_83),k2_relat_1(A_83),A_83) = k2_relat_1(A_83)
      | ~ v1_funct_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(resolution,[status(thm)],[c_298,c_30])).

tff(c_2093,plain,
    ( k2_relset_1(k1_relat_1('#skF_4'),'#skF_1','#skF_4') = k2_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2083,c_322])).

tff(c_2113,plain,(
    k2_relset_1(k1_relat_1('#skF_4'),'#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_84,c_2083,c_2093])).

tff(c_62,plain,(
    ! [A_52] :
      ( m1_subset_1(A_52,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_52),k2_relat_1(A_52))))
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_2099,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2083,c_62])).

tff(c_2117,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_84,c_2099])).

tff(c_2935,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1(k1_relat_1('#skF_4'))
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1(k1_relat_1('#skF_4'),'#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2117,c_2933])).

tff(c_2952,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1(k1_relat_1('#skF_4'))
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2119,c_2113,c_2819,c_2935])).

tff(c_2953,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1(k1_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2952])).

tff(c_2984,plain,(
    k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2971,c_2953])).

tff(c_3012,plain,(
    k1_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2984,c_95])).

tff(c_3029,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_3012])).

tff(c_28,plain,(
    ! [A_14,B_16] :
      ( k2_funct_1(A_14) = B_16
      | k6_relat_1(k2_relat_1(A_14)) != k5_relat_1(B_16,A_14)
      | k2_relat_1(B_16) != k1_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_91,plain,(
    ! [A_14,B_16] :
      ( k2_funct_1(A_14) = B_16
      | k6_partfun1(k2_relat_1(A_14)) != k5_relat_1(B_16,A_14)
      | k2_relat_1(B_16) != k1_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_28])).

tff(c_2087,plain,(
    ! [B_16] :
      ( k2_funct_1('#skF_4') = B_16
      | k5_relat_1(B_16,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_16) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2083,c_91])).

tff(c_2109,plain,(
    ! [B_16] :
      ( k2_funct_1('#skF_4') = B_16
      | k5_relat_1(B_16,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_16) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_84,c_2087])).

tff(c_10234,plain,(
    ! [B_402] :
      ( k2_funct_1('#skF_4') = B_402
      | k5_relat_1(B_402,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_402) != '#skF_2'
      | ~ v1_funct_1(B_402)
      | ~ v1_relat_1(B_402) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2819,c_3029,c_2109])).

tff(c_10372,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_175,c_10234])).

tff(c_10511,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_265,c_2871,c_10372])).

tff(c_16,plain,(
    ! [A_9] :
      ( v1_relat_1(k2_funct_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_226,plain,(
    ! [A_74] :
      ( k2_relat_1(k2_funct_1(A_74)) = k1_relat_1(A_74)
      | ~ v2_funct_1(A_74)
      | ~ v1_funct_1(A_74)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_8,plain,(
    ! [A_7] :
      ( k10_relat_1(A_7,k2_relat_1(A_7)) = k1_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4194,plain,(
    ! [A_277] :
      ( k10_relat_1(k2_funct_1(A_277),k1_relat_1(A_277)) = k1_relat_1(k2_funct_1(A_277))
      | ~ v1_relat_1(k2_funct_1(A_277))
      | ~ v2_funct_1(A_277)
      | ~ v1_funct_1(A_277)
      | ~ v1_relat_1(A_277) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_8])).

tff(c_4209,plain,
    ( k10_relat_1(k2_funct_1('#skF_4'),'#skF_2') = k1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3029,c_4194])).

tff(c_4223,plain,
    ( k10_relat_1(k2_funct_1('#skF_4'),'#skF_2') = k1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_84,c_2819,c_4209])).

tff(c_4448,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_4223])).

tff(c_4451,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_4448])).

tff(c_4455,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_84,c_4451])).

tff(c_4457,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4223])).

tff(c_14,plain,(
    ! [A_9] :
      ( v1_funct_1(k2_funct_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4510,plain,(
    ! [A_281] :
      ( v1_funct_2(k2_funct_1(A_281),k1_relat_1(k2_funct_1(A_281)),k1_relat_1(A_281))
      | ~ v1_funct_1(k2_funct_1(A_281))
      | ~ v1_relat_1(k2_funct_1(A_281))
      | ~ v2_funct_1(A_281)
      | ~ v1_funct_1(A_281)
      | ~ v1_relat_1(A_281) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_64])).

tff(c_4522,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3029,c_4510])).

tff(c_4539,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_84,c_2819,c_4457,c_4522])).

tff(c_4542,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_4539])).

tff(c_4545,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_4542])).

tff(c_4549,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_84,c_4545])).

tff(c_4551,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4539])).

tff(c_26,plain,(
    ! [A_13] :
      ( k1_relat_1(k2_funct_1(A_13)) = k2_relat_1(A_13)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4550,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_4539])).

tff(c_4555,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_2')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_4550])).

tff(c_4557,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_84,c_2819,c_2083,c_4555])).

tff(c_2105,plain,
    ( k10_relat_1('#skF_4','#skF_1') = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2083,c_8])).

tff(c_2121,plain,(
    k10_relat_1('#skF_4','#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_2105])).

tff(c_3091,plain,(
    k10_relat_1('#skF_4','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3029,c_2121])).

tff(c_211,plain,(
    ! [A_73] :
      ( k1_relat_1(k2_funct_1(A_73)) = k2_relat_1(A_73)
      | ~ v2_funct_1(A_73)
      | ~ v1_funct_1(A_73)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [A_6] :
      ( k9_relat_1(A_6,k1_relat_1(A_6)) = k2_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_220,plain,(
    ! [A_73] :
      ( k9_relat_1(k2_funct_1(A_73),k2_relat_1(A_73)) = k2_relat_1(k2_funct_1(A_73))
      | ~ v1_relat_1(k2_funct_1(A_73))
      | ~ v2_funct_1(A_73)
      | ~ v1_funct_1(A_73)
      | ~ v1_relat_1(A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_6])).

tff(c_2090,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_1') = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2083,c_220])).

tff(c_2111,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_1') = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_84,c_2090])).

tff(c_4608,plain,(
    k9_relat_1(k2_funct_1('#skF_4'),'#skF_1') = k2_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2819,c_4457,c_2111])).

tff(c_22,plain,(
    ! [B_12,A_11] :
      ( k9_relat_1(k2_funct_1(B_12),A_11) = k10_relat_1(B_12,A_11)
      | ~ v2_funct_1(B_12)
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4612,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = k10_relat_1('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4608,c_22])).

tff(c_4619,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_84,c_2819,c_3091,c_4612])).

tff(c_4638,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_2')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4619,c_62])).

tff(c_4662,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4457,c_4551,c_4638])).

tff(c_4741,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'),'#skF_2')))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_4662])).

tff(c_4778,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_84,c_2819,c_2083,c_4741])).

tff(c_4632,plain,
    ( k2_relset_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_2',k2_funct_1('#skF_4')) = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4619,c_322])).

tff(c_4658,plain,(
    k2_relset_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_2',k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4457,c_4551,c_4619,c_4632])).

tff(c_4699,plain,
    ( k2_relset_1(k2_relat_1('#skF_4'),'#skF_2',k2_funct_1('#skF_4')) = '#skF_2'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_4658])).

tff(c_4703,plain,(
    k2_relset_1('#skF_1','#skF_2',k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_84,c_2819,c_2083,c_4699])).

tff(c_2818,plain,(
    k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2082])).

tff(c_1286,plain,(
    ! [A_138,B_136,E_137] :
      ( k1_partfun1(A_138,B_136,'#skF_2','#skF_1',E_137,'#skF_4') = k5_relat_1(E_137,'#skF_4')
      | ~ m1_subset_1(E_137,k1_zfmisc_1(k2_zfmisc_1(A_138,B_136)))
      | ~ v1_funct_1(E_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1270])).

tff(c_4788,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1',k2_funct_1('#skF_4'),'#skF_4') = k5_relat_1(k2_funct_1('#skF_4'),'#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4778,c_1286])).

tff(c_4821,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1',k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4551,c_2818,c_4788])).

tff(c_56,plain,(
    ! [E_48,D_46,C_45,A_43,B_44] :
      ( k1_xboole_0 = C_45
      | v2_funct_1(D_46)
      | k2_relset_1(A_43,B_44,D_46) != B_44
      | ~ v2_funct_1(k1_partfun1(A_43,B_44,B_44,C_45,D_46,E_48))
      | ~ m1_subset_1(E_48,k1_zfmisc_1(k2_zfmisc_1(B_44,C_45)))
      | ~ v1_funct_2(E_48,B_44,C_45)
      | ~ v1_funct_1(E_48)
      | ~ m1_subset_1(D_46,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44)))
      | ~ v1_funct_2(D_46,A_43,B_44)
      | ~ v1_funct_1(D_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_4913,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_1','#skF_2',k2_funct_1('#skF_4')) != '#skF_2'
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_1','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4821,c_56])).

tff(c_4925,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4551,c_4557,c_4778,c_84,c_82,c_80,c_92,c_4703,c_4913])).

tff(c_4926,plain,(
    v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_4925])).

tff(c_70,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_60,plain,(
    ! [A_49,C_51,B_50] :
      ( k6_partfun1(A_49) = k5_relat_1(C_51,k2_funct_1(C_51))
      | k1_xboole_0 = B_50
      | ~ v2_funct_1(C_51)
      | k2_relset_1(A_49,B_50,C_51) != B_50
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50)))
      | ~ v1_funct_2(C_51,A_49,B_50)
      | ~ v1_funct_1(C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_4785,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),k2_funct_1(k2_funct_1('#skF_4'))) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_1','#skF_2',k2_funct_1('#skF_4')) != '#skF_2'
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_1','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4778,c_60])).

tff(c_4817,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),k2_funct_1(k2_funct_1('#skF_4'))) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4551,c_4557,c_4703,c_4785])).

tff(c_4818,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),k2_funct_1(k2_funct_1('#skF_4'))) = k6_partfun1('#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_4817])).

tff(c_4954,plain,(
    k5_relat_1(k2_funct_1('#skF_4'),k2_funct_1(k2_funct_1('#skF_4'))) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4926,c_4818])).

tff(c_4715,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),k2_funct_1(k2_funct_1('#skF_4'))) = k6_partfun1(k1_relat_1(k2_funct_1('#skF_4')))
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_2',k2_funct_1('#skF_4')) != '#skF_2'
    | ~ v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4662,c_60])).

tff(c_4750,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),k2_funct_1(k2_funct_1('#skF_4'))) = k6_partfun1(k1_relat_1(k2_funct_1('#skF_4')))
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4551,c_4550,c_4658,c_4715])).

tff(c_4751,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),k2_funct_1(k2_funct_1('#skF_4'))) = k6_partfun1(k1_relat_1(k2_funct_1('#skF_4')))
    | ~ v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_4750])).

tff(c_5053,plain,(
    k6_partfun1(k1_relat_1(k2_funct_1('#skF_4'))) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4926,c_4954,c_4751])).

tff(c_5099,plain,(
    k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5053,c_95])).

tff(c_5133,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_5099])).

tff(c_24,plain,(
    ! [A_13] :
      ( k2_relat_1(k2_funct_1(A_13)) = k1_relat_1(A_13)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_493,plain,(
    ! [A_93,B_94] :
      ( k2_funct_1(A_93) = B_94
      | k6_partfun1(k2_relat_1(A_93)) != k5_relat_1(B_94,A_93)
      | k2_relat_1(B_94) != k1_relat_1(A_93)
      | ~ v2_funct_1(A_93)
      | ~ v1_funct_1(B_94)
      | ~ v1_relat_1(B_94)
      | ~ v1_funct_1(A_93)
      | ~ v1_relat_1(A_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_28])).

tff(c_6687,plain,(
    ! [A_341,B_342] :
      ( k2_funct_1(k2_funct_1(A_341)) = B_342
      | k5_relat_1(B_342,k2_funct_1(A_341)) != k6_partfun1(k1_relat_1(A_341))
      | k2_relat_1(B_342) != k1_relat_1(k2_funct_1(A_341))
      | ~ v2_funct_1(k2_funct_1(A_341))
      | ~ v1_funct_1(B_342)
      | ~ v1_relat_1(B_342)
      | ~ v1_funct_1(k2_funct_1(A_341))
      | ~ v1_relat_1(k2_funct_1(A_341))
      | ~ v2_funct_1(A_341)
      | ~ v1_funct_1(A_341)
      | ~ v1_relat_1(A_341) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_493])).

tff(c_6705,plain,
    ( k2_funct_1(k2_funct_1('#skF_4')) = '#skF_4'
    | k6_partfun1(k1_relat_1('#skF_4')) != k6_partfun1('#skF_2')
    | k1_relat_1(k2_funct_1('#skF_4')) != k2_relat_1('#skF_4')
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2971,c_6687])).

tff(c_6725,plain,(
    k2_funct_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_84,c_2819,c_4457,c_4551,c_172,c_84,c_4926,c_2083,c_5133,c_3029,c_6705])).

tff(c_10528,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10511,c_6725])).

tff(c_10561,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_10528])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:10:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.03/3.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.20/3.68  
% 10.20/3.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.20/3.68  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.20/3.68  
% 10.20/3.68  %Foreground sorts:
% 10.20/3.68  
% 10.20/3.68  
% 10.20/3.68  %Background operators:
% 10.20/3.68  
% 10.20/3.68  
% 10.20/3.68  %Foreground operators:
% 10.20/3.68  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.20/3.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.20/3.68  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 10.20/3.68  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.20/3.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.20/3.68  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 10.20/3.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.20/3.68  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 10.20/3.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.20/3.68  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.20/3.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.20/3.68  tff('#skF_2', type, '#skF_2': $i).
% 10.20/3.68  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 10.20/3.68  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 10.20/3.68  tff('#skF_3', type, '#skF_3': $i).
% 10.20/3.68  tff('#skF_1', type, '#skF_1': $i).
% 10.20/3.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.20/3.68  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 10.20/3.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.20/3.68  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 10.20/3.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.20/3.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.20/3.68  tff('#skF_4', type, '#skF_4': $i).
% 10.20/3.68  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 10.20/3.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.20/3.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.20/3.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.20/3.68  
% 10.20/3.71  tff(f_228, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 10.20/3.71  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.20/3.71  tff(f_117, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 10.20/3.71  tff(f_121, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 10.20/3.71  tff(f_105, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 10.20/3.71  tff(f_131, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 10.20/3.71  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 10.20/3.71  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 10.20/3.71  tff(f_192, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 10.20/3.71  tff(f_150, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 10.20/3.71  tff(f_133, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 10.20/3.71  tff(f_58, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 10.20/3.71  tff(f_176, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 10.20/3.71  tff(f_46, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 10.20/3.71  tff(f_202, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 10.20/3.71  tff(f_93, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 10.20/3.71  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 10.20/3.71  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 10.20/3.71  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 10.20/3.71  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 10.20/3.71  tff(f_66, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 10.20/3.71  tff(c_68, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_228])).
% 10.20/3.71  tff(c_90, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_228])).
% 10.20/3.71  tff(c_78, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_228])).
% 10.20/3.71  tff(c_86, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_228])).
% 10.20/3.71  tff(c_251, plain, (![A_78, B_79, C_80]: (k2_relset_1(A_78, B_79, C_80)=k2_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.20/3.71  tff(c_260, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_251])).
% 10.20/3.71  tff(c_265, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_260])).
% 10.20/3.71  tff(c_84, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_228])).
% 10.20/3.71  tff(c_80, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_228])).
% 10.20/3.71  tff(c_1065, plain, (![A_124, B_121, E_122, F_123, D_125, C_120]: (m1_subset_1(k1_partfun1(A_124, B_121, C_120, D_125, E_122, F_123), k1_zfmisc_1(k2_zfmisc_1(A_124, D_125))) | ~m1_subset_1(F_123, k1_zfmisc_1(k2_zfmisc_1(C_120, D_125))) | ~v1_funct_1(F_123) | ~m1_subset_1(E_122, k1_zfmisc_1(k2_zfmisc_1(A_124, B_121))) | ~v1_funct_1(E_122))), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.20/3.71  tff(c_42, plain, (![A_30]: (m1_subset_1(k6_partfun1(A_30), k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.20/3.71  tff(c_76, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_228])).
% 10.20/3.71  tff(c_368, plain, (![D_86, C_87, A_88, B_89]: (D_86=C_87 | ~r2_relset_1(A_88, B_89, C_87, D_86) | ~m1_subset_1(D_86, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 10.20/3.71  tff(c_378, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_76, c_368])).
% 10.20/3.71  tff(c_397, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_378])).
% 10.20/3.71  tff(c_569, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_397])).
% 10.20/3.71  tff(c_1077, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1065, c_569])).
% 10.20/3.71  tff(c_1098, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_84, c_80, c_1077])).
% 10.20/3.71  tff(c_1099, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_397])).
% 10.20/3.71  tff(c_1258, plain, (![C_140, A_138, B_136, E_137, F_139, D_135]: (k1_partfun1(A_138, B_136, C_140, D_135, E_137, F_139)=k5_relat_1(E_137, F_139) | ~m1_subset_1(F_139, k1_zfmisc_1(k2_zfmisc_1(C_140, D_135))) | ~v1_funct_1(F_139) | ~m1_subset_1(E_137, k1_zfmisc_1(k2_zfmisc_1(A_138, B_136))) | ~v1_funct_1(E_137))), inference(cnfTransformation, [status(thm)], [f_131])).
% 10.20/3.71  tff(c_1270, plain, (![A_138, B_136, E_137]: (k1_partfun1(A_138, B_136, '#skF_2', '#skF_1', E_137, '#skF_4')=k5_relat_1(E_137, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_137, k1_zfmisc_1(k2_zfmisc_1(A_138, B_136))) | ~v1_funct_1(E_137))), inference(resolution, [status(thm)], [c_80, c_1258])).
% 10.20/3.71  tff(c_2833, plain, (![A_223, B_224, E_225]: (k1_partfun1(A_223, B_224, '#skF_2', '#skF_1', E_225, '#skF_4')=k5_relat_1(E_225, '#skF_4') | ~m1_subset_1(E_225, k1_zfmisc_1(k2_zfmisc_1(A_223, B_224))) | ~v1_funct_1(E_225))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_1270])).
% 10.20/3.71  tff(c_2854, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_2833])).
% 10.20/3.71  tff(c_2871, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_1099, c_2854])).
% 10.20/3.71  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.20/3.71  tff(c_157, plain, (![B_67, A_68]: (v1_relat_1(B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(A_68)) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.20/3.71  tff(c_166, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_86, c_157])).
% 10.20/3.71  tff(c_175, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_166])).
% 10.20/3.71  tff(c_72, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_228])).
% 10.20/3.71  tff(c_82, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_228])).
% 10.20/3.71  tff(c_263, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_80, c_251])).
% 10.20/3.71  tff(c_1350, plain, (![B_145, C_146, A_147]: (k6_partfun1(B_145)=k5_relat_1(k2_funct_1(C_146), C_146) | k1_xboole_0=B_145 | ~v2_funct_1(C_146) | k2_relset_1(A_147, B_145, C_146)!=B_145 | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_147, B_145))) | ~v1_funct_2(C_146, A_147, B_145) | ~v1_funct_1(C_146))), inference(cnfTransformation, [status(thm)], [f_192])).
% 10.20/3.71  tff(c_1362, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_80, c_1350])).
% 10.20/3.71  tff(c_1381, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_263, c_1362])).
% 10.20/3.71  tff(c_1382, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_72, c_1381])).
% 10.20/3.71  tff(c_1397, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_1382])).
% 10.20/3.71  tff(c_88, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_228])).
% 10.20/3.71  tff(c_241, plain, (![A_75, B_76, D_77]: (r2_relset_1(A_75, B_76, D_77, D_77) | ~m1_subset_1(D_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 10.20/3.71  tff(c_248, plain, (![A_30]: (r2_relset_1(A_30, A_30, k6_partfun1(A_30), k6_partfun1(A_30)))), inference(resolution, [status(thm)], [c_42, c_241])).
% 10.20/3.71  tff(c_2074, plain, (![A_182, B_183, C_184, D_185]: (k2_relset_1(A_182, B_183, C_184)=B_183 | ~r2_relset_1(B_183, B_183, k1_partfun1(B_183, A_182, A_182, B_183, D_185, C_184), k6_partfun1(B_183)) | ~m1_subset_1(D_185, k1_zfmisc_1(k2_zfmisc_1(B_183, A_182))) | ~v1_funct_2(D_185, B_183, A_182) | ~v1_funct_1(D_185) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_182, B_183))) | ~v1_funct_2(C_184, A_182, B_183) | ~v1_funct_1(C_184))), inference(cnfTransformation, [status(thm)], [f_150])).
% 10.20/3.71  tff(c_2077, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1099, c_2074])).
% 10.20/3.71  tff(c_2079, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_90, c_88, c_86, c_248, c_263, c_2077])).
% 10.20/3.71  tff(c_2081, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1397, c_2079])).
% 10.20/3.71  tff(c_2082, plain, (~v2_funct_1('#skF_4') | k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1382])).
% 10.20/3.71  tff(c_2127, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_2082])).
% 10.20/3.71  tff(c_46, plain, (![A_37]: (k6_relat_1(A_37)=k6_partfun1(A_37))), inference(cnfTransformation, [status(thm)], [f_133])).
% 10.20/3.71  tff(c_20, plain, (![A_10]: (v2_funct_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.20/3.71  tff(c_92, plain, (![A_10]: (v2_funct_1(k6_partfun1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_20])).
% 10.20/3.71  tff(c_2806, plain, (![D_220, B_222, A_221, E_218, C_219]: (k1_xboole_0=C_219 | v2_funct_1(E_218) | k2_relset_1(A_221, B_222, D_220)!=B_222 | ~v2_funct_1(k1_partfun1(A_221, B_222, B_222, C_219, D_220, E_218)) | ~m1_subset_1(E_218, k1_zfmisc_1(k2_zfmisc_1(B_222, C_219))) | ~v1_funct_2(E_218, B_222, C_219) | ~v1_funct_1(E_218) | ~m1_subset_1(D_220, k1_zfmisc_1(k2_zfmisc_1(A_221, B_222))) | ~v1_funct_2(D_220, A_221, B_222) | ~v1_funct_1(D_220))), inference(cnfTransformation, [status(thm)], [f_176])).
% 10.20/3.71  tff(c_2810, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1099, c_2806])).
% 10.20/3.71  tff(c_2815, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_84, c_82, c_80, c_92, c_78, c_2810])).
% 10.20/3.71  tff(c_2817, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2127, c_72, c_2815])).
% 10.20/3.71  tff(c_2819, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_2082])).
% 10.20/3.71  tff(c_10, plain, (![A_8]: (k1_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.20/3.71  tff(c_95, plain, (![A_8]: (k1_relat_1(k6_partfun1(A_8))=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_10])).
% 10.20/3.71  tff(c_2083, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_1382])).
% 10.20/3.71  tff(c_2084, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2083, c_263])).
% 10.20/3.71  tff(c_2933, plain, (![A_226, C_227, B_228]: (k6_partfun1(A_226)=k5_relat_1(C_227, k2_funct_1(C_227)) | k1_xboole_0=B_228 | ~v2_funct_1(C_227) | k2_relset_1(A_226, B_228, C_227)!=B_228 | ~m1_subset_1(C_227, k1_zfmisc_1(k2_zfmisc_1(A_226, B_228))) | ~v1_funct_2(C_227, A_226, B_228) | ~v1_funct_1(C_227))), inference(cnfTransformation, [status(thm)], [f_192])).
% 10.20/3.71  tff(c_2947, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_80, c_2933])).
% 10.20/3.71  tff(c_2970, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_2084, c_2819, c_2947])).
% 10.20/3.71  tff(c_2971, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_72, c_2970])).
% 10.20/3.71  tff(c_163, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_80, c_157])).
% 10.20/3.71  tff(c_172, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_163])).
% 10.20/3.71  tff(c_64, plain, (![A_52]: (v1_funct_2(A_52, k1_relat_1(A_52), k2_relat_1(A_52)) | ~v1_funct_1(A_52) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_202])).
% 10.20/3.71  tff(c_2102, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_1') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2083, c_64])).
% 10.20/3.71  tff(c_2119, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_172, c_84, c_2102])).
% 10.20/3.71  tff(c_298, plain, (![A_83]: (m1_subset_1(A_83, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_83), k2_relat_1(A_83)))) | ~v1_funct_1(A_83) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_202])).
% 10.20/3.71  tff(c_30, plain, (![A_17, B_18, C_19]: (k2_relset_1(A_17, B_18, C_19)=k2_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.20/3.71  tff(c_322, plain, (![A_83]: (k2_relset_1(k1_relat_1(A_83), k2_relat_1(A_83), A_83)=k2_relat_1(A_83) | ~v1_funct_1(A_83) | ~v1_relat_1(A_83))), inference(resolution, [status(thm)], [c_298, c_30])).
% 10.20/3.71  tff(c_2093, plain, (k2_relset_1(k1_relat_1('#skF_4'), '#skF_1', '#skF_4')=k2_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2083, c_322])).
% 10.20/3.71  tff(c_2113, plain, (k2_relset_1(k1_relat_1('#skF_4'), '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_172, c_84, c_2083, c_2093])).
% 10.20/3.71  tff(c_62, plain, (![A_52]: (m1_subset_1(A_52, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_52), k2_relat_1(A_52)))) | ~v1_funct_1(A_52) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_202])).
% 10.20/3.71  tff(c_2099, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_1'))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2083, c_62])).
% 10.20/3.71  tff(c_2117, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_84, c_2099])).
% 10.20/3.71  tff(c_2935, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1(k1_relat_1('#skF_4')) | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1(k1_relat_1('#skF_4'), '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_2117, c_2933])).
% 10.20/3.71  tff(c_2952, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1(k1_relat_1('#skF_4')) | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_2119, c_2113, c_2819, c_2935])).
% 10.20/3.71  tff(c_2953, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1(k1_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_72, c_2952])).
% 10.20/3.71  tff(c_2984, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2971, c_2953])).
% 10.20/3.71  tff(c_3012, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2984, c_95])).
% 10.20/3.71  tff(c_3029, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_95, c_3012])).
% 10.20/3.71  tff(c_28, plain, (![A_14, B_16]: (k2_funct_1(A_14)=B_16 | k6_relat_1(k2_relat_1(A_14))!=k5_relat_1(B_16, A_14) | k2_relat_1(B_16)!=k1_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.20/3.71  tff(c_91, plain, (![A_14, B_16]: (k2_funct_1(A_14)=B_16 | k6_partfun1(k2_relat_1(A_14))!=k5_relat_1(B_16, A_14) | k2_relat_1(B_16)!=k1_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_28])).
% 10.20/3.71  tff(c_2087, plain, (![B_16]: (k2_funct_1('#skF_4')=B_16 | k5_relat_1(B_16, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_16)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_16) | ~v1_relat_1(B_16) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2083, c_91])).
% 10.20/3.71  tff(c_2109, plain, (![B_16]: (k2_funct_1('#skF_4')=B_16 | k5_relat_1(B_16, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_16)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_16) | ~v1_relat_1(B_16))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_84, c_2087])).
% 10.20/3.71  tff(c_10234, plain, (![B_402]: (k2_funct_1('#skF_4')=B_402 | k5_relat_1(B_402, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_402)!='#skF_2' | ~v1_funct_1(B_402) | ~v1_relat_1(B_402))), inference(demodulation, [status(thm), theory('equality')], [c_2819, c_3029, c_2109])).
% 10.20/3.71  tff(c_10372, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_175, c_10234])).
% 10.20/3.71  tff(c_10511, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_265, c_2871, c_10372])).
% 10.20/3.71  tff(c_16, plain, (![A_9]: (v1_relat_1(k2_funct_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.20/3.71  tff(c_226, plain, (![A_74]: (k2_relat_1(k2_funct_1(A_74))=k1_relat_1(A_74) | ~v2_funct_1(A_74) | ~v1_funct_1(A_74) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.20/3.71  tff(c_8, plain, (![A_7]: (k10_relat_1(A_7, k2_relat_1(A_7))=k1_relat_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.20/3.71  tff(c_4194, plain, (![A_277]: (k10_relat_1(k2_funct_1(A_277), k1_relat_1(A_277))=k1_relat_1(k2_funct_1(A_277)) | ~v1_relat_1(k2_funct_1(A_277)) | ~v2_funct_1(A_277) | ~v1_funct_1(A_277) | ~v1_relat_1(A_277))), inference(superposition, [status(thm), theory('equality')], [c_226, c_8])).
% 10.20/3.71  tff(c_4209, plain, (k10_relat_1(k2_funct_1('#skF_4'), '#skF_2')=k1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3029, c_4194])).
% 10.20/3.71  tff(c_4223, plain, (k10_relat_1(k2_funct_1('#skF_4'), '#skF_2')=k1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_84, c_2819, c_4209])).
% 10.20/3.71  tff(c_4448, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_4223])).
% 10.20/3.71  tff(c_4451, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_4448])).
% 10.20/3.71  tff(c_4455, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_172, c_84, c_4451])).
% 10.20/3.71  tff(c_4457, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_4223])).
% 10.20/3.71  tff(c_14, plain, (![A_9]: (v1_funct_1(k2_funct_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.20/3.71  tff(c_4510, plain, (![A_281]: (v1_funct_2(k2_funct_1(A_281), k1_relat_1(k2_funct_1(A_281)), k1_relat_1(A_281)) | ~v1_funct_1(k2_funct_1(A_281)) | ~v1_relat_1(k2_funct_1(A_281)) | ~v2_funct_1(A_281) | ~v1_funct_1(A_281) | ~v1_relat_1(A_281))), inference(superposition, [status(thm), theory('equality')], [c_226, c_64])).
% 10.20/3.71  tff(c_4522, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3029, c_4510])).
% 10.20/3.71  tff(c_4539, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_84, c_2819, c_4457, c_4522])).
% 10.20/3.71  tff(c_4542, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_4539])).
% 10.20/3.71  tff(c_4545, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_4542])).
% 10.20/3.71  tff(c_4549, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_172, c_84, c_4545])).
% 10.20/3.71  tff(c_4551, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_4539])).
% 10.20/3.71  tff(c_26, plain, (![A_13]: (k1_relat_1(k2_funct_1(A_13))=k2_relat_1(A_13) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.20/3.71  tff(c_4550, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_2')), inference(splitRight, [status(thm)], [c_4539])).
% 10.20/3.71  tff(c_4555, plain, (v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_2') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_26, c_4550])).
% 10.20/3.71  tff(c_4557, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_172, c_84, c_2819, c_2083, c_4555])).
% 10.20/3.71  tff(c_2105, plain, (k10_relat_1('#skF_4', '#skF_1')=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2083, c_8])).
% 10.20/3.71  tff(c_2121, plain, (k10_relat_1('#skF_4', '#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_172, c_2105])).
% 10.20/3.71  tff(c_3091, plain, (k10_relat_1('#skF_4', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3029, c_2121])).
% 10.20/3.71  tff(c_211, plain, (![A_73]: (k1_relat_1(k2_funct_1(A_73))=k2_relat_1(A_73) | ~v2_funct_1(A_73) | ~v1_funct_1(A_73) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.20/3.71  tff(c_6, plain, (![A_6]: (k9_relat_1(A_6, k1_relat_1(A_6))=k2_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.20/3.71  tff(c_220, plain, (![A_73]: (k9_relat_1(k2_funct_1(A_73), k2_relat_1(A_73))=k2_relat_1(k2_funct_1(A_73)) | ~v1_relat_1(k2_funct_1(A_73)) | ~v2_funct_1(A_73) | ~v1_funct_1(A_73) | ~v1_relat_1(A_73))), inference(superposition, [status(thm), theory('equality')], [c_211, c_6])).
% 10.20/3.71  tff(c_2090, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_1')=k2_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2083, c_220])).
% 10.20/3.71  tff(c_2111, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_1')=k2_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_172, c_84, c_2090])).
% 10.20/3.71  tff(c_4608, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_1')=k2_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2819, c_4457, c_2111])).
% 10.20/3.71  tff(c_22, plain, (![B_12, A_11]: (k9_relat_1(k2_funct_1(B_12), A_11)=k10_relat_1(B_12, A_11) | ~v2_funct_1(B_12) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.20/3.71  tff(c_4612, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k10_relat_1('#skF_4', '#skF_1') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4608, c_22])).
% 10.20/3.71  tff(c_4619, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_172, c_84, c_2819, c_3091, c_4612])).
% 10.20/3.71  tff(c_4638, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_2'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4619, c_62])).
% 10.20/3.71  tff(c_4662, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4457, c_4551, c_4638])).
% 10.20/3.71  tff(c_4741, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'), '#skF_2'))) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_26, c_4662])).
% 10.20/3.71  tff(c_4778, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_84, c_2819, c_2083, c_4741])).
% 10.20/3.71  tff(c_4632, plain, (k2_relset_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_2', k2_funct_1('#skF_4'))=k2_relat_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4619, c_322])).
% 10.20/3.71  tff(c_4658, plain, (k2_relset_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_2', k2_funct_1('#skF_4'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4457, c_4551, c_4619, c_4632])).
% 10.20/3.71  tff(c_4699, plain, (k2_relset_1(k2_relat_1('#skF_4'), '#skF_2', k2_funct_1('#skF_4'))='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_26, c_4658])).
% 10.20/3.71  tff(c_4703, plain, (k2_relset_1('#skF_1', '#skF_2', k2_funct_1('#skF_4'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_172, c_84, c_2819, c_2083, c_4699])).
% 10.20/3.71  tff(c_2818, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2082])).
% 10.20/3.71  tff(c_1286, plain, (![A_138, B_136, E_137]: (k1_partfun1(A_138, B_136, '#skF_2', '#skF_1', E_137, '#skF_4')=k5_relat_1(E_137, '#skF_4') | ~m1_subset_1(E_137, k1_zfmisc_1(k2_zfmisc_1(A_138, B_136))) | ~v1_funct_1(E_137))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_1270])).
% 10.20/3.71  tff(c_4788, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', k2_funct_1('#skF_4'), '#skF_4')=k5_relat_1(k2_funct_1('#skF_4'), '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_4778, c_1286])).
% 10.20/3.71  tff(c_4821, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4551, c_2818, c_4788])).
% 10.20/3.71  tff(c_56, plain, (![E_48, D_46, C_45, A_43, B_44]: (k1_xboole_0=C_45 | v2_funct_1(D_46) | k2_relset_1(A_43, B_44, D_46)!=B_44 | ~v2_funct_1(k1_partfun1(A_43, B_44, B_44, C_45, D_46, E_48)) | ~m1_subset_1(E_48, k1_zfmisc_1(k2_zfmisc_1(B_44, C_45))) | ~v1_funct_2(E_48, B_44, C_45) | ~v1_funct_1(E_48) | ~m1_subset_1(D_46, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))) | ~v1_funct_2(D_46, A_43, B_44) | ~v1_funct_1(D_46))), inference(cnfTransformation, [status(thm)], [f_176])).
% 10.20/3.71  tff(c_4913, plain, (k1_xboole_0='#skF_1' | v2_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_1', '#skF_2', k2_funct_1('#skF_4'))!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_1', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4821, c_56])).
% 10.20/3.71  tff(c_4925, plain, (k1_xboole_0='#skF_1' | v2_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4551, c_4557, c_4778, c_84, c_82, c_80, c_92, c_4703, c_4913])).
% 10.20/3.71  tff(c_4926, plain, (v2_funct_1(k2_funct_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_72, c_4925])).
% 10.20/3.71  tff(c_70, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_228])).
% 10.20/3.71  tff(c_60, plain, (![A_49, C_51, B_50]: (k6_partfun1(A_49)=k5_relat_1(C_51, k2_funct_1(C_51)) | k1_xboole_0=B_50 | ~v2_funct_1(C_51) | k2_relset_1(A_49, B_50, C_51)!=B_50 | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))) | ~v1_funct_2(C_51, A_49, B_50) | ~v1_funct_1(C_51))), inference(cnfTransformation, [status(thm)], [f_192])).
% 10.20/3.71  tff(c_4785, plain, (k5_relat_1(k2_funct_1('#skF_4'), k2_funct_1(k2_funct_1('#skF_4')))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_1', '#skF_2', k2_funct_1('#skF_4'))!='#skF_2' | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_1', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_4778, c_60])).
% 10.20/3.71  tff(c_4817, plain, (k5_relat_1(k2_funct_1('#skF_4'), k2_funct_1(k2_funct_1('#skF_4')))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4551, c_4557, c_4703, c_4785])).
% 10.20/3.71  tff(c_4818, plain, (k5_relat_1(k2_funct_1('#skF_4'), k2_funct_1(k2_funct_1('#skF_4')))=k6_partfun1('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_70, c_4817])).
% 10.20/3.71  tff(c_4954, plain, (k5_relat_1(k2_funct_1('#skF_4'), k2_funct_1(k2_funct_1('#skF_4')))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4926, c_4818])).
% 10.20/3.71  tff(c_4715, plain, (k5_relat_1(k2_funct_1('#skF_4'), k2_funct_1(k2_funct_1('#skF_4')))=k6_partfun1(k1_relat_1(k2_funct_1('#skF_4'))) | k1_xboole_0='#skF_2' | ~v2_funct_1(k2_funct_1('#skF_4')) | k2_relset_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_2', k2_funct_1('#skF_4'))!='#skF_2' | ~v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_4662, c_60])).
% 10.20/3.71  tff(c_4750, plain, (k5_relat_1(k2_funct_1('#skF_4'), k2_funct_1(k2_funct_1('#skF_4')))=k6_partfun1(k1_relat_1(k2_funct_1('#skF_4'))) | k1_xboole_0='#skF_2' | ~v2_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4551, c_4550, c_4658, c_4715])).
% 10.20/3.71  tff(c_4751, plain, (k5_relat_1(k2_funct_1('#skF_4'), k2_funct_1(k2_funct_1('#skF_4')))=k6_partfun1(k1_relat_1(k2_funct_1('#skF_4'))) | ~v2_funct_1(k2_funct_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_70, c_4750])).
% 10.20/3.71  tff(c_5053, plain, (k6_partfun1(k1_relat_1(k2_funct_1('#skF_4')))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4926, c_4954, c_4751])).
% 10.20/3.71  tff(c_5099, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5053, c_95])).
% 10.20/3.71  tff(c_5133, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_95, c_5099])).
% 10.20/3.71  tff(c_24, plain, (![A_13]: (k2_relat_1(k2_funct_1(A_13))=k1_relat_1(A_13) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.20/3.71  tff(c_493, plain, (![A_93, B_94]: (k2_funct_1(A_93)=B_94 | k6_partfun1(k2_relat_1(A_93))!=k5_relat_1(B_94, A_93) | k2_relat_1(B_94)!=k1_relat_1(A_93) | ~v2_funct_1(A_93) | ~v1_funct_1(B_94) | ~v1_relat_1(B_94) | ~v1_funct_1(A_93) | ~v1_relat_1(A_93))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_28])).
% 10.20/3.71  tff(c_6687, plain, (![A_341, B_342]: (k2_funct_1(k2_funct_1(A_341))=B_342 | k5_relat_1(B_342, k2_funct_1(A_341))!=k6_partfun1(k1_relat_1(A_341)) | k2_relat_1(B_342)!=k1_relat_1(k2_funct_1(A_341)) | ~v2_funct_1(k2_funct_1(A_341)) | ~v1_funct_1(B_342) | ~v1_relat_1(B_342) | ~v1_funct_1(k2_funct_1(A_341)) | ~v1_relat_1(k2_funct_1(A_341)) | ~v2_funct_1(A_341) | ~v1_funct_1(A_341) | ~v1_relat_1(A_341))), inference(superposition, [status(thm), theory('equality')], [c_24, c_493])).
% 10.20/3.71  tff(c_6705, plain, (k2_funct_1(k2_funct_1('#skF_4'))='#skF_4' | k6_partfun1(k1_relat_1('#skF_4'))!=k6_partfun1('#skF_2') | k1_relat_1(k2_funct_1('#skF_4'))!=k2_relat_1('#skF_4') | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2971, c_6687])).
% 10.20/3.71  tff(c_6725, plain, (k2_funct_1(k2_funct_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_172, c_84, c_2819, c_4457, c_4551, c_172, c_84, c_4926, c_2083, c_5133, c_3029, c_6705])).
% 10.20/3.71  tff(c_10528, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10511, c_6725])).
% 10.20/3.71  tff(c_10561, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_10528])).
% 10.20/3.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.20/3.71  
% 10.20/3.71  Inference rules
% 10.20/3.71  ----------------------
% 10.20/3.71  #Ref     : 0
% 10.20/3.71  #Sup     : 2171
% 10.20/3.71  #Fact    : 0
% 10.20/3.71  #Define  : 0
% 10.20/3.71  #Split   : 35
% 10.20/3.71  #Chain   : 0
% 10.20/3.71  #Close   : 0
% 10.20/3.71  
% 10.20/3.71  Ordering : KBO
% 10.20/3.71  
% 10.20/3.71  Simplification rules
% 10.20/3.71  ----------------------
% 10.20/3.71  #Subsume      : 122
% 10.20/3.71  #Demod        : 5457
% 10.20/3.71  #Tautology    : 993
% 10.20/3.71  #SimpNegUnit  : 240
% 10.20/3.71  #BackRed      : 166
% 10.20/3.71  
% 10.20/3.71  #Partial instantiations: 0
% 10.20/3.71  #Strategies tried      : 1
% 10.20/3.71  
% 10.20/3.71  Timing (in seconds)
% 10.20/3.72  ----------------------
% 10.20/3.72  Preprocessing        : 0.41
% 10.20/3.72  Parsing              : 0.21
% 10.20/3.72  CNF conversion       : 0.03
% 10.20/3.72  Main loop            : 2.51
% 10.20/3.72  Inferencing          : 0.63
% 10.20/3.72  Reduction            : 1.23
% 10.20/3.72  Demodulation         : 1.00
% 10.20/3.72  BG Simplification    : 0.07
% 10.20/3.72  Subsumption          : 0.43
% 10.20/3.72  Abstraction          : 0.09
% 10.20/3.72  MUC search           : 0.00
% 10.20/3.72  Cooper               : 0.00
% 10.20/3.72  Total                : 2.98
% 10.20/3.72  Index Insertion      : 0.00
% 10.20/3.72  Index Deletion       : 0.00
% 10.20/3.72  Index Matching       : 0.00
% 10.20/3.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
