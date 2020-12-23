%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:55 EST 2020

% Result     : Theorem 18.85s
% Output     : CNFRefutation 18.94s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 418 expanded)
%              Number of leaves         :   50 ( 175 expanded)
%              Depth                    :   13
%              Number of atoms          :  281 (1672 expanded)
%              Number of equality atoms :   96 ( 546 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_122,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_164,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_61,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_108,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_148,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_152,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_136,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_162,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_128,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_118,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
          & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_98,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
           => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(c_70,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_82,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_168,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_180,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_168])).

tff(c_88,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_179,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_168])).

tff(c_92,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_76,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_290,plain,(
    ! [A_88] :
      ( k4_relat_1(A_88) = k2_funct_1(A_88)
      | ~ v2_funct_1(A_88)
      | ~ v1_funct_1(A_88)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_293,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_290])).

tff(c_296,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_92,c_293])).

tff(c_12,plain,(
    ! [A_5] :
      ( v1_relat_1(k4_relat_1(A_5))
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_306,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_12])).

tff(c_314,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_306])).

tff(c_64,plain,(
    ! [A_47] : k6_relat_1(A_47) = k6_partfun1(A_47) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_20,plain,(
    ! [A_14] : k1_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_96,plain,(
    ! [A_14] : k1_relat_1(k6_partfun1(A_14)) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_20])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_90,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_80,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_2720,plain,(
    ! [A_210,C_211,B_212] :
      ( k6_partfun1(A_210) = k5_relat_1(C_211,k2_funct_1(C_211))
      | k1_xboole_0 = B_212
      | ~ v2_funct_1(C_211)
      | k2_relset_1(A_210,B_212,C_211) != B_212
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1(A_210,B_212)))
      | ~ v1_funct_2(C_211,A_210,B_212)
      | ~ v1_funct_1(C_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_2724,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_2720])).

tff(c_2730,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_80,c_76,c_2724])).

tff(c_2731,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2730])).

tff(c_38,plain,(
    ! [A_22] :
      ( k1_relat_1(k5_relat_1(A_22,k2_funct_1(A_22))) = k1_relat_1(A_22)
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2745,plain,
    ( k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2731,c_38])).

tff(c_2756,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_92,c_76,c_96,c_2745])).

tff(c_14,plain,(
    ! [A_6] :
      ( k2_relat_1(k4_relat_1(A_6)) = k1_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    ! [A_16] :
      ( k5_relat_1(A_16,k6_relat_1(k2_relat_1(A_16))) = A_16
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_181,plain,(
    ! [A_67] :
      ( k5_relat_1(A_67,k6_partfun1(k2_relat_1(A_67))) = A_67
      | ~ v1_relat_1(A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_26])).

tff(c_190,plain,(
    ! [A_6] :
      ( k5_relat_1(k4_relat_1(A_6),k6_partfun1(k1_relat_1(A_6))) = k4_relat_1(A_6)
      | ~ v1_relat_1(k4_relat_1(A_6))
      | ~ v1_relat_1(A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_181])).

tff(c_2783,plain,
    ( k5_relat_1(k4_relat_1('#skF_3'),k6_partfun1('#skF_1')) = k4_relat_1('#skF_3')
    | ~ v1_relat_1(k4_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2756,c_190])).

tff(c_2811,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_314,c_296,c_296,c_296,c_2783])).

tff(c_86,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_2172,plain,(
    ! [A_170,E_173,B_174,D_171,F_172,C_175] :
      ( m1_subset_1(k1_partfun1(A_170,B_174,C_175,D_171,E_173,F_172),k1_zfmisc_1(k2_zfmisc_1(A_170,D_171)))
      | ~ m1_subset_1(F_172,k1_zfmisc_1(k2_zfmisc_1(C_175,D_171)))
      | ~ v1_funct_1(F_172)
      | ~ m1_subset_1(E_173,k1_zfmisc_1(k2_zfmisc_1(A_170,B_174)))
      | ~ v1_funct_1(E_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_60,plain,(
    ! [A_40] : m1_subset_1(k6_partfun1(A_40),k1_zfmisc_1(k2_zfmisc_1(A_40,A_40))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_78,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_1105,plain,(
    ! [D_127,C_128,A_129,B_130] :
      ( D_127 = C_128
      | ~ r2_relset_1(A_129,B_130,C_128,D_127)
      | ~ m1_subset_1(D_127,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130)))
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1113,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_78,c_1105])).

tff(c_1128,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1113])).

tff(c_1327,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1128])).

tff(c_2192,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2172,c_1327])).

tff(c_2214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_86,c_82,c_2192])).

tff(c_2215,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1128])).

tff(c_2607,plain,(
    ! [E_197,C_199,A_198,F_201,D_200,B_202] :
      ( k1_partfun1(A_198,B_202,C_199,D_200,E_197,F_201) = k5_relat_1(E_197,F_201)
      | ~ m1_subset_1(F_201,k1_zfmisc_1(k2_zfmisc_1(C_199,D_200)))
      | ~ v1_funct_1(F_201)
      | ~ m1_subset_1(E_197,k1_zfmisc_1(k2_zfmisc_1(A_198,B_202)))
      | ~ v1_funct_1(E_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_2613,plain,(
    ! [A_198,B_202,E_197] :
      ( k1_partfun1(A_198,B_202,'#skF_2','#skF_1',E_197,'#skF_4') = k5_relat_1(E_197,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_197,k1_zfmisc_1(k2_zfmisc_1(A_198,B_202)))
      | ~ v1_funct_1(E_197) ) ),
    inference(resolution,[status(thm)],[c_82,c_2607])).

tff(c_3158,plain,(
    ! [A_222,B_223,E_224] :
      ( k1_partfun1(A_222,B_223,'#skF_2','#skF_1',E_224,'#skF_4') = k5_relat_1(E_224,'#skF_4')
      | ~ m1_subset_1(E_224,k1_zfmisc_1(k2_zfmisc_1(A_222,B_223)))
      | ~ v1_funct_1(E_224) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_2613])).

tff(c_3167,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_3158])).

tff(c_3175,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_2215,c_3167])).

tff(c_2886,plain,(
    ! [B_213,C_214,A_215] :
      ( k6_partfun1(B_213) = k5_relat_1(k2_funct_1(C_214),C_214)
      | k1_xboole_0 = B_213
      | ~ v2_funct_1(C_214)
      | k2_relset_1(A_215,B_213,C_214) != B_213
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k2_zfmisc_1(A_215,B_213)))
      | ~ v1_funct_2(C_214,A_215,B_213)
      | ~ v1_funct_1(C_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_2890,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_2886])).

tff(c_2896,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_80,c_76,c_2890])).

tff(c_2897,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2896])).

tff(c_18,plain,(
    ! [A_7,B_11,C_13] :
      ( k5_relat_1(k5_relat_1(A_7,B_11),C_13) = k5_relat_1(A_7,k5_relat_1(B_11,C_13))
      | ~ v1_relat_1(C_13)
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2983,plain,(
    ! [C_13] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_13)) = k5_relat_1(k6_partfun1('#skF_2'),C_13)
      | ~ v1_relat_1(C_13)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2897,c_18])).

tff(c_4972,plain,(
    ! [C_265] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_265)) = k5_relat_1(k6_partfun1('#skF_2'),C_265)
      | ~ v1_relat_1(C_265) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_179,c_2983])).

tff(c_5017,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3175,c_4972])).

tff(c_5051,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_2811,c_5017])).

tff(c_271,plain,(
    ! [C_83,A_84,B_85] :
      ( v4_relat_1(C_83,A_84)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_284,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_271])).

tff(c_22,plain,(
    ! [A_14] : k2_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_95,plain,(
    ! [A_14] : k2_relat_1(k6_partfun1(A_14)) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_22])).

tff(c_40,plain,(
    ! [A_23] :
      ( k2_relat_1(k5_relat_1(k2_funct_1(A_23),A_23)) = k2_relat_1(A_23)
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2986,plain,
    ( k2_relat_1(k6_partfun1('#skF_2')) = k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2897,c_40])).

tff(c_2999,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_92,c_76,c_95,c_2986])).

tff(c_871,plain,(
    ! [B_119,A_120] :
      ( r1_tarski(k2_relat_1(B_119),k1_relat_1(A_120))
      | k1_relat_1(k5_relat_1(B_119,A_120)) != k1_relat_1(B_119)
      | ~ v1_funct_1(B_119)
      | ~ v1_relat_1(B_119)
      | ~ v1_funct_1(A_120)
      | ~ v1_relat_1(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_218,plain,(
    ! [B_75,A_76] :
      ( r1_tarski(k1_relat_1(B_75),A_76)
      | ~ v4_relat_1(B_75,A_76)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_227,plain,(
    ! [B_75,A_76] :
      ( k1_relat_1(B_75) = A_76
      | ~ r1_tarski(A_76,k1_relat_1(B_75))
      | ~ v4_relat_1(B_75,A_76)
      | ~ v1_relat_1(B_75) ) ),
    inference(resolution,[status(thm)],[c_218,c_2])).

tff(c_19065,plain,(
    ! [B_494,A_495] :
      ( k2_relat_1(B_494) = k1_relat_1(A_495)
      | ~ v4_relat_1(A_495,k2_relat_1(B_494))
      | k1_relat_1(k5_relat_1(B_494,A_495)) != k1_relat_1(B_494)
      | ~ v1_funct_1(B_494)
      | ~ v1_relat_1(B_494)
      | ~ v1_funct_1(A_495)
      | ~ v1_relat_1(A_495) ) ),
    inference(resolution,[status(thm)],[c_871,c_227])).

tff(c_19129,plain,(
    ! [A_495] :
      ( k2_relat_1('#skF_3') = k1_relat_1(A_495)
      | ~ v4_relat_1(A_495,'#skF_2')
      | k1_relat_1(k5_relat_1('#skF_3',A_495)) != k1_relat_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_funct_1(A_495)
      | ~ v1_relat_1(A_495) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2999,c_19065])).

tff(c_32419,plain,(
    ! [A_571] :
      ( k1_relat_1(A_571) = '#skF_2'
      | ~ v4_relat_1(A_571,'#skF_2')
      | k1_relat_1(k5_relat_1('#skF_3',A_571)) != '#skF_1'
      | ~ v1_funct_1(A_571)
      | ~ v1_relat_1(A_571) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_92,c_2756,c_2999,c_19129])).

tff(c_32523,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v4_relat_1('#skF_4','#skF_2')
    | k1_relat_1(k6_partfun1('#skF_1')) != '#skF_1'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3175,c_32419])).

tff(c_32579,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_86,c_96,c_284,c_32523])).

tff(c_24,plain,(
    ! [A_15] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_15)),A_15) = A_15
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_94,plain,(
    ! [A_15] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_15)),A_15) = A_15
      | ~ v1_relat_1(A_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_24])).

tff(c_32696,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_32579,c_94])).

tff(c_32766,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_5051,c_32696])).

tff(c_32768,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_32766])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:58:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.85/10.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.94/10.36  
% 18.94/10.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.94/10.36  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 18.94/10.36  
% 18.94/10.36  %Foreground sorts:
% 18.94/10.36  
% 18.94/10.36  
% 18.94/10.36  %Background operators:
% 18.94/10.36  
% 18.94/10.36  
% 18.94/10.36  %Foreground operators:
% 18.94/10.36  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 18.94/10.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 18.94/10.36  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 18.94/10.36  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 18.94/10.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.94/10.36  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 18.94/10.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 18.94/10.36  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 18.94/10.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.94/10.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 18.94/10.36  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 18.94/10.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 18.94/10.36  tff('#skF_2', type, '#skF_2': $i).
% 18.94/10.36  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 18.94/10.36  tff('#skF_3', type, '#skF_3': $i).
% 18.94/10.36  tff('#skF_1', type, '#skF_1': $i).
% 18.94/10.36  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 18.94/10.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 18.94/10.36  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 18.94/10.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.94/10.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 18.94/10.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 18.94/10.36  tff('#skF_4', type, '#skF_4': $i).
% 18.94/10.36  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 18.94/10.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.94/10.36  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 18.94/10.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 18.94/10.36  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 18.94/10.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 18.94/10.36  
% 18.94/10.38  tff(f_206, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 18.94/10.38  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 18.94/10.38  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 18.94/10.38  tff(f_41, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 18.94/10.38  tff(f_164, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 18.94/10.38  tff(f_61, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 18.94/10.38  tff(f_180, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 18.94/10.38  tff(f_108, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 18.94/10.38  tff(f_47, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 18.94/10.38  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 18.94/10.38  tff(f_148, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 18.94/10.38  tff(f_152, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 18.94/10.38  tff(f_136, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 18.94/10.38  tff(f_162, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 18.94/10.38  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 18.94/10.38  tff(f_128, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 18.94/10.38  tff(f_118, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_funct_1)).
% 18.94/10.38  tff(f_98, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_funct_1)).
% 18.94/10.38  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 18.94/10.38  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 18.94/10.38  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 18.94/10.38  tff(c_70, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_206])).
% 18.94/10.38  tff(c_82, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_206])).
% 18.94/10.38  tff(c_168, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 18.94/10.38  tff(c_180, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_82, c_168])).
% 18.94/10.38  tff(c_88, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_206])).
% 18.94/10.38  tff(c_179, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_168])).
% 18.94/10.38  tff(c_92, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_206])).
% 18.94/10.38  tff(c_76, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_206])).
% 18.94/10.38  tff(c_290, plain, (![A_88]: (k4_relat_1(A_88)=k2_funct_1(A_88) | ~v2_funct_1(A_88) | ~v1_funct_1(A_88) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_77])).
% 18.94/10.38  tff(c_293, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_290])).
% 18.94/10.38  tff(c_296, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_92, c_293])).
% 18.94/10.38  tff(c_12, plain, (![A_5]: (v1_relat_1(k4_relat_1(A_5)) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 18.94/10.38  tff(c_306, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_296, c_12])).
% 18.94/10.38  tff(c_314, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_306])).
% 18.94/10.38  tff(c_64, plain, (![A_47]: (k6_relat_1(A_47)=k6_partfun1(A_47))), inference(cnfTransformation, [status(thm)], [f_164])).
% 18.94/10.38  tff(c_20, plain, (![A_14]: (k1_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_61])).
% 18.94/10.38  tff(c_96, plain, (![A_14]: (k1_relat_1(k6_partfun1(A_14))=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_20])).
% 18.94/10.38  tff(c_72, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_206])).
% 18.94/10.38  tff(c_90, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_206])).
% 18.94/10.38  tff(c_80, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_206])).
% 18.94/10.38  tff(c_2720, plain, (![A_210, C_211, B_212]: (k6_partfun1(A_210)=k5_relat_1(C_211, k2_funct_1(C_211)) | k1_xboole_0=B_212 | ~v2_funct_1(C_211) | k2_relset_1(A_210, B_212, C_211)!=B_212 | ~m1_subset_1(C_211, k1_zfmisc_1(k2_zfmisc_1(A_210, B_212))) | ~v1_funct_2(C_211, A_210, B_212) | ~v1_funct_1(C_211))), inference(cnfTransformation, [status(thm)], [f_180])).
% 18.94/10.38  tff(c_2724, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_2720])).
% 18.94/10.38  tff(c_2730, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_80, c_76, c_2724])).
% 18.94/10.38  tff(c_2731, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_72, c_2730])).
% 18.94/10.38  tff(c_38, plain, (![A_22]: (k1_relat_1(k5_relat_1(A_22, k2_funct_1(A_22)))=k1_relat_1(A_22) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_108])).
% 18.94/10.38  tff(c_2745, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2731, c_38])).
% 18.94/10.38  tff(c_2756, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_179, c_92, c_76, c_96, c_2745])).
% 18.94/10.38  tff(c_14, plain, (![A_6]: (k2_relat_1(k4_relat_1(A_6))=k1_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 18.94/10.38  tff(c_26, plain, (![A_16]: (k5_relat_1(A_16, k6_relat_1(k2_relat_1(A_16)))=A_16 | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_69])).
% 18.94/10.38  tff(c_181, plain, (![A_67]: (k5_relat_1(A_67, k6_partfun1(k2_relat_1(A_67)))=A_67 | ~v1_relat_1(A_67))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_26])).
% 18.94/10.38  tff(c_190, plain, (![A_6]: (k5_relat_1(k4_relat_1(A_6), k6_partfun1(k1_relat_1(A_6)))=k4_relat_1(A_6) | ~v1_relat_1(k4_relat_1(A_6)) | ~v1_relat_1(A_6))), inference(superposition, [status(thm), theory('equality')], [c_14, c_181])).
% 18.94/10.38  tff(c_2783, plain, (k5_relat_1(k4_relat_1('#skF_3'), k6_partfun1('#skF_1'))=k4_relat_1('#skF_3') | ~v1_relat_1(k4_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2756, c_190])).
% 18.94/10.38  tff(c_2811, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_314, c_296, c_296, c_296, c_2783])).
% 18.94/10.38  tff(c_86, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_206])).
% 18.94/10.38  tff(c_2172, plain, (![A_170, E_173, B_174, D_171, F_172, C_175]: (m1_subset_1(k1_partfun1(A_170, B_174, C_175, D_171, E_173, F_172), k1_zfmisc_1(k2_zfmisc_1(A_170, D_171))) | ~m1_subset_1(F_172, k1_zfmisc_1(k2_zfmisc_1(C_175, D_171))) | ~v1_funct_1(F_172) | ~m1_subset_1(E_173, k1_zfmisc_1(k2_zfmisc_1(A_170, B_174))) | ~v1_funct_1(E_173))), inference(cnfTransformation, [status(thm)], [f_148])).
% 18.94/10.38  tff(c_60, plain, (![A_40]: (m1_subset_1(k6_partfun1(A_40), k1_zfmisc_1(k2_zfmisc_1(A_40, A_40))))), inference(cnfTransformation, [status(thm)], [f_152])).
% 18.94/10.38  tff(c_78, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_206])).
% 18.94/10.38  tff(c_1105, plain, (![D_127, C_128, A_129, B_130]: (D_127=C_128 | ~r2_relset_1(A_129, B_130, C_128, D_127) | ~m1_subset_1(D_127, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 18.94/10.38  tff(c_1113, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_78, c_1105])).
% 18.94/10.38  tff(c_1128, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1113])).
% 18.94/10.38  tff(c_1327, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1128])).
% 18.94/10.38  tff(c_2192, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2172, c_1327])).
% 18.94/10.38  tff(c_2214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_86, c_82, c_2192])).
% 18.94/10.38  tff(c_2215, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1128])).
% 18.94/10.38  tff(c_2607, plain, (![E_197, C_199, A_198, F_201, D_200, B_202]: (k1_partfun1(A_198, B_202, C_199, D_200, E_197, F_201)=k5_relat_1(E_197, F_201) | ~m1_subset_1(F_201, k1_zfmisc_1(k2_zfmisc_1(C_199, D_200))) | ~v1_funct_1(F_201) | ~m1_subset_1(E_197, k1_zfmisc_1(k2_zfmisc_1(A_198, B_202))) | ~v1_funct_1(E_197))), inference(cnfTransformation, [status(thm)], [f_162])).
% 18.94/10.38  tff(c_2613, plain, (![A_198, B_202, E_197]: (k1_partfun1(A_198, B_202, '#skF_2', '#skF_1', E_197, '#skF_4')=k5_relat_1(E_197, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_197, k1_zfmisc_1(k2_zfmisc_1(A_198, B_202))) | ~v1_funct_1(E_197))), inference(resolution, [status(thm)], [c_82, c_2607])).
% 18.94/10.38  tff(c_3158, plain, (![A_222, B_223, E_224]: (k1_partfun1(A_222, B_223, '#skF_2', '#skF_1', E_224, '#skF_4')=k5_relat_1(E_224, '#skF_4') | ~m1_subset_1(E_224, k1_zfmisc_1(k2_zfmisc_1(A_222, B_223))) | ~v1_funct_1(E_224))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_2613])).
% 18.94/10.38  tff(c_3167, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_3158])).
% 18.94/10.38  tff(c_3175, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_2215, c_3167])).
% 18.94/10.38  tff(c_2886, plain, (![B_213, C_214, A_215]: (k6_partfun1(B_213)=k5_relat_1(k2_funct_1(C_214), C_214) | k1_xboole_0=B_213 | ~v2_funct_1(C_214) | k2_relset_1(A_215, B_213, C_214)!=B_213 | ~m1_subset_1(C_214, k1_zfmisc_1(k2_zfmisc_1(A_215, B_213))) | ~v1_funct_2(C_214, A_215, B_213) | ~v1_funct_1(C_214))), inference(cnfTransformation, [status(thm)], [f_180])).
% 18.94/10.38  tff(c_2890, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_2886])).
% 18.94/10.38  tff(c_2896, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_80, c_76, c_2890])).
% 18.94/10.38  tff(c_2897, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_72, c_2896])).
% 18.94/10.38  tff(c_18, plain, (![A_7, B_11, C_13]: (k5_relat_1(k5_relat_1(A_7, B_11), C_13)=k5_relat_1(A_7, k5_relat_1(B_11, C_13)) | ~v1_relat_1(C_13) | ~v1_relat_1(B_11) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_57])).
% 18.94/10.38  tff(c_2983, plain, (![C_13]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_13))=k5_relat_1(k6_partfun1('#skF_2'), C_13) | ~v1_relat_1(C_13) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2897, c_18])).
% 18.94/10.38  tff(c_4972, plain, (![C_265]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_265))=k5_relat_1(k6_partfun1('#skF_2'), C_265) | ~v1_relat_1(C_265))), inference(demodulation, [status(thm), theory('equality')], [c_314, c_179, c_2983])).
% 18.94/10.38  tff(c_5017, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3175, c_4972])).
% 18.94/10.38  tff(c_5051, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_180, c_2811, c_5017])).
% 18.94/10.38  tff(c_271, plain, (![C_83, A_84, B_85]: (v4_relat_1(C_83, A_84) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 18.94/10.38  tff(c_284, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_82, c_271])).
% 18.94/10.38  tff(c_22, plain, (![A_14]: (k2_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_61])).
% 18.94/10.38  tff(c_95, plain, (![A_14]: (k2_relat_1(k6_partfun1(A_14))=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_22])).
% 18.94/10.38  tff(c_40, plain, (![A_23]: (k2_relat_1(k5_relat_1(k2_funct_1(A_23), A_23))=k2_relat_1(A_23) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_118])).
% 18.94/10.38  tff(c_2986, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2897, c_40])).
% 18.94/10.38  tff(c_2999, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_179, c_92, c_76, c_95, c_2986])).
% 18.94/10.38  tff(c_871, plain, (![B_119, A_120]: (r1_tarski(k2_relat_1(B_119), k1_relat_1(A_120)) | k1_relat_1(k5_relat_1(B_119, A_120))!=k1_relat_1(B_119) | ~v1_funct_1(B_119) | ~v1_relat_1(B_119) | ~v1_funct_1(A_120) | ~v1_relat_1(A_120))), inference(cnfTransformation, [status(thm)], [f_98])).
% 18.94/10.38  tff(c_218, plain, (![B_75, A_76]: (r1_tarski(k1_relat_1(B_75), A_76) | ~v4_relat_1(B_75, A_76) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_37])).
% 18.94/10.38  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.94/10.38  tff(c_227, plain, (![B_75, A_76]: (k1_relat_1(B_75)=A_76 | ~r1_tarski(A_76, k1_relat_1(B_75)) | ~v4_relat_1(B_75, A_76) | ~v1_relat_1(B_75))), inference(resolution, [status(thm)], [c_218, c_2])).
% 18.94/10.38  tff(c_19065, plain, (![B_494, A_495]: (k2_relat_1(B_494)=k1_relat_1(A_495) | ~v4_relat_1(A_495, k2_relat_1(B_494)) | k1_relat_1(k5_relat_1(B_494, A_495))!=k1_relat_1(B_494) | ~v1_funct_1(B_494) | ~v1_relat_1(B_494) | ~v1_funct_1(A_495) | ~v1_relat_1(A_495))), inference(resolution, [status(thm)], [c_871, c_227])).
% 18.94/10.38  tff(c_19129, plain, (![A_495]: (k2_relat_1('#skF_3')=k1_relat_1(A_495) | ~v4_relat_1(A_495, '#skF_2') | k1_relat_1(k5_relat_1('#skF_3', A_495))!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1(A_495) | ~v1_relat_1(A_495))), inference(superposition, [status(thm), theory('equality')], [c_2999, c_19065])).
% 18.94/10.38  tff(c_32419, plain, (![A_571]: (k1_relat_1(A_571)='#skF_2' | ~v4_relat_1(A_571, '#skF_2') | k1_relat_1(k5_relat_1('#skF_3', A_571))!='#skF_1' | ~v1_funct_1(A_571) | ~v1_relat_1(A_571))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_92, c_2756, c_2999, c_19129])).
% 18.94/10.38  tff(c_32523, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v4_relat_1('#skF_4', '#skF_2') | k1_relat_1(k6_partfun1('#skF_1'))!='#skF_1' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3175, c_32419])).
% 18.94/10.38  tff(c_32579, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_180, c_86, c_96, c_284, c_32523])).
% 18.94/10.38  tff(c_24, plain, (![A_15]: (k5_relat_1(k6_relat_1(k1_relat_1(A_15)), A_15)=A_15 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 18.94/10.38  tff(c_94, plain, (![A_15]: (k5_relat_1(k6_partfun1(k1_relat_1(A_15)), A_15)=A_15 | ~v1_relat_1(A_15))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_24])).
% 18.94/10.38  tff(c_32696, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_32579, c_94])).
% 18.94/10.38  tff(c_32766, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_180, c_5051, c_32696])).
% 18.94/10.38  tff(c_32768, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_32766])).
% 18.94/10.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.94/10.38  
% 18.94/10.38  Inference rules
% 18.94/10.38  ----------------------
% 18.94/10.38  #Ref     : 0
% 18.94/10.38  #Sup     : 6762
% 18.94/10.38  #Fact    : 0
% 18.94/10.38  #Define  : 0
% 18.94/10.38  #Split   : 41
% 18.94/10.38  #Chain   : 0
% 18.94/10.38  #Close   : 0
% 18.94/10.38  
% 18.94/10.38  Ordering : KBO
% 18.94/10.38  
% 18.94/10.38  Simplification rules
% 18.94/10.38  ----------------------
% 18.94/10.38  #Subsume      : 565
% 18.94/10.38  #Demod        : 16447
% 18.94/10.38  #Tautology    : 2028
% 18.94/10.38  #SimpNegUnit  : 130
% 18.94/10.38  #BackRed      : 174
% 18.94/10.38  
% 18.94/10.38  #Partial instantiations: 0
% 18.94/10.38  #Strategies tried      : 1
% 18.94/10.38  
% 18.94/10.38  Timing (in seconds)
% 18.94/10.38  ----------------------
% 18.94/10.38  Preprocessing        : 0.39
% 18.94/10.38  Parsing              : 0.20
% 18.94/10.38  CNF conversion       : 0.03
% 18.94/10.38  Main loop            : 9.21
% 18.94/10.38  Inferencing          : 1.68
% 18.94/10.38  Reduction            : 5.37
% 18.94/10.38  Demodulation         : 4.73
% 18.94/10.38  BG Simplification    : 0.17
% 18.94/10.38  Subsumption          : 1.64
% 18.94/10.38  Abstraction          : 0.29
% 18.94/10.38  MUC search           : 0.00
% 18.94/10.38  Cooper               : 0.00
% 18.94/10.38  Total                : 9.64
% 18.94/10.38  Index Insertion      : 0.00
% 18.94/10.38  Index Deletion       : 0.00
% 18.94/10.38  Index Matching       : 0.00
% 18.94/10.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
