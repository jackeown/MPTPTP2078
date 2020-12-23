%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:36 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 289 expanded)
%              Number of leaves         :   37 ( 118 expanded)
%              Depth                    :   11
%              Number of atoms          :  202 (1000 expanded)
%              Number of equality atoms :   56 ( 189 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_131,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,C),B)
                & k2_relset_1(A,A,B) = A )
             => r2_relset_1(A,A,C,k6_partfun1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_funct_2)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_109,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_99,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
           => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).

tff(f_111,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k2_relat_1(A) = k1_relat_1(B)
              & k5_relat_1(A,B) = A )
           => B = k6_relat_1(k1_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_190,plain,(
    ! [A_62,B_63,D_64] :
      ( r2_relset_1(A_62,B_63,D_64,D_64)
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_196,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_190])).

tff(c_99,plain,(
    ! [C_45,A_46,B_47] :
      ( v1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_107,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_99])).

tff(c_127,plain,(
    ! [C_55,A_56,B_57] :
      ( v4_relat_1(C_55,A_56)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_135,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_127])).

tff(c_44,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_50,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_46,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_371,plain,(
    ! [B_98,A_101,E_97,C_100,F_99,D_102] :
      ( k1_partfun1(A_101,B_98,C_100,D_102,E_97,F_99) = k5_relat_1(E_97,F_99)
      | ~ m1_subset_1(F_99,k1_zfmisc_1(k2_zfmisc_1(C_100,D_102)))
      | ~ v1_funct_1(F_99)
      | ~ m1_subset_1(E_97,k1_zfmisc_1(k2_zfmisc_1(A_101,B_98)))
      | ~ v1_funct_1(E_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_375,plain,(
    ! [A_101,B_98,E_97] :
      ( k1_partfun1(A_101,B_98,'#skF_1','#skF_1',E_97,'#skF_3') = k5_relat_1(E_97,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_97,k1_zfmisc_1(k2_zfmisc_1(A_101,B_98)))
      | ~ v1_funct_1(E_97) ) ),
    inference(resolution,[status(thm)],[c_40,c_371])).

tff(c_405,plain,(
    ! [A_106,B_107,E_108] :
      ( k1_partfun1(A_106,B_107,'#skF_1','#skF_1',E_108,'#skF_3') = k5_relat_1(E_108,'#skF_3')
      | ~ m1_subset_1(E_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107)))
      | ~ v1_funct_1(E_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_375])).

tff(c_408,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_405])).

tff(c_414,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_408])).

tff(c_38,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_248,plain,(
    ! [D_75,C_76,A_77,B_78] :
      ( D_75 = C_76
      | ~ r2_relset_1(A_77,B_78,C_76,D_75)
      | ~ m1_subset_1(D_75,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78)))
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_254,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = '#skF_2'
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_38,c_248])).

tff(c_265,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = '#skF_2'
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_254])).

tff(c_267,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_265])).

tff(c_419,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_414,c_267])).

tff(c_430,plain,(
    ! [D_109,F_112,B_110,A_111,E_114,C_113] :
      ( m1_subset_1(k1_partfun1(A_111,B_110,C_113,D_109,E_114,F_112),k1_zfmisc_1(k2_zfmisc_1(A_111,D_109)))
      | ~ m1_subset_1(F_112,k1_zfmisc_1(k2_zfmisc_1(C_113,D_109)))
      | ~ v1_funct_1(F_112)
      | ~ m1_subset_1(E_114,k1_zfmisc_1(k2_zfmisc_1(A_111,B_110)))
      | ~ v1_funct_1(E_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_463,plain,
    ( m1_subset_1(k5_relat_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_430])).

tff(c_482,plain,(
    m1_subset_1(k5_relat_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_44,c_40,c_463])).

tff(c_487,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_419,c_482])).

tff(c_488,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_265])).

tff(c_607,plain,(
    ! [C_137,A_138,E_134,B_135,D_139,F_136] :
      ( k1_partfun1(A_138,B_135,C_137,D_139,E_134,F_136) = k5_relat_1(E_134,F_136)
      | ~ m1_subset_1(F_136,k1_zfmisc_1(k2_zfmisc_1(C_137,D_139)))
      | ~ v1_funct_1(F_136)
      | ~ m1_subset_1(E_134,k1_zfmisc_1(k2_zfmisc_1(A_138,B_135)))
      | ~ v1_funct_1(E_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_611,plain,(
    ! [A_138,B_135,E_134] :
      ( k1_partfun1(A_138,B_135,'#skF_1','#skF_1',E_134,'#skF_3') = k5_relat_1(E_134,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_134,k1_zfmisc_1(k2_zfmisc_1(A_138,B_135)))
      | ~ v1_funct_1(E_134) ) ),
    inference(resolution,[status(thm)],[c_40,c_607])).

tff(c_641,plain,(
    ! [A_143,B_144,E_145] :
      ( k1_partfun1(A_143,B_144,'#skF_1','#skF_1',E_145,'#skF_3') = k5_relat_1(E_145,'#skF_3')
      | ~ m1_subset_1(E_145,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144)))
      | ~ v1_funct_1(E_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_611])).

tff(c_644,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_641])).

tff(c_650,plain,(
    k5_relat_1('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_488,c_644])).

tff(c_106,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_99])).

tff(c_36,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_197,plain,(
    ! [A_65,B_66,C_67] :
      ( k2_relset_1(A_65,B_66,C_67) = k2_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_200,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_197])).

tff(c_205,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_200])).

tff(c_108,plain,(
    ! [B_48,A_49] :
      ( r1_tarski(k1_relat_1(B_48),A_49)
      | ~ v4_relat_1(B_48,A_49)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_136,plain,(
    ! [B_58,A_59] :
      ( k2_xboole_0(k1_relat_1(B_58),A_59) = A_59
      | ~ v4_relat_1(B_58,A_59)
      | ~ v1_relat_1(B_58) ) ),
    inference(resolution,[status(thm)],[c_108,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_142,plain,(
    ! [A_59,B_58] :
      ( k2_xboole_0(A_59,k1_relat_1(B_58)) = A_59
      | ~ v4_relat_1(B_58,A_59)
      | ~ v1_relat_1(B_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_2])).

tff(c_216,plain,(
    ! [B_70,A_71] :
      ( r1_tarski(k2_relat_1(B_70),k1_relat_1(A_71))
      | k1_relat_1(k5_relat_1(B_70,A_71)) != k1_relat_1(B_70)
      | ~ v1_funct_1(B_70)
      | ~ v1_relat_1(B_70)
      | ~ v1_funct_1(A_71)
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_497,plain,(
    ! [B_115,A_116] :
      ( k2_xboole_0(k2_relat_1(B_115),k1_relat_1(A_116)) = k1_relat_1(A_116)
      | k1_relat_1(k5_relat_1(B_115,A_116)) != k1_relat_1(B_115)
      | ~ v1_funct_1(B_115)
      | ~ v1_relat_1(B_115)
      | ~ v1_funct_1(A_116)
      | ~ v1_relat_1(A_116) ) ),
    inference(resolution,[status(thm)],[c_216,c_4])).

tff(c_600,plain,(
    ! [B_131,B_132] :
      ( k2_relat_1(B_131) = k1_relat_1(B_132)
      | k1_relat_1(k5_relat_1(B_131,B_132)) != k1_relat_1(B_131)
      | ~ v1_funct_1(B_131)
      | ~ v1_relat_1(B_131)
      | ~ v1_funct_1(B_132)
      | ~ v1_relat_1(B_132)
      | ~ v4_relat_1(B_132,k2_relat_1(B_131))
      | ~ v1_relat_1(B_132) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_497])).

tff(c_603,plain,(
    ! [B_132] :
      ( k2_relat_1('#skF_2') = k1_relat_1(B_132)
      | k1_relat_1(k5_relat_1('#skF_2',B_132)) != k1_relat_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_funct_1(B_132)
      | ~ v1_relat_1(B_132)
      | ~ v4_relat_1(B_132,'#skF_1')
      | ~ v1_relat_1(B_132) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_600])).

tff(c_605,plain,(
    ! [B_132] :
      ( k1_relat_1(B_132) = '#skF_1'
      | k1_relat_1(k5_relat_1('#skF_2',B_132)) != k1_relat_1('#skF_2')
      | ~ v1_funct_1(B_132)
      | ~ v4_relat_1(B_132,'#skF_1')
      | ~ v1_relat_1(B_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_50,c_205,c_603])).

tff(c_657,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ v1_funct_1('#skF_3')
    | ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_650,c_605])).

tff(c_664,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_135,c_44,c_657])).

tff(c_32,plain,(
    ! [A_38] : k6_relat_1(A_38) = k6_partfun1(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_12,plain,(
    ! [B_12,A_10] :
      ( k6_relat_1(k1_relat_1(B_12)) = B_12
      | k5_relat_1(A_10,B_12) != A_10
      | k2_relat_1(A_10) != k1_relat_1(B_12)
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_51,plain,(
    ! [B_12,A_10] :
      ( k6_partfun1(k1_relat_1(B_12)) = B_12
      | k5_relat_1(A_10,B_12) != A_10
      | k2_relat_1(A_10) != k1_relat_1(B_12)
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_12])).

tff(c_659,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | k2_relat_1('#skF_2') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_650,c_51])).

tff(c_667,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_50,c_107,c_44,c_205,c_659])).

tff(c_823,plain,(
    k6_partfun1('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_664,c_664,c_667])).

tff(c_34,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_824,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_823,c_34])).

tff(c_827,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_824])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n009.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 19:33:11 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.48  
% 3.31/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.48  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.31/1.48  
% 3.31/1.48  %Foreground sorts:
% 3.31/1.48  
% 3.31/1.48  
% 3.31/1.48  %Background operators:
% 3.31/1.48  
% 3.31/1.48  
% 3.31/1.48  %Foreground operators:
% 3.31/1.48  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.31/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.31/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.48  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.31/1.48  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.31/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.31/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.31/1.48  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.31/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.31/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.31/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.31/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.31/1.48  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.31/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.31/1.48  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.31/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.31/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.31/1.48  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.31/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.48  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.31/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.31/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.31/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.31/1.48  
% 3.31/1.50  tff(f_131, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), B) & (k2_relset_1(A, A, B) = A)) => r2_relset_1(A, A, C, k6_partfun1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_funct_2)).
% 3.31/1.50  tff(f_87, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.31/1.50  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.31/1.50  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.31/1.50  tff(f_109, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.31/1.50  tff(f_99, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.31/1.50  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.31/1.50  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.31/1.50  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.31/1.50  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.31/1.50  tff(f_50, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_funct_1)).
% 3.31/1.50  tff(f_111, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.31/1.50  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k2_relat_1(A) = k1_relat_1(B)) & (k5_relat_1(A, B) = A)) => (B = k6_relat_1(k1_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_funct_1)).
% 3.31/1.50  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.31/1.50  tff(c_190, plain, (![A_62, B_63, D_64]: (r2_relset_1(A_62, B_63, D_64, D_64) | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.31/1.50  tff(c_196, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_190])).
% 3.31/1.50  tff(c_99, plain, (![C_45, A_46, B_47]: (v1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.31/1.50  tff(c_107, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_99])).
% 3.31/1.50  tff(c_127, plain, (![C_55, A_56, B_57]: (v4_relat_1(C_55, A_56) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.31/1.50  tff(c_135, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_40, c_127])).
% 3.31/1.50  tff(c_44, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.31/1.50  tff(c_50, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.31/1.50  tff(c_46, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.31/1.50  tff(c_371, plain, (![B_98, A_101, E_97, C_100, F_99, D_102]: (k1_partfun1(A_101, B_98, C_100, D_102, E_97, F_99)=k5_relat_1(E_97, F_99) | ~m1_subset_1(F_99, k1_zfmisc_1(k2_zfmisc_1(C_100, D_102))) | ~v1_funct_1(F_99) | ~m1_subset_1(E_97, k1_zfmisc_1(k2_zfmisc_1(A_101, B_98))) | ~v1_funct_1(E_97))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.31/1.50  tff(c_375, plain, (![A_101, B_98, E_97]: (k1_partfun1(A_101, B_98, '#skF_1', '#skF_1', E_97, '#skF_3')=k5_relat_1(E_97, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_97, k1_zfmisc_1(k2_zfmisc_1(A_101, B_98))) | ~v1_funct_1(E_97))), inference(resolution, [status(thm)], [c_40, c_371])).
% 3.31/1.50  tff(c_405, plain, (![A_106, B_107, E_108]: (k1_partfun1(A_106, B_107, '#skF_1', '#skF_1', E_108, '#skF_3')=k5_relat_1(E_108, '#skF_3') | ~m1_subset_1(E_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))) | ~v1_funct_1(E_108))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_375])).
% 3.31/1.50  tff(c_408, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k5_relat_1('#skF_2', '#skF_3') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_46, c_405])).
% 3.31/1.50  tff(c_414, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k5_relat_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_408])).
% 3.31/1.50  tff(c_38, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.31/1.50  tff(c_248, plain, (![D_75, C_76, A_77, B_78]: (D_75=C_76 | ~r2_relset_1(A_77, B_78, C_76, D_75) | ~m1_subset_1(D_75, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.31/1.50  tff(c_254, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_38, c_248])).
% 3.31/1.50  tff(c_265, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')='#skF_2' | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_254])).
% 3.31/1.50  tff(c_267, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_265])).
% 3.31/1.50  tff(c_419, plain, (~m1_subset_1(k5_relat_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_414, c_267])).
% 3.31/1.50  tff(c_430, plain, (![D_109, F_112, B_110, A_111, E_114, C_113]: (m1_subset_1(k1_partfun1(A_111, B_110, C_113, D_109, E_114, F_112), k1_zfmisc_1(k2_zfmisc_1(A_111, D_109))) | ~m1_subset_1(F_112, k1_zfmisc_1(k2_zfmisc_1(C_113, D_109))) | ~v1_funct_1(F_112) | ~m1_subset_1(E_114, k1_zfmisc_1(k2_zfmisc_1(A_111, B_110))) | ~v1_funct_1(E_114))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.31/1.50  tff(c_463, plain, (m1_subset_1(k5_relat_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_414, c_430])).
% 3.31/1.50  tff(c_482, plain, (m1_subset_1(k5_relat_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_44, c_40, c_463])).
% 3.31/1.50  tff(c_487, plain, $false, inference(negUnitSimplification, [status(thm)], [c_419, c_482])).
% 3.31/1.50  tff(c_488, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_265])).
% 3.31/1.50  tff(c_607, plain, (![C_137, A_138, E_134, B_135, D_139, F_136]: (k1_partfun1(A_138, B_135, C_137, D_139, E_134, F_136)=k5_relat_1(E_134, F_136) | ~m1_subset_1(F_136, k1_zfmisc_1(k2_zfmisc_1(C_137, D_139))) | ~v1_funct_1(F_136) | ~m1_subset_1(E_134, k1_zfmisc_1(k2_zfmisc_1(A_138, B_135))) | ~v1_funct_1(E_134))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.31/1.50  tff(c_611, plain, (![A_138, B_135, E_134]: (k1_partfun1(A_138, B_135, '#skF_1', '#skF_1', E_134, '#skF_3')=k5_relat_1(E_134, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_134, k1_zfmisc_1(k2_zfmisc_1(A_138, B_135))) | ~v1_funct_1(E_134))), inference(resolution, [status(thm)], [c_40, c_607])).
% 3.31/1.50  tff(c_641, plain, (![A_143, B_144, E_145]: (k1_partfun1(A_143, B_144, '#skF_1', '#skF_1', E_145, '#skF_3')=k5_relat_1(E_145, '#skF_3') | ~m1_subset_1(E_145, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))) | ~v1_funct_1(E_145))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_611])).
% 3.31/1.50  tff(c_644, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k5_relat_1('#skF_2', '#skF_3') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_46, c_641])).
% 3.31/1.50  tff(c_650, plain, (k5_relat_1('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_488, c_644])).
% 3.31/1.50  tff(c_106, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_46, c_99])).
% 3.31/1.50  tff(c_36, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.31/1.50  tff(c_197, plain, (![A_65, B_66, C_67]: (k2_relset_1(A_65, B_66, C_67)=k2_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.31/1.50  tff(c_200, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_46, c_197])).
% 3.31/1.50  tff(c_205, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_200])).
% 3.31/1.50  tff(c_108, plain, (![B_48, A_49]: (r1_tarski(k1_relat_1(B_48), A_49) | ~v4_relat_1(B_48, A_49) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.31/1.50  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.31/1.50  tff(c_136, plain, (![B_58, A_59]: (k2_xboole_0(k1_relat_1(B_58), A_59)=A_59 | ~v4_relat_1(B_58, A_59) | ~v1_relat_1(B_58))), inference(resolution, [status(thm)], [c_108, c_4])).
% 3.31/1.50  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.31/1.50  tff(c_142, plain, (![A_59, B_58]: (k2_xboole_0(A_59, k1_relat_1(B_58))=A_59 | ~v4_relat_1(B_58, A_59) | ~v1_relat_1(B_58))), inference(superposition, [status(thm), theory('equality')], [c_136, c_2])).
% 3.31/1.50  tff(c_216, plain, (![B_70, A_71]: (r1_tarski(k2_relat_1(B_70), k1_relat_1(A_71)) | k1_relat_1(k5_relat_1(B_70, A_71))!=k1_relat_1(B_70) | ~v1_funct_1(B_70) | ~v1_relat_1(B_70) | ~v1_funct_1(A_71) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.31/1.50  tff(c_497, plain, (![B_115, A_116]: (k2_xboole_0(k2_relat_1(B_115), k1_relat_1(A_116))=k1_relat_1(A_116) | k1_relat_1(k5_relat_1(B_115, A_116))!=k1_relat_1(B_115) | ~v1_funct_1(B_115) | ~v1_relat_1(B_115) | ~v1_funct_1(A_116) | ~v1_relat_1(A_116))), inference(resolution, [status(thm)], [c_216, c_4])).
% 3.31/1.50  tff(c_600, plain, (![B_131, B_132]: (k2_relat_1(B_131)=k1_relat_1(B_132) | k1_relat_1(k5_relat_1(B_131, B_132))!=k1_relat_1(B_131) | ~v1_funct_1(B_131) | ~v1_relat_1(B_131) | ~v1_funct_1(B_132) | ~v1_relat_1(B_132) | ~v4_relat_1(B_132, k2_relat_1(B_131)) | ~v1_relat_1(B_132))), inference(superposition, [status(thm), theory('equality')], [c_142, c_497])).
% 3.31/1.50  tff(c_603, plain, (![B_132]: (k2_relat_1('#skF_2')=k1_relat_1(B_132) | k1_relat_1(k5_relat_1('#skF_2', B_132))!=k1_relat_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_funct_1(B_132) | ~v1_relat_1(B_132) | ~v4_relat_1(B_132, '#skF_1') | ~v1_relat_1(B_132))), inference(superposition, [status(thm), theory('equality')], [c_205, c_600])).
% 3.31/1.50  tff(c_605, plain, (![B_132]: (k1_relat_1(B_132)='#skF_1' | k1_relat_1(k5_relat_1('#skF_2', B_132))!=k1_relat_1('#skF_2') | ~v1_funct_1(B_132) | ~v4_relat_1(B_132, '#skF_1') | ~v1_relat_1(B_132))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_50, c_205, c_603])).
% 3.31/1.50  tff(c_657, plain, (k1_relat_1('#skF_3')='#skF_1' | ~v1_funct_1('#skF_3') | ~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_650, c_605])).
% 3.31/1.50  tff(c_664, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_107, c_135, c_44, c_657])).
% 3.31/1.50  tff(c_32, plain, (![A_38]: (k6_relat_1(A_38)=k6_partfun1(A_38))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.31/1.50  tff(c_12, plain, (![B_12, A_10]: (k6_relat_1(k1_relat_1(B_12))=B_12 | k5_relat_1(A_10, B_12)!=A_10 | k2_relat_1(A_10)!=k1_relat_1(B_12) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.31/1.50  tff(c_51, plain, (![B_12, A_10]: (k6_partfun1(k1_relat_1(B_12))=B_12 | k5_relat_1(A_10, B_12)!=A_10 | k2_relat_1(A_10)!=k1_relat_1(B_12) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_12])).
% 3.31/1.50  tff(c_659, plain, (k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | k2_relat_1('#skF_2')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_650, c_51])).
% 3.31/1.50  tff(c_667, plain, (k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_50, c_107, c_44, c_205, c_659])).
% 3.31/1.50  tff(c_823, plain, (k6_partfun1('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_664, c_664, c_667])).
% 3.31/1.50  tff(c_34, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.31/1.50  tff(c_824, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_823, c_34])).
% 3.31/1.50  tff(c_827, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_196, c_824])).
% 3.31/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.50  
% 3.31/1.50  Inference rules
% 3.31/1.50  ----------------------
% 3.31/1.50  #Ref     : 0
% 3.31/1.50  #Sup     : 180
% 3.31/1.50  #Fact    : 0
% 3.31/1.50  #Define  : 0
% 3.31/1.50  #Split   : 1
% 3.31/1.50  #Chain   : 0
% 3.31/1.50  #Close   : 0
% 3.31/1.50  
% 3.31/1.50  Ordering : KBO
% 3.31/1.50  
% 3.31/1.50  Simplification rules
% 3.31/1.50  ----------------------
% 3.31/1.50  #Subsume      : 28
% 3.31/1.50  #Demod        : 131
% 3.31/1.50  #Tautology    : 60
% 3.31/1.50  #SimpNegUnit  : 1
% 3.31/1.50  #BackRed      : 10
% 3.31/1.50  
% 3.31/1.50  #Partial instantiations: 0
% 3.31/1.50  #Strategies tried      : 1
% 3.31/1.50  
% 3.31/1.50  Timing (in seconds)
% 3.31/1.50  ----------------------
% 3.31/1.51  Preprocessing        : 0.34
% 3.31/1.51  Parsing              : 0.19
% 3.31/1.51  CNF conversion       : 0.02
% 3.31/1.51  Main loop            : 0.40
% 3.31/1.51  Inferencing          : 0.15
% 3.31/1.51  Reduction            : 0.13
% 3.31/1.51  Demodulation         : 0.09
% 3.31/1.51  BG Simplification    : 0.02
% 3.31/1.51  Subsumption          : 0.07
% 3.31/1.51  Abstraction          : 0.02
% 3.31/1.51  MUC search           : 0.00
% 3.31/1.51  Cooper               : 0.00
% 3.31/1.51  Total                : 0.78
% 3.31/1.51  Index Insertion      : 0.00
% 3.31/1.51  Index Deletion       : 0.00
% 3.31/1.51  Index Matching       : 0.00
% 3.31/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
