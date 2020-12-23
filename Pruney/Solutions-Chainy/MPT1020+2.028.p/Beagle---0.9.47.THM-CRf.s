%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:54 EST 2020

% Result     : Theorem 5.79s
% Output     : CNFRefutation 6.01s
% Verified   : 
% Statistics : Number of formulae       :  228 (1834 expanded)
%              Number of leaves         :   49 ( 618 expanded)
%              Depth                    :   14
%              Number of atoms          :  421 (5400 expanded)
%              Number of equality atoms :  131 (1148 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k8_relat_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

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

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

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

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

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

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_202,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & v3_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,C),k6_partfun1(A))
             => r2_relset_1(A,A,C,k2_funct_2(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_124,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_120,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_180,axiom,(
    ! [A,B,C] :
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

tff(f_134,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_36,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_136,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_45,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k8_relat_1(k2_relat_1(A),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_66,axiom,(
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

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_185,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_202,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_185])).

tff(c_74,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_203,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_185])).

tff(c_331,plain,(
    ! [A_74,B_75,D_76] :
      ( r2_relset_1(A_74,B_75,D_76,D_76)
      | ~ m1_subset_1(D_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_342,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_331])).

tff(c_301,plain,(
    ! [C_69,B_70,A_71] :
      ( v5_relat_1(C_69,B_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_71,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_317,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_301])).

tff(c_353,plain,(
    ! [B_78,A_79] :
      ( k2_relat_1(B_78) = A_79
      | ~ v2_funct_2(B_78,A_79)
      | ~ v5_relat_1(B_78,A_79)
      | ~ v1_relat_1(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_362,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_317,c_353])).

tff(c_374,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_362])).

tff(c_408,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_374])).

tff(c_80,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_76,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_536,plain,(
    ! [C_95,B_96,A_97] :
      ( v2_funct_2(C_95,B_96)
      | ~ v3_funct_2(C_95,A_97,B_96)
      | ~ v1_funct_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_97,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_548,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_536])).

tff(c_557,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_548])).

tff(c_559,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_408,c_557])).

tff(c_560,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_374])).

tff(c_10,plain,(
    ! [A_4] :
      ( k2_relat_1(A_4) != k1_xboole_0
      | k1_xboole_0 = A_4
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_218,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_203,c_10])).

tff(c_235,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_563,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_235])).

tff(c_78,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_72,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_70,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_378,plain,(
    ! [A_80,B_81,C_82] :
      ( k2_relset_1(A_80,B_81,C_82) = k2_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_395,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_378])).

tff(c_562,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_395])).

tff(c_50,plain,(
    ! [A_33] : m1_subset_1(k6_partfun1(A_33),k1_zfmisc_1(k2_zfmisc_1(A_33,A_33))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_341,plain,(
    ! [A_33] : r2_relset_1(A_33,A_33,k6_partfun1(A_33),k6_partfun1(A_33)) ),
    inference(resolution,[status(thm)],[c_50,c_331])).

tff(c_583,plain,(
    ! [C_98,A_99,B_100] :
      ( v2_funct_1(C_98)
      | ~ v3_funct_2(C_98,A_99,B_100)
      | ~ v1_funct_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_595,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_583])).

tff(c_605,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_595])).

tff(c_887,plain,(
    ! [C_140,D_141,B_143,A_144,F_139,E_142] :
      ( m1_subset_1(k1_partfun1(A_144,B_143,C_140,D_141,E_142,F_139),k1_zfmisc_1(k2_zfmisc_1(A_144,D_141)))
      | ~ m1_subset_1(F_139,k1_zfmisc_1(k2_zfmisc_1(C_140,D_141)))
      | ~ v1_funct_1(F_139)
      | ~ m1_subset_1(E_142,k1_zfmisc_1(k2_zfmisc_1(A_144,B_143)))
      | ~ v1_funct_1(E_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_64,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_725,plain,(
    ! [D_112,C_113,A_114,B_115] :
      ( D_112 = C_113
      | ~ r2_relset_1(A_114,B_115,C_113,D_112)
      | ~ m1_subset_1(D_112,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115)))
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_735,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_64,c_725])).

tff(c_754,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_735])).

tff(c_785,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_754])).

tff(c_900,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_887,c_785])).

tff(c_932,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_74,c_72,c_66,c_900])).

tff(c_933,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_754])).

tff(c_1334,plain,(
    ! [C_205,D_206,B_207,A_208] :
      ( k2_funct_1(C_205) = D_206
      | k1_xboole_0 = B_207
      | k1_xboole_0 = A_208
      | ~ v2_funct_1(C_205)
      | ~ r2_relset_1(A_208,A_208,k1_partfun1(A_208,B_207,B_207,A_208,C_205,D_206),k6_partfun1(A_208))
      | k2_relset_1(A_208,B_207,C_205) != B_207
      | ~ m1_subset_1(D_206,k1_zfmisc_1(k2_zfmisc_1(B_207,A_208)))
      | ~ v1_funct_2(D_206,B_207,A_208)
      | ~ v1_funct_1(D_206)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_208,B_207)))
      | ~ v1_funct_2(C_205,A_208,B_207)
      | ~ v1_funct_1(C_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_1337,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_933,c_1334])).

tff(c_1342,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_74,c_72,c_70,c_66,c_562,c_341,c_605,c_1337])).

tff(c_1343,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_563,c_1342])).

tff(c_755,plain,(
    ! [A_116,B_117] :
      ( k2_funct_2(A_116,B_117) = k2_funct_1(B_117)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(k2_zfmisc_1(A_116,A_116)))
      | ~ v3_funct_2(B_117,A_116,A_116)
      | ~ v1_funct_2(B_117,A_116,A_116)
      | ~ v1_funct_1(B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_767,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_755])).

tff(c_775,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_767])).

tff(c_62,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_780,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_775,c_62])).

tff(c_1345,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1343,c_780])).

tff(c_1349,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_1345])).

tff(c_1350,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_8,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1365,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1350,c_1350,c_8])).

tff(c_12,plain,(
    ! [A_4] :
      ( k1_relat_1(A_4) != k1_xboole_0
      | k1_xboole_0 = A_4
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_219,plain,
    ( k1_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_203,c_12])).

tff(c_234,plain,(
    k1_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_219])).

tff(c_1432,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1365,c_1350,c_234])).

tff(c_1433,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_6,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1447,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1433,c_1433,c_6])).

tff(c_1478,plain,(
    ! [C_212,B_213,A_214] :
      ( v5_relat_1(C_212,B_213)
      | ~ m1_subset_1(C_212,k1_zfmisc_1(k2_zfmisc_1(A_214,B_213))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1490,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_1478])).

tff(c_1588,plain,(
    ! [B_225,A_226] :
      ( k2_relat_1(B_225) = A_226
      | ~ v2_funct_2(B_225,A_226)
      | ~ v5_relat_1(B_225,A_226)
      | ~ v1_relat_1(B_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1597,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1490,c_1588])).

tff(c_1609,plain,
    ( '#skF_2' = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_1447,c_1597])).

tff(c_1613,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1609])).

tff(c_1914,plain,(
    ! [C_254,B_255,A_256] :
      ( v2_funct_2(C_254,B_255)
      | ~ v3_funct_2(C_254,A_256,B_255)
      | ~ v1_funct_1(C_254)
      | ~ m1_subset_1(C_254,k1_zfmisc_1(k2_zfmisc_1(A_256,B_255))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1926,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_1914])).

tff(c_1936,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_1926])).

tff(c_1938,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1613,c_1936])).

tff(c_1939,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1609])).

tff(c_210,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_202,c_10])).

tff(c_220,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_210])).

tff(c_1436,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1433,c_220])).

tff(c_1950,plain,(
    k2_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1939,c_1436])).

tff(c_68,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_2078,plain,(
    ! [C_263,B_264,A_265] :
      ( v2_funct_2(C_263,B_264)
      | ~ v3_funct_2(C_263,A_265,B_264)
      | ~ v1_funct_1(C_263)
      | ~ m1_subset_1(C_263,k1_zfmisc_1(k2_zfmisc_1(A_265,B_264))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2084,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_2078])).

tff(c_2088,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_2084])).

tff(c_1489,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_1478])).

tff(c_1600,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1489,c_1588])).

tff(c_1612,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_1600])).

tff(c_2135,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2088,c_1612])).

tff(c_2136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1950,c_2135])).

tff(c_2137,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_2138,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_2685,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2137,c_2138])).

tff(c_2751,plain,(
    ! [C_313,B_314,A_315] :
      ( v5_relat_1(C_313,B_314)
      | ~ m1_subset_1(C_313,k1_zfmisc_1(k2_zfmisc_1(A_315,B_314))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2763,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_2751])).

tff(c_2806,plain,(
    ! [B_321,A_322] :
      ( k2_relat_1(B_321) = A_322
      | ~ v2_funct_2(B_321,A_322)
      | ~ v5_relat_1(B_321,A_322)
      | ~ v1_relat_1(B_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2815,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2763,c_2806])).

tff(c_2824,plain,
    ( '#skF_3' = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_2685,c_2815])).

tff(c_2825,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2824])).

tff(c_2938,plain,(
    ! [C_338,B_339,A_340] :
      ( v2_funct_2(C_338,B_339)
      | ~ v3_funct_2(C_338,A_340,B_339)
      | ~ v1_funct_1(C_338)
      | ~ m1_subset_1(C_338,k1_zfmisc_1(k2_zfmisc_1(A_340,B_339))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2947,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_2938])).

tff(c_2954,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_2947])).

tff(c_2956,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2825,c_2954])).

tff(c_2957,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2824])).

tff(c_2959,plain,(
    ! [A_341,B_342,D_343] :
      ( r2_relset_1(A_341,B_342,D_343,D_343)
      | ~ m1_subset_1(D_343,k1_zfmisc_1(k2_zfmisc_1(A_341,B_342))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2968,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_2959])).

tff(c_3091,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2957,c_2957,c_2968])).

tff(c_2993,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2957,c_72])).

tff(c_2150,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2137,c_2137,c_8])).

tff(c_2986,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2957,c_2957,c_2150])).

tff(c_100,plain,(
    ! [A_51] : k6_relat_1(A_51) = k6_partfun1(A_51) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_14,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_106,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_14])).

tff(c_54,plain,(
    ! [A_36] : k6_relat_1(A_36) = k6_partfun1(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_16,plain,(
    ! [A_5] : v1_relat_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_83,plain,(
    ! [A_5] : v1_relat_1(k6_partfun1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_16])).

tff(c_122,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_83])).

tff(c_151,plain,(
    ! [A_54] :
      ( k8_relat_1(k2_relat_1(A_54),A_54) = A_54
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_160,plain,
    ( k8_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_151])).

tff(c_164,plain,(
    k8_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_160])).

tff(c_2142,plain,(
    k8_relat_1('#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2137,c_2137,c_2137,c_164])).

tff(c_2976,plain,(
    k8_relat_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2957,c_2957,c_2957,c_2142])).

tff(c_2989,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2957,c_202])).

tff(c_2148,plain,(
    k6_partfun1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2137,c_2137,c_106])).

tff(c_2980,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2957,c_2957,c_2148])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k5_relat_1(B_2,k6_relat_1(A_1)) = k8_relat_1(A_1,B_2)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_84,plain,(
    ! [B_2,A_1] :
      ( k5_relat_1(B_2,k6_partfun1(A_1)) = k8_relat_1(A_1,B_2)
      | ~ v1_relat_1(B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2])).

tff(c_3242,plain,(
    ! [B_366] :
      ( k8_relat_1('#skF_1',B_366) = k5_relat_1(B_366,'#skF_1')
      | ~ v1_relat_1(B_366) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2980,c_84])).

tff(c_3245,plain,(
    k8_relat_1('#skF_1','#skF_1') = k5_relat_1('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_2989,c_3242])).

tff(c_3250,plain,(
    k5_relat_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2976,c_3245])).

tff(c_18,plain,(
    ! [A_5] : v2_funct_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_82,plain,(
    ! [A_5] : v2_funct_1(k6_partfun1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_18])).

tff(c_120,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_82])).

tff(c_2147,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2137,c_120])).

tff(c_2987,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2957,c_2147])).

tff(c_2982,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2957,c_2957,c_2685])).

tff(c_20,plain,(
    ! [A_6,B_8] :
      ( k2_funct_1(A_6) = B_8
      | k6_relat_1(k1_relat_1(A_6)) != k5_relat_1(A_6,B_8)
      | k2_relat_1(A_6) != k1_relat_1(B_8)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(B_8)
      | ~ v1_relat_1(B_8)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3283,plain,(
    ! [A_370,B_371] :
      ( k2_funct_1(A_370) = B_371
      | k6_partfun1(k1_relat_1(A_370)) != k5_relat_1(A_370,B_371)
      | k2_relat_1(A_370) != k1_relat_1(B_371)
      | ~ v2_funct_1(A_370)
      | ~ v1_funct_1(B_371)
      | ~ v1_relat_1(B_371)
      | ~ v1_funct_1(A_370)
      | ~ v1_relat_1(A_370) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_20])).

tff(c_3285,plain,(
    ! [B_371] :
      ( k2_funct_1('#skF_1') = B_371
      | k5_relat_1('#skF_1',B_371) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_1') != k1_relat_1(B_371)
      | ~ v2_funct_1('#skF_1')
      | ~ v1_funct_1(B_371)
      | ~ v1_relat_1(B_371)
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2986,c_3283])).

tff(c_3292,plain,(
    ! [B_372] :
      ( k2_funct_1('#skF_1') = B_372
      | k5_relat_1('#skF_1',B_372) != '#skF_1'
      | k1_relat_1(B_372) != '#skF_1'
      | ~ v1_funct_1(B_372)
      | ~ v1_relat_1(B_372) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2989,c_2993,c_2987,c_2982,c_2980,c_3285])).

tff(c_3295,plain,
    ( k2_funct_1('#skF_1') = '#skF_1'
    | k5_relat_1('#skF_1','#skF_1') != '#skF_1'
    | k1_relat_1('#skF_1') != '#skF_1'
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2989,c_3292])).

tff(c_3301,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2993,c_2986,c_3250,c_3295])).

tff(c_2991,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2957,c_70])).

tff(c_2992,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2957,c_68])).

tff(c_169,plain,(
    ! [A_55] : m1_subset_1(k6_partfun1(A_55),k1_zfmisc_1(k2_zfmisc_1(A_55,A_55))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_172,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_169])).

tff(c_2141,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2137,c_2137,c_2137,c_172])).

tff(c_2975,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2957,c_2957,c_2957,c_2141])).

tff(c_3226,plain,(
    ! [A_364,B_365] :
      ( k2_funct_2(A_364,B_365) = k2_funct_1(B_365)
      | ~ m1_subset_1(B_365,k1_zfmisc_1(k2_zfmisc_1(A_364,A_364)))
      | ~ v3_funct_2(B_365,A_364,A_364)
      | ~ v1_funct_2(B_365,A_364,A_364)
      | ~ v1_funct_1(B_365) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_3229,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2975,c_3226])).

tff(c_3235,plain,(
    k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2993,c_2991,c_2992,c_3229])).

tff(c_2186,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2137,c_2138])).

tff(c_2213,plain,(
    ! [C_269,B_270,A_271] :
      ( v5_relat_1(C_269,B_270)
      | ~ m1_subset_1(C_269,k1_zfmisc_1(k2_zfmisc_1(A_271,B_270))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2224,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_2213])).

tff(c_2324,plain,(
    ! [B_281,A_282] :
      ( k2_relat_1(B_281) = A_282
      | ~ v2_funct_2(B_281,A_282)
      | ~ v5_relat_1(B_281,A_282)
      | ~ v1_relat_1(B_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2336,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2224,c_2324])).

tff(c_2348,plain,
    ( '#skF_3' = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_2186,c_2336])).

tff(c_2349,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2348])).

tff(c_2447,plain,(
    ! [C_295,B_296,A_297] :
      ( v2_funct_2(C_295,B_296)
      | ~ v3_funct_2(C_295,A_297,B_296)
      | ~ v1_funct_1(C_295)
      | ~ m1_subset_1(C_295,k1_zfmisc_1(k2_zfmisc_1(A_297,B_296))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2456,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_2447])).

tff(c_2466,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_2456])).

tff(c_2468,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2349,c_2466])).

tff(c_2469,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2348])).

tff(c_2184,plain,
    ( k2_relat_1('#skF_2') != '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2137,c_2137,c_218])).

tff(c_2185,plain,(
    k2_relat_1('#skF_2') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2184])).

tff(c_2482,plain,(
    k2_relat_1('#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2469,c_2185])).

tff(c_2225,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_2213])).

tff(c_2333,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2225,c_2324])).

tff(c_2345,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_2333])).

tff(c_2611,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_2482,c_2345])).

tff(c_2646,plain,(
    ! [C_307,B_308,A_309] :
      ( v2_funct_2(C_307,B_308)
      | ~ v3_funct_2(C_307,A_309,B_308)
      | ~ v1_funct_1(C_307)
      | ~ m1_subset_1(C_307,k1_zfmisc_1(k2_zfmisc_1(A_309,B_308))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2655,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_2646])).

tff(c_2662,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_2655])).

tff(c_2664,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2611,c_2662])).

tff(c_2665,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2184])).

tff(c_2670,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2665,c_62])).

tff(c_2981,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2957,c_2957,c_2670])).

tff(c_3237,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3235,c_2981])).

tff(c_3304,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3301,c_3237])).

tff(c_3308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3091,c_3304])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:16:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.79/2.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.79/2.10  
% 5.79/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.79/2.11  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k8_relat_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.79/2.11  
% 5.79/2.11  %Foreground sorts:
% 5.79/2.11  
% 5.79/2.11  
% 5.79/2.11  %Background operators:
% 5.79/2.11  
% 5.79/2.11  
% 5.79/2.11  %Foreground operators:
% 5.79/2.11  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.79/2.11  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 5.79/2.11  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.79/2.11  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.79/2.11  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.79/2.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.79/2.11  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.79/2.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.79/2.11  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.79/2.11  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.79/2.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.79/2.11  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.79/2.11  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.79/2.11  tff('#skF_2', type, '#skF_2': $i).
% 5.79/2.11  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.79/2.11  tff('#skF_3', type, '#skF_3': $i).
% 5.79/2.11  tff('#skF_1', type, '#skF_1': $i).
% 5.79/2.11  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.79/2.11  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.79/2.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.79/2.11  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.79/2.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.79/2.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.79/2.11  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.79/2.11  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.79/2.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.79/2.11  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.79/2.11  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.79/2.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.79/2.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.79/2.11  
% 6.01/2.14  tff(f_202, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_2)).
% 6.01/2.14  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.01/2.14  tff(f_88, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.01/2.14  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.01/2.14  tff(f_108, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 6.01/2.14  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 6.01/2.14  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 6.01/2.14  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.01/2.14  tff(f_124, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.01/2.14  tff(f_120, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.01/2.14  tff(f_180, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 6.01/2.14  tff(f_134, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 6.01/2.14  tff(f_36, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 6.01/2.14  tff(f_136, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.01/2.14  tff(f_45, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 6.01/2.14  tff(f_49, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 6.01/2.14  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k8_relat_1(k2_relat_1(A), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_relat_1)).
% 6.01/2.14  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 6.01/2.14  tff(f_66, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 6.01/2.14  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.01/2.14  tff(c_185, plain, (![C_58, A_59, B_60]: (v1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.01/2.14  tff(c_202, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_185])).
% 6.01/2.14  tff(c_74, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.01/2.14  tff(c_203, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_185])).
% 6.01/2.14  tff(c_331, plain, (![A_74, B_75, D_76]: (r2_relset_1(A_74, B_75, D_76, D_76) | ~m1_subset_1(D_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.01/2.14  tff(c_342, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_331])).
% 6.01/2.14  tff(c_301, plain, (![C_69, B_70, A_71]: (v5_relat_1(C_69, B_70) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_71, B_70))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.01/2.14  tff(c_317, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_74, c_301])).
% 6.01/2.14  tff(c_353, plain, (![B_78, A_79]: (k2_relat_1(B_78)=A_79 | ~v2_funct_2(B_78, A_79) | ~v5_relat_1(B_78, A_79) | ~v1_relat_1(B_78))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.01/2.14  tff(c_362, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_317, c_353])).
% 6.01/2.14  tff(c_374, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_203, c_362])).
% 6.01/2.14  tff(c_408, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_374])).
% 6.01/2.14  tff(c_80, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.01/2.14  tff(c_76, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.01/2.14  tff(c_536, plain, (![C_95, B_96, A_97]: (v2_funct_2(C_95, B_96) | ~v3_funct_2(C_95, A_97, B_96) | ~v1_funct_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_97, B_96))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.01/2.14  tff(c_548, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_536])).
% 6.01/2.14  tff(c_557, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_548])).
% 6.01/2.14  tff(c_559, plain, $false, inference(negUnitSimplification, [status(thm)], [c_408, c_557])).
% 6.01/2.14  tff(c_560, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_374])).
% 6.01/2.14  tff(c_10, plain, (![A_4]: (k2_relat_1(A_4)!=k1_xboole_0 | k1_xboole_0=A_4 | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.01/2.14  tff(c_218, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_203, c_10])).
% 6.01/2.14  tff(c_235, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_218])).
% 6.01/2.14  tff(c_563, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_560, c_235])).
% 6.01/2.14  tff(c_78, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.01/2.14  tff(c_72, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.01/2.14  tff(c_70, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.01/2.14  tff(c_378, plain, (![A_80, B_81, C_82]: (k2_relset_1(A_80, B_81, C_82)=k2_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.01/2.14  tff(c_395, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_378])).
% 6.01/2.14  tff(c_562, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_560, c_395])).
% 6.01/2.14  tff(c_50, plain, (![A_33]: (m1_subset_1(k6_partfun1(A_33), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.01/2.14  tff(c_341, plain, (![A_33]: (r2_relset_1(A_33, A_33, k6_partfun1(A_33), k6_partfun1(A_33)))), inference(resolution, [status(thm)], [c_50, c_331])).
% 6.01/2.14  tff(c_583, plain, (![C_98, A_99, B_100]: (v2_funct_1(C_98) | ~v3_funct_2(C_98, A_99, B_100) | ~v1_funct_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.01/2.14  tff(c_595, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_583])).
% 6.01/2.14  tff(c_605, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_595])).
% 6.01/2.14  tff(c_887, plain, (![C_140, D_141, B_143, A_144, F_139, E_142]: (m1_subset_1(k1_partfun1(A_144, B_143, C_140, D_141, E_142, F_139), k1_zfmisc_1(k2_zfmisc_1(A_144, D_141))) | ~m1_subset_1(F_139, k1_zfmisc_1(k2_zfmisc_1(C_140, D_141))) | ~v1_funct_1(F_139) | ~m1_subset_1(E_142, k1_zfmisc_1(k2_zfmisc_1(A_144, B_143))) | ~v1_funct_1(E_142))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.01/2.14  tff(c_64, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.01/2.14  tff(c_725, plain, (![D_112, C_113, A_114, B_115]: (D_112=C_113 | ~r2_relset_1(A_114, B_115, C_113, D_112) | ~m1_subset_1(D_112, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.01/2.14  tff(c_735, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_64, c_725])).
% 6.01/2.14  tff(c_754, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_735])).
% 6.01/2.14  tff(c_785, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_754])).
% 6.01/2.14  tff(c_900, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_887, c_785])).
% 6.01/2.14  tff(c_932, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_74, c_72, c_66, c_900])).
% 6.01/2.14  tff(c_933, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_754])).
% 6.01/2.14  tff(c_1334, plain, (![C_205, D_206, B_207, A_208]: (k2_funct_1(C_205)=D_206 | k1_xboole_0=B_207 | k1_xboole_0=A_208 | ~v2_funct_1(C_205) | ~r2_relset_1(A_208, A_208, k1_partfun1(A_208, B_207, B_207, A_208, C_205, D_206), k6_partfun1(A_208)) | k2_relset_1(A_208, B_207, C_205)!=B_207 | ~m1_subset_1(D_206, k1_zfmisc_1(k2_zfmisc_1(B_207, A_208))) | ~v1_funct_2(D_206, B_207, A_208) | ~v1_funct_1(D_206) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(A_208, B_207))) | ~v1_funct_2(C_205, A_208, B_207) | ~v1_funct_1(C_205))), inference(cnfTransformation, [status(thm)], [f_180])).
% 6.01/2.14  tff(c_1337, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_933, c_1334])).
% 6.01/2.14  tff(c_1342, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_74, c_72, c_70, c_66, c_562, c_341, c_605, c_1337])).
% 6.01/2.14  tff(c_1343, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_563, c_1342])).
% 6.01/2.14  tff(c_755, plain, (![A_116, B_117]: (k2_funct_2(A_116, B_117)=k2_funct_1(B_117) | ~m1_subset_1(B_117, k1_zfmisc_1(k2_zfmisc_1(A_116, A_116))) | ~v3_funct_2(B_117, A_116, A_116) | ~v1_funct_2(B_117, A_116, A_116) | ~v1_funct_1(B_117))), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.01/2.14  tff(c_767, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_755])).
% 6.01/2.14  tff(c_775, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_767])).
% 6.01/2.14  tff(c_62, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.01/2.14  tff(c_780, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_775, c_62])).
% 6.01/2.14  tff(c_1345, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1343, c_780])).
% 6.01/2.14  tff(c_1349, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_342, c_1345])).
% 6.01/2.14  tff(c_1350, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_218])).
% 6.01/2.14  tff(c_8, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.01/2.14  tff(c_1365, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1350, c_1350, c_8])).
% 6.01/2.14  tff(c_12, plain, (![A_4]: (k1_relat_1(A_4)!=k1_xboole_0 | k1_xboole_0=A_4 | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.01/2.14  tff(c_219, plain, (k1_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_203, c_12])).
% 6.01/2.14  tff(c_234, plain, (k1_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_219])).
% 6.01/2.14  tff(c_1432, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1365, c_1350, c_234])).
% 6.01/2.14  tff(c_1433, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_219])).
% 6.01/2.14  tff(c_6, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.01/2.14  tff(c_1447, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1433, c_1433, c_6])).
% 6.01/2.14  tff(c_1478, plain, (![C_212, B_213, A_214]: (v5_relat_1(C_212, B_213) | ~m1_subset_1(C_212, k1_zfmisc_1(k2_zfmisc_1(A_214, B_213))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.01/2.14  tff(c_1490, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_74, c_1478])).
% 6.01/2.14  tff(c_1588, plain, (![B_225, A_226]: (k2_relat_1(B_225)=A_226 | ~v2_funct_2(B_225, A_226) | ~v5_relat_1(B_225, A_226) | ~v1_relat_1(B_225))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.01/2.14  tff(c_1597, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1490, c_1588])).
% 6.01/2.14  tff(c_1609, plain, ('#skF_2'='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_203, c_1447, c_1597])).
% 6.01/2.14  tff(c_1613, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_1609])).
% 6.01/2.14  tff(c_1914, plain, (![C_254, B_255, A_256]: (v2_funct_2(C_254, B_255) | ~v3_funct_2(C_254, A_256, B_255) | ~v1_funct_1(C_254) | ~m1_subset_1(C_254, k1_zfmisc_1(k2_zfmisc_1(A_256, B_255))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.01/2.14  tff(c_1926, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_1914])).
% 6.01/2.14  tff(c_1936, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_1926])).
% 6.01/2.14  tff(c_1938, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1613, c_1936])).
% 6.01/2.14  tff(c_1939, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_1609])).
% 6.01/2.14  tff(c_210, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_202, c_10])).
% 6.01/2.14  tff(c_220, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_210])).
% 6.01/2.14  tff(c_1436, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1433, c_220])).
% 6.01/2.14  tff(c_1950, plain, (k2_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1939, c_1436])).
% 6.01/2.14  tff(c_68, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.01/2.14  tff(c_2078, plain, (![C_263, B_264, A_265]: (v2_funct_2(C_263, B_264) | ~v3_funct_2(C_263, A_265, B_264) | ~v1_funct_1(C_263) | ~m1_subset_1(C_263, k1_zfmisc_1(k2_zfmisc_1(A_265, B_264))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.01/2.14  tff(c_2084, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_2078])).
% 6.01/2.14  tff(c_2088, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_2084])).
% 6.01/2.14  tff(c_1489, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_1478])).
% 6.01/2.14  tff(c_1600, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1489, c_1588])).
% 6.01/2.14  tff(c_1612, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_202, c_1600])).
% 6.01/2.14  tff(c_2135, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2088, c_1612])).
% 6.01/2.14  tff(c_2136, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1950, c_2135])).
% 6.01/2.14  tff(c_2137, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_210])).
% 6.01/2.14  tff(c_2138, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_210])).
% 6.01/2.14  tff(c_2685, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2137, c_2138])).
% 6.01/2.14  tff(c_2751, plain, (![C_313, B_314, A_315]: (v5_relat_1(C_313, B_314) | ~m1_subset_1(C_313, k1_zfmisc_1(k2_zfmisc_1(A_315, B_314))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.01/2.14  tff(c_2763, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_2751])).
% 6.01/2.14  tff(c_2806, plain, (![B_321, A_322]: (k2_relat_1(B_321)=A_322 | ~v2_funct_2(B_321, A_322) | ~v5_relat_1(B_321, A_322) | ~v1_relat_1(B_321))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.01/2.14  tff(c_2815, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2763, c_2806])).
% 6.01/2.14  tff(c_2824, plain, ('#skF_3'='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_202, c_2685, c_2815])).
% 6.01/2.14  tff(c_2825, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_2824])).
% 6.01/2.14  tff(c_2938, plain, (![C_338, B_339, A_340]: (v2_funct_2(C_338, B_339) | ~v3_funct_2(C_338, A_340, B_339) | ~v1_funct_1(C_338) | ~m1_subset_1(C_338, k1_zfmisc_1(k2_zfmisc_1(A_340, B_339))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.01/2.14  tff(c_2947, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_2938])).
% 6.01/2.14  tff(c_2954, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_2947])).
% 6.01/2.14  tff(c_2956, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2825, c_2954])).
% 6.01/2.14  tff(c_2957, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_2824])).
% 6.01/2.14  tff(c_2959, plain, (![A_341, B_342, D_343]: (r2_relset_1(A_341, B_342, D_343, D_343) | ~m1_subset_1(D_343, k1_zfmisc_1(k2_zfmisc_1(A_341, B_342))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.01/2.14  tff(c_2968, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_2959])).
% 6.01/2.14  tff(c_3091, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2957, c_2957, c_2968])).
% 6.01/2.14  tff(c_2993, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2957, c_72])).
% 6.01/2.14  tff(c_2150, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2137, c_2137, c_8])).
% 6.01/2.14  tff(c_2986, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2957, c_2957, c_2150])).
% 6.01/2.14  tff(c_100, plain, (![A_51]: (k6_relat_1(A_51)=k6_partfun1(A_51))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.01/2.14  tff(c_14, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.01/2.14  tff(c_106, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_100, c_14])).
% 6.01/2.14  tff(c_54, plain, (![A_36]: (k6_relat_1(A_36)=k6_partfun1(A_36))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.01/2.14  tff(c_16, plain, (![A_5]: (v1_relat_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.01/2.14  tff(c_83, plain, (![A_5]: (v1_relat_1(k6_partfun1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_16])).
% 6.01/2.14  tff(c_122, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_106, c_83])).
% 6.01/2.14  tff(c_151, plain, (![A_54]: (k8_relat_1(k2_relat_1(A_54), A_54)=A_54 | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.01/2.14  tff(c_160, plain, (k8_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_151])).
% 6.01/2.14  tff(c_164, plain, (k8_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_122, c_160])).
% 6.01/2.14  tff(c_2142, plain, (k8_relat_1('#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2137, c_2137, c_2137, c_164])).
% 6.01/2.14  tff(c_2976, plain, (k8_relat_1('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2957, c_2957, c_2957, c_2142])).
% 6.01/2.14  tff(c_2989, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2957, c_202])).
% 6.01/2.14  tff(c_2148, plain, (k6_partfun1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2137, c_2137, c_106])).
% 6.01/2.14  tff(c_2980, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2957, c_2957, c_2148])).
% 6.01/2.14  tff(c_2, plain, (![B_2, A_1]: (k5_relat_1(B_2, k6_relat_1(A_1))=k8_relat_1(A_1, B_2) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.01/2.14  tff(c_84, plain, (![B_2, A_1]: (k5_relat_1(B_2, k6_partfun1(A_1))=k8_relat_1(A_1, B_2) | ~v1_relat_1(B_2))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2])).
% 6.01/2.14  tff(c_3242, plain, (![B_366]: (k8_relat_1('#skF_1', B_366)=k5_relat_1(B_366, '#skF_1') | ~v1_relat_1(B_366))), inference(superposition, [status(thm), theory('equality')], [c_2980, c_84])).
% 6.01/2.14  tff(c_3245, plain, (k8_relat_1('#skF_1', '#skF_1')=k5_relat_1('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_2989, c_3242])).
% 6.01/2.14  tff(c_3250, plain, (k5_relat_1('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2976, c_3245])).
% 6.01/2.14  tff(c_18, plain, (![A_5]: (v2_funct_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.01/2.14  tff(c_82, plain, (![A_5]: (v2_funct_1(k6_partfun1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_18])).
% 6.01/2.14  tff(c_120, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_106, c_82])).
% 6.01/2.14  tff(c_2147, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2137, c_120])).
% 6.01/2.14  tff(c_2987, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2957, c_2147])).
% 6.01/2.14  tff(c_2982, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2957, c_2957, c_2685])).
% 6.01/2.14  tff(c_20, plain, (![A_6, B_8]: (k2_funct_1(A_6)=B_8 | k6_relat_1(k1_relat_1(A_6))!=k5_relat_1(A_6, B_8) | k2_relat_1(A_6)!=k1_relat_1(B_8) | ~v2_funct_1(A_6) | ~v1_funct_1(B_8) | ~v1_relat_1(B_8) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.01/2.14  tff(c_3283, plain, (![A_370, B_371]: (k2_funct_1(A_370)=B_371 | k6_partfun1(k1_relat_1(A_370))!=k5_relat_1(A_370, B_371) | k2_relat_1(A_370)!=k1_relat_1(B_371) | ~v2_funct_1(A_370) | ~v1_funct_1(B_371) | ~v1_relat_1(B_371) | ~v1_funct_1(A_370) | ~v1_relat_1(A_370))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_20])).
% 6.01/2.14  tff(c_3285, plain, (![B_371]: (k2_funct_1('#skF_1')=B_371 | k5_relat_1('#skF_1', B_371)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_1')!=k1_relat_1(B_371) | ~v2_funct_1('#skF_1') | ~v1_funct_1(B_371) | ~v1_relat_1(B_371) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2986, c_3283])).
% 6.01/2.14  tff(c_3292, plain, (![B_372]: (k2_funct_1('#skF_1')=B_372 | k5_relat_1('#skF_1', B_372)!='#skF_1' | k1_relat_1(B_372)!='#skF_1' | ~v1_funct_1(B_372) | ~v1_relat_1(B_372))), inference(demodulation, [status(thm), theory('equality')], [c_2989, c_2993, c_2987, c_2982, c_2980, c_3285])).
% 6.01/2.14  tff(c_3295, plain, (k2_funct_1('#skF_1')='#skF_1' | k5_relat_1('#skF_1', '#skF_1')!='#skF_1' | k1_relat_1('#skF_1')!='#skF_1' | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_2989, c_3292])).
% 6.01/2.14  tff(c_3301, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2993, c_2986, c_3250, c_3295])).
% 6.01/2.14  tff(c_2991, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2957, c_70])).
% 6.01/2.14  tff(c_2992, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2957, c_68])).
% 6.01/2.14  tff(c_169, plain, (![A_55]: (m1_subset_1(k6_partfun1(A_55), k1_zfmisc_1(k2_zfmisc_1(A_55, A_55))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.01/2.14  tff(c_172, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_106, c_169])).
% 6.01/2.14  tff(c_2141, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2137, c_2137, c_2137, c_172])).
% 6.01/2.14  tff(c_2975, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2957, c_2957, c_2957, c_2141])).
% 6.01/2.14  tff(c_3226, plain, (![A_364, B_365]: (k2_funct_2(A_364, B_365)=k2_funct_1(B_365) | ~m1_subset_1(B_365, k1_zfmisc_1(k2_zfmisc_1(A_364, A_364))) | ~v3_funct_2(B_365, A_364, A_364) | ~v1_funct_2(B_365, A_364, A_364) | ~v1_funct_1(B_365))), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.01/2.14  tff(c_3229, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_2975, c_3226])).
% 6.01/2.14  tff(c_3235, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2993, c_2991, c_2992, c_3229])).
% 6.01/2.14  tff(c_2186, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2137, c_2138])).
% 6.01/2.14  tff(c_2213, plain, (![C_269, B_270, A_271]: (v5_relat_1(C_269, B_270) | ~m1_subset_1(C_269, k1_zfmisc_1(k2_zfmisc_1(A_271, B_270))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.01/2.14  tff(c_2224, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_2213])).
% 6.01/2.14  tff(c_2324, plain, (![B_281, A_282]: (k2_relat_1(B_281)=A_282 | ~v2_funct_2(B_281, A_282) | ~v5_relat_1(B_281, A_282) | ~v1_relat_1(B_281))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.01/2.14  tff(c_2336, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2224, c_2324])).
% 6.01/2.14  tff(c_2348, plain, ('#skF_3'='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_202, c_2186, c_2336])).
% 6.01/2.14  tff(c_2349, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_2348])).
% 6.01/2.14  tff(c_2447, plain, (![C_295, B_296, A_297]: (v2_funct_2(C_295, B_296) | ~v3_funct_2(C_295, A_297, B_296) | ~v1_funct_1(C_295) | ~m1_subset_1(C_295, k1_zfmisc_1(k2_zfmisc_1(A_297, B_296))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.01/2.14  tff(c_2456, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_2447])).
% 6.01/2.14  tff(c_2466, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_2456])).
% 6.01/2.14  tff(c_2468, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2349, c_2466])).
% 6.01/2.14  tff(c_2469, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_2348])).
% 6.01/2.14  tff(c_2184, plain, (k2_relat_1('#skF_2')!='#skF_3' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2137, c_2137, c_218])).
% 6.01/2.14  tff(c_2185, plain, (k2_relat_1('#skF_2')!='#skF_3'), inference(splitLeft, [status(thm)], [c_2184])).
% 6.01/2.14  tff(c_2482, plain, (k2_relat_1('#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2469, c_2185])).
% 6.01/2.14  tff(c_2225, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_74, c_2213])).
% 6.01/2.14  tff(c_2333, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2225, c_2324])).
% 6.01/2.14  tff(c_2345, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_203, c_2333])).
% 6.01/2.14  tff(c_2611, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_2482, c_2345])).
% 6.01/2.14  tff(c_2646, plain, (![C_307, B_308, A_309]: (v2_funct_2(C_307, B_308) | ~v3_funct_2(C_307, A_309, B_308) | ~v1_funct_1(C_307) | ~m1_subset_1(C_307, k1_zfmisc_1(k2_zfmisc_1(A_309, B_308))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.01/2.14  tff(c_2655, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_2646])).
% 6.01/2.14  tff(c_2662, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_2655])).
% 6.01/2.14  tff(c_2664, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2611, c_2662])).
% 6.01/2.14  tff(c_2665, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_2184])).
% 6.01/2.14  tff(c_2670, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2665, c_62])).
% 6.01/2.14  tff(c_2981, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2957, c_2957, c_2670])).
% 6.01/2.14  tff(c_3237, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3235, c_2981])).
% 6.01/2.14  tff(c_3304, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3301, c_3237])).
% 6.01/2.14  tff(c_3308, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3091, c_3304])).
% 6.01/2.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.01/2.14  
% 6.01/2.14  Inference rules
% 6.01/2.14  ----------------------
% 6.01/2.14  #Ref     : 0
% 6.01/2.14  #Sup     : 728
% 6.01/2.14  #Fact    : 0
% 6.01/2.14  #Define  : 0
% 6.01/2.14  #Split   : 24
% 6.01/2.14  #Chain   : 0
% 6.01/2.14  #Close   : 0
% 6.01/2.14  
% 6.01/2.14  Ordering : KBO
% 6.01/2.14  
% 6.01/2.14  Simplification rules
% 6.01/2.14  ----------------------
% 6.01/2.14  #Subsume      : 50
% 6.01/2.14  #Demod        : 857
% 6.01/2.14  #Tautology    : 447
% 6.01/2.14  #SimpNegUnit  : 11
% 6.01/2.14  #BackRed      : 143
% 6.01/2.14  
% 6.01/2.14  #Partial instantiations: 0
% 6.01/2.14  #Strategies tried      : 1
% 6.01/2.14  
% 6.01/2.14  Timing (in seconds)
% 6.01/2.14  ----------------------
% 6.01/2.14  Preprocessing        : 0.39
% 6.01/2.14  Parsing              : 0.21
% 6.01/2.14  CNF conversion       : 0.03
% 6.01/2.14  Main loop            : 0.95
% 6.01/2.14  Inferencing          : 0.33
% 6.01/2.14  Reduction            : 0.35
% 6.01/2.14  Demodulation         : 0.25
% 6.01/2.14  BG Simplification    : 0.04
% 6.01/2.14  Subsumption          : 0.15
% 6.01/2.14  Abstraction          : 0.04
% 6.01/2.14  MUC search           : 0.00
% 6.01/2.14  Cooper               : 0.00
% 6.01/2.14  Total                : 1.41
% 6.01/2.14  Index Insertion      : 0.00
% 6.01/2.14  Index Deletion       : 0.00
% 6.01/2.14  Index Matching       : 0.00
% 6.01/2.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
