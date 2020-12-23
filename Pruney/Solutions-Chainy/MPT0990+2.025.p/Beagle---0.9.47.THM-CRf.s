%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:59 EST 2020

% Result     : Theorem 11.88s
% Output     : CNFRefutation 12.18s
% Verified   : 
% Statistics : Number of formulae       :  225 (1538 expanded)
%              Number of leaves         :   47 ( 561 expanded)
%              Depth                    :   17
%              Number of atoms          :  557 (6229 expanded)
%              Number of equality atoms :  158 (2113 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(f_238,negated_conjecture,(
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

tff(f_119,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_123,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_155,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_179,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_49,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_137,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_35,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & k2_relat_1(B) = k1_relat_1(A) )
           => ( v2_funct_1(B)
              & v2_funct_1(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_177,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_135,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_167,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_127,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_212,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_196,axiom,(
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

tff(f_115,axiom,(
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

tff(f_98,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(c_78,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_94,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_92,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_90,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_144,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_155,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_90,c_144])).

tff(c_82,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_352,plain,(
    ! [A_86,B_87,C_88] :
      ( k1_relset_1(A_86,B_87,C_88) = k1_relat_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_364,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_90,c_352])).

tff(c_445,plain,(
    ! [B_103,A_104,C_105] :
      ( k1_xboole_0 = B_103
      | k1_relset_1(A_104,B_103,C_105) = A_104
      | ~ v1_funct_2(C_105,A_104,B_103)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_104,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_451,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_90,c_445])).

tff(c_459,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_364,c_451])).

tff(c_460,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_459])).

tff(c_28,plain,(
    ! [A_11] :
      ( k2_relat_1(k2_funct_1(A_11)) = k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ! [A_45] : k6_relat_1(A_45) = k6_partfun1(A_45) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_12,plain,(
    ! [B_5,A_4] :
      ( k5_relat_1(B_5,k6_relat_1(A_4)) = B_5
      | ~ r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_195,plain,(
    ! [B_75,A_76] :
      ( k5_relat_1(B_75,k6_partfun1(A_76)) = B_75
      | ~ r1_tarski(k2_relat_1(B_75),A_76)
      | ~ v1_relat_1(B_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_12])).

tff(c_209,plain,(
    ! [B_77] :
      ( k5_relat_1(B_77,k6_partfun1(k2_relat_1(B_77))) = B_77
      | ~ v1_relat_1(B_77) ) ),
    inference(resolution,[status(thm)],[c_6,c_195])).

tff(c_534,plain,(
    ! [A_110] :
      ( k5_relat_1(k2_funct_1(A_110),k6_partfun1(k1_relat_1(A_110))) = k2_funct_1(A_110)
      | ~ v1_relat_1(k2_funct_1(A_110))
      | ~ v2_funct_1(A_110)
      | ~ v1_funct_1(A_110)
      | ~ v1_relat_1(A_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_209])).

tff(c_549,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),k6_partfun1('#skF_2')) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_460,c_534])).

tff(c_563,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),k6_partfun1('#skF_2')) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_94,c_549])).

tff(c_615,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_563])).

tff(c_96,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_156,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_144])).

tff(c_100,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_84,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_18,plain,(
    ! [A_7] :
      ( v2_funct_1(k2_funct_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    ! [A_6] :
      ( v1_funct_1(k2_funct_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_80,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_98,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_365,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_352])).

tff(c_454,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_96,c_445])).

tff(c_463,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_365,c_454])).

tff(c_464,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_463])).

tff(c_48,plain,(
    ! [A_29] : m1_subset_1(k6_relat_1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_101,plain,(
    ! [A_29] : m1_subset_1(k6_partfun1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_48])).

tff(c_154,plain,(
    ! [A_29] : v1_relat_1(k6_partfun1(A_29)) ),
    inference(resolution,[status(thm)],[c_101,c_144])).

tff(c_16,plain,(
    ! [A_6] :
      ( v1_relat_1(k2_funct_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_546,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_464,c_534])).

tff(c_561,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_100,c_84,c_546])).

tff(c_605,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_561])).

tff(c_608,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_605])).

tff(c_612,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_100,c_608])).

tff(c_614,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_561])).

tff(c_8,plain,(
    ! [A_3] : k1_relat_1(k6_relat_1(A_3)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_107,plain,(
    ! [A_3] : k1_relat_1(k6_partfun1(A_3)) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_8])).

tff(c_613,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_561])).

tff(c_24,plain,(
    ! [A_8,B_10] :
      ( v2_funct_1(A_8)
      | k2_relat_1(B_10) != k1_relat_1(A_8)
      | ~ v2_funct_1(k5_relat_1(B_10,A_8))
      | ~ v1_funct_1(B_10)
      | ~ v1_relat_1(B_10)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_622,plain,
    ( v2_funct_1(k6_partfun1('#skF_1'))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1(k6_partfun1('#skF_1'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_relat_1(k6_partfun1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_613,c_24])).

tff(c_628,plain,
    ( v2_funct_1(k6_partfun1('#skF_1'))
    | k2_relat_1(k2_funct_1('#skF_3')) != '#skF_1'
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_614,c_107,c_622])).

tff(c_630,plain,(
    ~ v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_628])).

tff(c_1174,plain,(
    ! [C_176,A_174,D_177,F_178,B_175,E_179] :
      ( k1_partfun1(A_174,B_175,C_176,D_177,E_179,F_178) = k5_relat_1(E_179,F_178)
      | ~ m1_subset_1(F_178,k1_zfmisc_1(k2_zfmisc_1(C_176,D_177)))
      | ~ v1_funct_1(F_178)
      | ~ m1_subset_1(E_179,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175)))
      | ~ v1_funct_1(E_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_1180,plain,(
    ! [A_174,B_175,E_179] :
      ( k1_partfun1(A_174,B_175,'#skF_2','#skF_1',E_179,'#skF_4') = k5_relat_1(E_179,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_179,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175)))
      | ~ v1_funct_1(E_179) ) ),
    inference(resolution,[status(thm)],[c_90,c_1174])).

tff(c_1191,plain,(
    ! [A_180,B_181,E_182] :
      ( k1_partfun1(A_180,B_181,'#skF_2','#skF_1',E_182,'#skF_4') = k5_relat_1(E_182,'#skF_4')
      | ~ m1_subset_1(E_182,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181)))
      | ~ v1_funct_1(E_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_1180])).

tff(c_1203,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_1191])).

tff(c_1211,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_1203])).

tff(c_86,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_631,plain,(
    ! [D_113,C_114,A_115,B_116] :
      ( D_113 = C_114
      | ~ r2_relset_1(A_115,B_116,C_114,D_113)
      | ~ m1_subset_1(D_113,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116)))
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_639,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_86,c_631])).

tff(c_654,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_639])).

tff(c_682,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_654])).

tff(c_1218,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1211,c_682])).

tff(c_1230,plain,(
    ! [D_188,B_189,E_185,F_187,C_186,A_184] :
      ( m1_subset_1(k1_partfun1(A_184,B_189,C_186,D_188,E_185,F_187),k1_zfmisc_1(k2_zfmisc_1(A_184,D_188)))
      | ~ m1_subset_1(F_187,k1_zfmisc_1(k2_zfmisc_1(C_186,D_188)))
      | ~ v1_funct_1(F_187)
      | ~ m1_subset_1(E_185,k1_zfmisc_1(k2_zfmisc_1(A_184,B_189)))
      | ~ v1_funct_1(E_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_1289,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1211,c_1230])).

tff(c_1313,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_96,c_94,c_90,c_1289])).

tff(c_1315,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1218,c_1313])).

tff(c_1316,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_654])).

tff(c_1325,plain,(
    ! [E_191,A_190,D_194,F_193,B_195,C_192] :
      ( v1_funct_1(k1_partfun1(A_190,B_195,C_192,D_194,E_191,F_193))
      | ~ m1_subset_1(F_193,k1_zfmisc_1(k2_zfmisc_1(C_192,D_194)))
      | ~ v1_funct_1(F_193)
      | ~ m1_subset_1(E_191,k1_zfmisc_1(k2_zfmisc_1(A_190,B_195)))
      | ~ v1_funct_1(E_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_1329,plain,(
    ! [A_190,B_195,E_191] :
      ( v1_funct_1(k1_partfun1(A_190,B_195,'#skF_2','#skF_1',E_191,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_191,k1_zfmisc_1(k2_zfmisc_1(A_190,B_195)))
      | ~ v1_funct_1(E_191) ) ),
    inference(resolution,[status(thm)],[c_90,c_1325])).

tff(c_1340,plain,(
    ! [A_197,B_198,E_199] :
      ( v1_funct_1(k1_partfun1(A_197,B_198,'#skF_2','#skF_1',E_199,'#skF_4'))
      | ~ m1_subset_1(E_199,k1_zfmisc_1(k2_zfmisc_1(A_197,B_198)))
      | ~ v1_funct_1(E_199) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_1329])).

tff(c_1349,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_1340])).

tff(c_1356,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_1316,c_1349])).

tff(c_1358,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_630,c_1356])).

tff(c_1359,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relat_1(k2_funct_1('#skF_3')) != '#skF_1'
    | v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_628])).

tff(c_1361,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1359])).

tff(c_1364,plain,
    ( k1_relat_1('#skF_3') != '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1361])).

tff(c_1367,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_100,c_84,c_464,c_1364])).

tff(c_1368,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1359])).

tff(c_1423,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1368])).

tff(c_1426,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_1423])).

tff(c_1430,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_100,c_1426])).

tff(c_1431,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_3'))
    | v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1368])).

tff(c_2239,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1431])).

tff(c_2242,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_2239])).

tff(c_2246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_100,c_84,c_2242])).

tff(c_2247,plain,(
    v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1431])).

tff(c_88,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_271,plain,(
    ! [A_81,B_82,C_83] :
      ( k2_relset_1(A_81,B_82,C_83) = k2_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_280,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_271])).

tff(c_285,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_280])).

tff(c_2044,plain,(
    ! [A_245,D_248,F_249,C_247,E_250,B_246] :
      ( k1_partfun1(A_245,B_246,C_247,D_248,E_250,F_249) = k5_relat_1(E_250,F_249)
      | ~ m1_subset_1(F_249,k1_zfmisc_1(k2_zfmisc_1(C_247,D_248)))
      | ~ v1_funct_1(F_249)
      | ~ m1_subset_1(E_250,k1_zfmisc_1(k2_zfmisc_1(A_245,B_246)))
      | ~ v1_funct_1(E_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_2050,plain,(
    ! [A_245,B_246,E_250] :
      ( k1_partfun1(A_245,B_246,'#skF_2','#skF_1',E_250,'#skF_4') = k5_relat_1(E_250,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_250,k1_zfmisc_1(k2_zfmisc_1(A_245,B_246)))
      | ~ v1_funct_1(E_250) ) ),
    inference(resolution,[status(thm)],[c_90,c_2044])).

tff(c_2113,plain,(
    ! [A_252,B_253,E_254] :
      ( k1_partfun1(A_252,B_253,'#skF_2','#skF_1',E_254,'#skF_4') = k5_relat_1(E_254,'#skF_4')
      | ~ m1_subset_1(E_254,k1_zfmisc_1(k2_zfmisc_1(A_252,B_253)))
      | ~ v1_funct_1(E_254) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_2050])).

tff(c_2125,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_2113])).

tff(c_2133,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_2125])).

tff(c_1370,plain,(
    ! [D_200,C_201,A_202,B_203] :
      ( D_200 = C_201
      | ~ r2_relset_1(A_202,B_203,C_201,D_200)
      | ~ m1_subset_1(D_200,k1_zfmisc_1(k2_zfmisc_1(A_202,B_203)))
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(A_202,B_203))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1378,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_86,c_1370])).

tff(c_1393,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_1378])).

tff(c_1433,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1393])).

tff(c_2140,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2133,c_1433])).

tff(c_2151,plain,(
    ! [E_256,F_258,A_255,D_259,C_257,B_260] :
      ( m1_subset_1(k1_partfun1(A_255,B_260,C_257,D_259,E_256,F_258),k1_zfmisc_1(k2_zfmisc_1(A_255,D_259)))
      | ~ m1_subset_1(F_258,k1_zfmisc_1(k2_zfmisc_1(C_257,D_259)))
      | ~ v1_funct_1(F_258)
      | ~ m1_subset_1(E_256,k1_zfmisc_1(k2_zfmisc_1(A_255,B_260)))
      | ~ v1_funct_1(E_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_2205,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2133,c_2151])).

tff(c_2227,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_96,c_94,c_90,c_2205])).

tff(c_2230,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2140,c_2227])).

tff(c_2231,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1393])).

tff(c_3566,plain,(
    ! [F_348,B_345,A_344,C_346,D_347,E_349] :
      ( k1_partfun1(A_344,B_345,C_346,D_347,E_349,F_348) = k5_relat_1(E_349,F_348)
      | ~ m1_subset_1(F_348,k1_zfmisc_1(k2_zfmisc_1(C_346,D_347)))
      | ~ v1_funct_1(F_348)
      | ~ m1_subset_1(E_349,k1_zfmisc_1(k2_zfmisc_1(A_344,B_345)))
      | ~ v1_funct_1(E_349) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_3572,plain,(
    ! [A_344,B_345,E_349] :
      ( k1_partfun1(A_344,B_345,'#skF_2','#skF_1',E_349,'#skF_4') = k5_relat_1(E_349,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_349,k1_zfmisc_1(k2_zfmisc_1(A_344,B_345)))
      | ~ v1_funct_1(E_349) ) ),
    inference(resolution,[status(thm)],[c_90,c_3566])).

tff(c_3605,plain,(
    ! [A_351,B_352,E_353] :
      ( k1_partfun1(A_351,B_352,'#skF_2','#skF_1',E_353,'#skF_4') = k5_relat_1(E_353,'#skF_4')
      | ~ m1_subset_1(E_353,k1_zfmisc_1(k2_zfmisc_1(A_351,B_352)))
      | ~ v1_funct_1(E_353) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_3572])).

tff(c_3617,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_3605])).

tff(c_3625,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_2231,c_3617])).

tff(c_3632,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3625,c_24])).

tff(c_3638,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_94,c_156,c_100,c_2247,c_285,c_460,c_3632])).

tff(c_3640,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_615,c_3638])).

tff(c_3642,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_563])).

tff(c_283,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_90,c_271])).

tff(c_4601,plain,(
    ! [C_446,A_447,B_448] :
      ( v1_funct_1(k2_funct_1(C_446))
      | k2_relset_1(A_447,B_448,C_446) != B_448
      | ~ v2_funct_1(C_446)
      | ~ m1_subset_1(C_446,k1_zfmisc_1(k2_zfmisc_1(A_447,B_448)))
      | ~ v1_funct_2(C_446,A_447,B_448)
      | ~ v1_funct_1(C_446) ) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_4607,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_90,c_4601])).

tff(c_4616,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_3642,c_283,c_4607])).

tff(c_4620,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4616])).

tff(c_166,plain,(
    ! [A_69,B_70,D_71] :
      ( r2_relset_1(A_69,B_70,D_71,D_71)
      | ~ m1_subset_1(D_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_173,plain,(
    ! [A_29] : r2_relset_1(A_29,A_29,k6_partfun1(A_29),k6_partfun1(A_29)) ),
    inference(resolution,[status(thm)],[c_101,c_166])).

tff(c_4953,plain,(
    ! [F_481,E_482,C_479,B_478,D_480,A_477] :
      ( k1_partfun1(A_477,B_478,C_479,D_480,E_482,F_481) = k5_relat_1(E_482,F_481)
      | ~ m1_subset_1(F_481,k1_zfmisc_1(k2_zfmisc_1(C_479,D_480)))
      | ~ v1_funct_1(F_481)
      | ~ m1_subset_1(E_482,k1_zfmisc_1(k2_zfmisc_1(A_477,B_478)))
      | ~ v1_funct_1(E_482) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_4957,plain,(
    ! [A_477,B_478,E_482] :
      ( k1_partfun1(A_477,B_478,'#skF_2','#skF_1',E_482,'#skF_4') = k5_relat_1(E_482,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_482,k1_zfmisc_1(k2_zfmisc_1(A_477,B_478)))
      | ~ v1_funct_1(E_482) ) ),
    inference(resolution,[status(thm)],[c_90,c_4953])).

tff(c_4992,plain,(
    ! [A_485,B_486,E_487] :
      ( k1_partfun1(A_485,B_486,'#skF_2','#skF_1',E_487,'#skF_4') = k5_relat_1(E_487,'#skF_4')
      | ~ m1_subset_1(E_487,k1_zfmisc_1(k2_zfmisc_1(A_485,B_486)))
      | ~ v1_funct_1(E_487) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_4957])).

tff(c_5001,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_4992])).

tff(c_5008,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_5001])).

tff(c_3681,plain,(
    ! [D_354,C_355,A_356,B_357] :
      ( D_354 = C_355
      | ~ r2_relset_1(A_356,B_357,C_355,D_354)
      | ~ m1_subset_1(D_354,k1_zfmisc_1(k2_zfmisc_1(A_356,B_357)))
      | ~ m1_subset_1(C_355,k1_zfmisc_1(k2_zfmisc_1(A_356,B_357))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_3689,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_86,c_3681])).

tff(c_3704,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_3689])).

tff(c_4760,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_3704])).

tff(c_5015,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5008,c_4760])).

tff(c_5140,plain,(
    ! [B_500,C_497,E_496,D_499,A_495,F_498] :
      ( m1_subset_1(k1_partfun1(A_495,B_500,C_497,D_499,E_496,F_498),k1_zfmisc_1(k2_zfmisc_1(A_495,D_499)))
      | ~ m1_subset_1(F_498,k1_zfmisc_1(k2_zfmisc_1(C_497,D_499)))
      | ~ v1_funct_1(F_498)
      | ~ m1_subset_1(E_496,k1_zfmisc_1(k2_zfmisc_1(A_495,B_500)))
      | ~ v1_funct_1(E_496) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_5203,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5008,c_5140])).

tff(c_5231,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_96,c_94,c_90,c_5203])).

tff(c_5233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5015,c_5231])).

tff(c_5234,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_3704])).

tff(c_6263,plain,(
    ! [A_556,B_557,C_558,D_559] :
      ( k2_relset_1(A_556,B_557,C_558) = B_557
      | ~ r2_relset_1(B_557,B_557,k1_partfun1(B_557,A_556,A_556,B_557,D_559,C_558),k6_partfun1(B_557))
      | ~ m1_subset_1(D_559,k1_zfmisc_1(k2_zfmisc_1(B_557,A_556)))
      | ~ v1_funct_2(D_559,B_557,A_556)
      | ~ v1_funct_1(D_559)
      | ~ m1_subset_1(C_558,k1_zfmisc_1(k2_zfmisc_1(A_556,B_557)))
      | ~ v1_funct_2(C_558,A_556,B_557)
      | ~ v1_funct_1(C_558) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_6269,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5234,c_6263])).

tff(c_6273,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_90,c_100,c_98,c_96,c_173,c_283,c_6269])).

tff(c_6275,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4620,c_6273])).

tff(c_6277,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4616])).

tff(c_36,plain,(
    ! [A_13,B_15] :
      ( k2_funct_1(A_13) = B_15
      | k6_relat_1(k2_relat_1(A_13)) != k5_relat_1(B_15,A_13)
      | k2_relat_1(B_15) != k1_relat_1(A_13)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_6423,plain,(
    ! [A_562,B_563] :
      ( k2_funct_1(A_562) = B_563
      | k6_partfun1(k2_relat_1(A_562)) != k5_relat_1(B_563,A_562)
      | k2_relat_1(B_563) != k1_relat_1(A_562)
      | ~ v2_funct_1(A_562)
      | ~ v1_funct_1(B_563)
      | ~ v1_relat_1(B_563)
      | ~ v1_funct_1(A_562)
      | ~ v1_relat_1(A_562) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_36])).

tff(c_6441,plain,(
    ! [B_563] :
      ( k2_funct_1('#skF_3') = B_563
      | k5_relat_1(B_563,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_563) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_563)
      | ~ v1_relat_1(B_563)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_6423])).

tff(c_7053,plain,(
    ! [B_617] :
      ( k2_funct_1('#skF_3') = B_617
      | k5_relat_1(B_617,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_617) != '#skF_1'
      | ~ v1_funct_1(B_617)
      | ~ v1_relat_1(B_617) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_100,c_84,c_464,c_6441])).

tff(c_7068,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_155,c_7053])).

tff(c_7086,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_6277,c_7068])).

tff(c_7087,plain,(
    k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_7086])).

tff(c_6427,plain,(
    ! [B_563] :
      ( k2_funct_1('#skF_4') = B_563
      | k5_relat_1(B_563,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_563) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_563)
      | ~ v1_relat_1(B_563)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6277,c_6423])).

tff(c_7210,plain,(
    ! [B_634] :
      ( k2_funct_1('#skF_4') = B_634
      | k5_relat_1(B_634,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_634) != '#skF_2'
      | ~ v1_funct_1(B_634)
      | ~ v1_relat_1(B_634) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_94,c_3642,c_460,c_6427])).

tff(c_7222,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_156,c_7210])).

tff(c_7240,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_285,c_7222])).

tff(c_7245,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_7240])).

tff(c_6794,plain,(
    ! [F_597,C_595,B_594,D_596,E_598,A_593] :
      ( k1_partfun1(A_593,B_594,C_595,D_596,E_598,F_597) = k5_relat_1(E_598,F_597)
      | ~ m1_subset_1(F_597,k1_zfmisc_1(k2_zfmisc_1(C_595,D_596)))
      | ~ v1_funct_1(F_597)
      | ~ m1_subset_1(E_598,k1_zfmisc_1(k2_zfmisc_1(A_593,B_594)))
      | ~ v1_funct_1(E_598) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_6800,plain,(
    ! [A_593,B_594,E_598] :
      ( k1_partfun1(A_593,B_594,'#skF_2','#skF_1',E_598,'#skF_4') = k5_relat_1(E_598,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_598,k1_zfmisc_1(k2_zfmisc_1(A_593,B_594)))
      | ~ v1_funct_1(E_598) ) ),
    inference(resolution,[status(thm)],[c_90,c_6794])).

tff(c_6847,plain,(
    ! [A_602,B_603,E_604] :
      ( k1_partfun1(A_602,B_603,'#skF_2','#skF_1',E_604,'#skF_4') = k5_relat_1(E_604,'#skF_4')
      | ~ m1_subset_1(E_604,k1_zfmisc_1(k2_zfmisc_1(A_602,B_603)))
      | ~ v1_funct_1(E_604) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_6800])).

tff(c_6859,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_6847])).

tff(c_6867,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_6859])).

tff(c_6494,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_3704])).

tff(c_6874,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6867,c_6494])).

tff(c_6886,plain,(
    ! [A_605,E_606,B_610,C_607,F_608,D_609] :
      ( m1_subset_1(k1_partfun1(A_605,B_610,C_607,D_609,E_606,F_608),k1_zfmisc_1(k2_zfmisc_1(A_605,D_609)))
      | ~ m1_subset_1(F_608,k1_zfmisc_1(k2_zfmisc_1(C_607,D_609)))
      | ~ v1_funct_1(F_608)
      | ~ m1_subset_1(E_606,k1_zfmisc_1(k2_zfmisc_1(A_605,B_610)))
      | ~ v1_funct_1(E_606) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_6937,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6867,c_6886])).

tff(c_6958,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_96,c_94,c_90,c_6937])).

tff(c_6961,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6874,c_6958])).

tff(c_6962,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_3704])).

tff(c_7280,plain,(
    ! [B_642,D_644,F_645,A_641,E_646,C_643] :
      ( k1_partfun1(A_641,B_642,C_643,D_644,E_646,F_645) = k5_relat_1(E_646,F_645)
      | ~ m1_subset_1(F_645,k1_zfmisc_1(k2_zfmisc_1(C_643,D_644)))
      | ~ v1_funct_1(F_645)
      | ~ m1_subset_1(E_646,k1_zfmisc_1(k2_zfmisc_1(A_641,B_642)))
      | ~ v1_funct_1(E_646) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_7286,plain,(
    ! [A_641,B_642,E_646] :
      ( k1_partfun1(A_641,B_642,'#skF_2','#skF_1',E_646,'#skF_4') = k5_relat_1(E_646,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_646,k1_zfmisc_1(k2_zfmisc_1(A_641,B_642)))
      | ~ v1_funct_1(E_646) ) ),
    inference(resolution,[status(thm)],[c_90,c_7280])).

tff(c_7321,plain,(
    ! [A_648,B_649,E_650] :
      ( k1_partfun1(A_648,B_649,'#skF_2','#skF_1',E_650,'#skF_4') = k5_relat_1(E_650,'#skF_4')
      | ~ m1_subset_1(E_650,k1_zfmisc_1(k2_zfmisc_1(A_648,B_649)))
      | ~ v1_funct_1(E_650) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_7286])).

tff(c_7333,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_7321])).

tff(c_7341,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_6962,c_7333])).

tff(c_7343,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7245,c_7341])).

tff(c_7344,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_7240])).

tff(c_34,plain,(
    ! [A_12] :
      ( k5_relat_1(A_12,k2_funct_1(A_12)) = k6_relat_1(k1_relat_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_103,plain,(
    ! [A_12] :
      ( k5_relat_1(A_12,k2_funct_1(A_12)) = k6_partfun1(k1_relat_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_34])).

tff(c_7366,plain,
    ( k6_partfun1(k1_relat_1('#skF_4')) = k5_relat_1('#skF_4','#skF_3')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7344,c_103])).

tff(c_7392,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_94,c_3642,c_460,c_7366])).

tff(c_7394,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7087,c_7392])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:39:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.88/4.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.88/4.24  
% 11.88/4.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.88/4.24  %$ r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.88/4.24  
% 11.88/4.24  %Foreground sorts:
% 11.88/4.24  
% 11.88/4.24  
% 11.88/4.24  %Background operators:
% 11.88/4.24  
% 11.88/4.24  
% 11.88/4.24  %Foreground operators:
% 11.88/4.24  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.88/4.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.88/4.24  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 11.88/4.24  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 11.88/4.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.88/4.24  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 11.88/4.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.88/4.24  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 11.88/4.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.88/4.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.88/4.24  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.88/4.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.88/4.24  tff('#skF_2', type, '#skF_2': $i).
% 11.88/4.24  tff('#skF_3', type, '#skF_3': $i).
% 11.88/4.24  tff('#skF_1', type, '#skF_1': $i).
% 11.88/4.24  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.88/4.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.88/4.24  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 11.88/4.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.88/4.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.88/4.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.88/4.24  tff('#skF_4', type, '#skF_4': $i).
% 11.88/4.24  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 11.88/4.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.88/4.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.88/4.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.88/4.24  
% 12.18/4.28  tff(f_238, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 12.18/4.28  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 12.18/4.28  tff(f_123, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 12.18/4.28  tff(f_155, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 12.18/4.28  tff(f_88, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 12.18/4.28  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.18/4.28  tff(f_179, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 12.18/4.28  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 12.18/4.28  tff(f_61, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 12.18/4.28  tff(f_49, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 12.18/4.28  tff(f_137, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 12.18/4.28  tff(f_35, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 12.18/4.28  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 12.18/4.28  tff(f_177, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 12.18/4.28  tff(f_135, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 12.18/4.28  tff(f_167, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 12.18/4.28  tff(f_127, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 12.18/4.28  tff(f_212, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 12.18/4.28  tff(f_196, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 12.18/4.28  tff(f_115, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 12.18/4.28  tff(f_98, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 12.18/4.28  tff(c_78, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_238])).
% 12.18/4.28  tff(c_94, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_238])).
% 12.18/4.28  tff(c_92, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_238])).
% 12.18/4.28  tff(c_90, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_238])).
% 12.18/4.28  tff(c_144, plain, (![C_62, A_63, B_64]: (v1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 12.18/4.28  tff(c_155, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_90, c_144])).
% 12.18/4.28  tff(c_82, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_238])).
% 12.18/4.28  tff(c_352, plain, (![A_86, B_87, C_88]: (k1_relset_1(A_86, B_87, C_88)=k1_relat_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 12.18/4.28  tff(c_364, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_90, c_352])).
% 12.18/4.28  tff(c_445, plain, (![B_103, A_104, C_105]: (k1_xboole_0=B_103 | k1_relset_1(A_104, B_103, C_105)=A_104 | ~v1_funct_2(C_105, A_104, B_103) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_104, B_103))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 12.18/4.28  tff(c_451, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_90, c_445])).
% 12.18/4.28  tff(c_459, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_364, c_451])).
% 12.18/4.28  tff(c_460, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_82, c_459])).
% 12.18/4.28  tff(c_28, plain, (![A_11]: (k2_relat_1(k2_funct_1(A_11))=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_88])).
% 12.18/4.28  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.18/4.28  tff(c_68, plain, (![A_45]: (k6_relat_1(A_45)=k6_partfun1(A_45))), inference(cnfTransformation, [status(thm)], [f_179])).
% 12.18/4.28  tff(c_12, plain, (![B_5, A_4]: (k5_relat_1(B_5, k6_relat_1(A_4))=B_5 | ~r1_tarski(k2_relat_1(B_5), A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.18/4.28  tff(c_195, plain, (![B_75, A_76]: (k5_relat_1(B_75, k6_partfun1(A_76))=B_75 | ~r1_tarski(k2_relat_1(B_75), A_76) | ~v1_relat_1(B_75))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_12])).
% 12.18/4.28  tff(c_209, plain, (![B_77]: (k5_relat_1(B_77, k6_partfun1(k2_relat_1(B_77)))=B_77 | ~v1_relat_1(B_77))), inference(resolution, [status(thm)], [c_6, c_195])).
% 12.18/4.28  tff(c_534, plain, (![A_110]: (k5_relat_1(k2_funct_1(A_110), k6_partfun1(k1_relat_1(A_110)))=k2_funct_1(A_110) | ~v1_relat_1(k2_funct_1(A_110)) | ~v2_funct_1(A_110) | ~v1_funct_1(A_110) | ~v1_relat_1(A_110))), inference(superposition, [status(thm), theory('equality')], [c_28, c_209])).
% 12.18/4.28  tff(c_549, plain, (k5_relat_1(k2_funct_1('#skF_4'), k6_partfun1('#skF_2'))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_460, c_534])).
% 12.18/4.28  tff(c_563, plain, (k5_relat_1(k2_funct_1('#skF_4'), k6_partfun1('#skF_2'))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_94, c_549])).
% 12.18/4.28  tff(c_615, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_563])).
% 12.18/4.28  tff(c_96, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_238])).
% 12.18/4.28  tff(c_156, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_144])).
% 12.18/4.28  tff(c_100, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_238])).
% 12.18/4.28  tff(c_84, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_238])).
% 12.18/4.28  tff(c_18, plain, (![A_7]: (v2_funct_1(k2_funct_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_61])).
% 12.18/4.28  tff(c_14, plain, (![A_6]: (v1_funct_1(k2_funct_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.18/4.28  tff(c_80, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_238])).
% 12.18/4.28  tff(c_98, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_238])).
% 12.18/4.28  tff(c_365, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_352])).
% 12.18/4.28  tff(c_454, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_96, c_445])).
% 12.18/4.28  tff(c_463, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_365, c_454])).
% 12.18/4.28  tff(c_464, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_80, c_463])).
% 12.18/4.28  tff(c_48, plain, (![A_29]: (m1_subset_1(k6_relat_1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 12.18/4.28  tff(c_101, plain, (![A_29]: (m1_subset_1(k6_partfun1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_48])).
% 12.18/4.28  tff(c_154, plain, (![A_29]: (v1_relat_1(k6_partfun1(A_29)))), inference(resolution, [status(thm)], [c_101, c_144])).
% 12.18/4.28  tff(c_16, plain, (![A_6]: (v1_relat_1(k2_funct_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.18/4.28  tff(c_546, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_464, c_534])).
% 12.18/4.28  tff(c_561, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_100, c_84, c_546])).
% 12.18/4.28  tff(c_605, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_561])).
% 12.18/4.28  tff(c_608, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_605])).
% 12.18/4.28  tff(c_612, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_156, c_100, c_608])).
% 12.18/4.29  tff(c_614, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_561])).
% 12.18/4.29  tff(c_8, plain, (![A_3]: (k1_relat_1(k6_relat_1(A_3))=A_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.18/4.29  tff(c_107, plain, (![A_3]: (k1_relat_1(k6_partfun1(A_3))=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_68, c_8])).
% 12.18/4.29  tff(c_613, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_561])).
% 12.18/4.29  tff(c_24, plain, (![A_8, B_10]: (v2_funct_1(A_8) | k2_relat_1(B_10)!=k1_relat_1(A_8) | ~v2_funct_1(k5_relat_1(B_10, A_8)) | ~v1_funct_1(B_10) | ~v1_relat_1(B_10) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_78])).
% 12.18/4.29  tff(c_622, plain, (v2_funct_1(k6_partfun1('#skF_1')) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1(k6_partfun1('#skF_1')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k6_partfun1('#skF_1')) | ~v1_relat_1(k6_partfun1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_613, c_24])).
% 12.18/4.29  tff(c_628, plain, (v2_funct_1(k6_partfun1('#skF_1')) | k2_relat_1(k2_funct_1('#skF_3'))!='#skF_1' | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_614, c_107, c_622])).
% 12.18/4.29  tff(c_630, plain, (~v1_funct_1(k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_628])).
% 12.18/4.29  tff(c_1174, plain, (![C_176, A_174, D_177, F_178, B_175, E_179]: (k1_partfun1(A_174, B_175, C_176, D_177, E_179, F_178)=k5_relat_1(E_179, F_178) | ~m1_subset_1(F_178, k1_zfmisc_1(k2_zfmisc_1(C_176, D_177))) | ~v1_funct_1(F_178) | ~m1_subset_1(E_179, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))) | ~v1_funct_1(E_179))), inference(cnfTransformation, [status(thm)], [f_177])).
% 12.18/4.29  tff(c_1180, plain, (![A_174, B_175, E_179]: (k1_partfun1(A_174, B_175, '#skF_2', '#skF_1', E_179, '#skF_4')=k5_relat_1(E_179, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_179, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))) | ~v1_funct_1(E_179))), inference(resolution, [status(thm)], [c_90, c_1174])).
% 12.18/4.29  tff(c_1191, plain, (![A_180, B_181, E_182]: (k1_partfun1(A_180, B_181, '#skF_2', '#skF_1', E_182, '#skF_4')=k5_relat_1(E_182, '#skF_4') | ~m1_subset_1(E_182, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))) | ~v1_funct_1(E_182))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_1180])).
% 12.18/4.29  tff(c_1203, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_1191])).
% 12.18/4.29  tff(c_1211, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_1203])).
% 12.18/4.29  tff(c_86, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_238])).
% 12.18/4.29  tff(c_631, plain, (![D_113, C_114, A_115, B_116]: (D_113=C_114 | ~r2_relset_1(A_115, B_116, C_114, D_113) | ~m1_subset_1(D_113, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 12.18/4.29  tff(c_639, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_86, c_631])).
% 12.18/4.29  tff(c_654, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_639])).
% 12.18/4.29  tff(c_682, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_654])).
% 12.18/4.29  tff(c_1218, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1211, c_682])).
% 12.18/4.29  tff(c_1230, plain, (![D_188, B_189, E_185, F_187, C_186, A_184]: (m1_subset_1(k1_partfun1(A_184, B_189, C_186, D_188, E_185, F_187), k1_zfmisc_1(k2_zfmisc_1(A_184, D_188))) | ~m1_subset_1(F_187, k1_zfmisc_1(k2_zfmisc_1(C_186, D_188))) | ~v1_funct_1(F_187) | ~m1_subset_1(E_185, k1_zfmisc_1(k2_zfmisc_1(A_184, B_189))) | ~v1_funct_1(E_185))), inference(cnfTransformation, [status(thm)], [f_167])).
% 12.18/4.29  tff(c_1289, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1211, c_1230])).
% 12.18/4.29  tff(c_1313, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_96, c_94, c_90, c_1289])).
% 12.18/4.29  tff(c_1315, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1218, c_1313])).
% 12.18/4.29  tff(c_1316, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_654])).
% 12.18/4.29  tff(c_1325, plain, (![E_191, A_190, D_194, F_193, B_195, C_192]: (v1_funct_1(k1_partfun1(A_190, B_195, C_192, D_194, E_191, F_193)) | ~m1_subset_1(F_193, k1_zfmisc_1(k2_zfmisc_1(C_192, D_194))) | ~v1_funct_1(F_193) | ~m1_subset_1(E_191, k1_zfmisc_1(k2_zfmisc_1(A_190, B_195))) | ~v1_funct_1(E_191))), inference(cnfTransformation, [status(thm)], [f_167])).
% 12.18/4.29  tff(c_1329, plain, (![A_190, B_195, E_191]: (v1_funct_1(k1_partfun1(A_190, B_195, '#skF_2', '#skF_1', E_191, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_191, k1_zfmisc_1(k2_zfmisc_1(A_190, B_195))) | ~v1_funct_1(E_191))), inference(resolution, [status(thm)], [c_90, c_1325])).
% 12.18/4.29  tff(c_1340, plain, (![A_197, B_198, E_199]: (v1_funct_1(k1_partfun1(A_197, B_198, '#skF_2', '#skF_1', E_199, '#skF_4')) | ~m1_subset_1(E_199, k1_zfmisc_1(k2_zfmisc_1(A_197, B_198))) | ~v1_funct_1(E_199))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_1329])).
% 12.18/4.29  tff(c_1349, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_1340])).
% 12.18/4.29  tff(c_1356, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_1316, c_1349])).
% 12.18/4.29  tff(c_1358, plain, $false, inference(negUnitSimplification, [status(thm)], [c_630, c_1356])).
% 12.18/4.29  tff(c_1359, plain, (~v1_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relat_1(k2_funct_1('#skF_3'))!='#skF_1' | v2_funct_1(k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_628])).
% 12.18/4.29  tff(c_1361, plain, (k2_relat_1(k2_funct_1('#skF_3'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_1359])).
% 12.18/4.29  tff(c_1364, plain, (k1_relat_1('#skF_3')!='#skF_1' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_1361])).
% 12.18/4.29  tff(c_1367, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_156, c_100, c_84, c_464, c_1364])).
% 12.18/4.29  tff(c_1368, plain, (~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | v2_funct_1(k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_1359])).
% 12.18/4.29  tff(c_1423, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1368])).
% 12.18/4.29  tff(c_1426, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_1423])).
% 12.18/4.29  tff(c_1430, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_156, c_100, c_1426])).
% 12.18/4.29  tff(c_1431, plain, (~v2_funct_1(k2_funct_1('#skF_3')) | v2_funct_1(k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_1368])).
% 12.18/4.29  tff(c_2239, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1431])).
% 12.18/4.29  tff(c_2242, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_2239])).
% 12.18/4.29  tff(c_2246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_156, c_100, c_84, c_2242])).
% 12.18/4.29  tff(c_2247, plain, (v2_funct_1(k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_1431])).
% 12.18/4.29  tff(c_88, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_238])).
% 12.18/4.29  tff(c_271, plain, (![A_81, B_82, C_83]: (k2_relset_1(A_81, B_82, C_83)=k2_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 12.18/4.29  tff(c_280, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_271])).
% 12.18/4.29  tff(c_285, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_280])).
% 12.18/4.29  tff(c_2044, plain, (![A_245, D_248, F_249, C_247, E_250, B_246]: (k1_partfun1(A_245, B_246, C_247, D_248, E_250, F_249)=k5_relat_1(E_250, F_249) | ~m1_subset_1(F_249, k1_zfmisc_1(k2_zfmisc_1(C_247, D_248))) | ~v1_funct_1(F_249) | ~m1_subset_1(E_250, k1_zfmisc_1(k2_zfmisc_1(A_245, B_246))) | ~v1_funct_1(E_250))), inference(cnfTransformation, [status(thm)], [f_177])).
% 12.18/4.29  tff(c_2050, plain, (![A_245, B_246, E_250]: (k1_partfun1(A_245, B_246, '#skF_2', '#skF_1', E_250, '#skF_4')=k5_relat_1(E_250, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_250, k1_zfmisc_1(k2_zfmisc_1(A_245, B_246))) | ~v1_funct_1(E_250))), inference(resolution, [status(thm)], [c_90, c_2044])).
% 12.18/4.29  tff(c_2113, plain, (![A_252, B_253, E_254]: (k1_partfun1(A_252, B_253, '#skF_2', '#skF_1', E_254, '#skF_4')=k5_relat_1(E_254, '#skF_4') | ~m1_subset_1(E_254, k1_zfmisc_1(k2_zfmisc_1(A_252, B_253))) | ~v1_funct_1(E_254))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_2050])).
% 12.18/4.29  tff(c_2125, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_2113])).
% 12.18/4.29  tff(c_2133, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_2125])).
% 12.18/4.29  tff(c_1370, plain, (![D_200, C_201, A_202, B_203]: (D_200=C_201 | ~r2_relset_1(A_202, B_203, C_201, D_200) | ~m1_subset_1(D_200, k1_zfmisc_1(k2_zfmisc_1(A_202, B_203))) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(A_202, B_203))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 12.18/4.29  tff(c_1378, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_86, c_1370])).
% 12.18/4.29  tff(c_1393, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_1378])).
% 12.18/4.29  tff(c_1433, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1393])).
% 12.18/4.29  tff(c_2140, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2133, c_1433])).
% 12.18/4.29  tff(c_2151, plain, (![E_256, F_258, A_255, D_259, C_257, B_260]: (m1_subset_1(k1_partfun1(A_255, B_260, C_257, D_259, E_256, F_258), k1_zfmisc_1(k2_zfmisc_1(A_255, D_259))) | ~m1_subset_1(F_258, k1_zfmisc_1(k2_zfmisc_1(C_257, D_259))) | ~v1_funct_1(F_258) | ~m1_subset_1(E_256, k1_zfmisc_1(k2_zfmisc_1(A_255, B_260))) | ~v1_funct_1(E_256))), inference(cnfTransformation, [status(thm)], [f_167])).
% 12.18/4.29  tff(c_2205, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2133, c_2151])).
% 12.18/4.29  tff(c_2227, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_96, c_94, c_90, c_2205])).
% 12.18/4.29  tff(c_2230, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2140, c_2227])).
% 12.18/4.29  tff(c_2231, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1393])).
% 12.18/4.29  tff(c_3566, plain, (![F_348, B_345, A_344, C_346, D_347, E_349]: (k1_partfun1(A_344, B_345, C_346, D_347, E_349, F_348)=k5_relat_1(E_349, F_348) | ~m1_subset_1(F_348, k1_zfmisc_1(k2_zfmisc_1(C_346, D_347))) | ~v1_funct_1(F_348) | ~m1_subset_1(E_349, k1_zfmisc_1(k2_zfmisc_1(A_344, B_345))) | ~v1_funct_1(E_349))), inference(cnfTransformation, [status(thm)], [f_177])).
% 12.18/4.29  tff(c_3572, plain, (![A_344, B_345, E_349]: (k1_partfun1(A_344, B_345, '#skF_2', '#skF_1', E_349, '#skF_4')=k5_relat_1(E_349, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_349, k1_zfmisc_1(k2_zfmisc_1(A_344, B_345))) | ~v1_funct_1(E_349))), inference(resolution, [status(thm)], [c_90, c_3566])).
% 12.18/4.29  tff(c_3605, plain, (![A_351, B_352, E_353]: (k1_partfun1(A_351, B_352, '#skF_2', '#skF_1', E_353, '#skF_4')=k5_relat_1(E_353, '#skF_4') | ~m1_subset_1(E_353, k1_zfmisc_1(k2_zfmisc_1(A_351, B_352))) | ~v1_funct_1(E_353))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_3572])).
% 12.18/4.29  tff(c_3617, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_3605])).
% 12.18/4.29  tff(c_3625, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_2231, c_3617])).
% 12.18/4.29  tff(c_3632, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3625, c_24])).
% 12.18/4.29  tff(c_3638, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_94, c_156, c_100, c_2247, c_285, c_460, c_3632])).
% 12.18/4.29  tff(c_3640, plain, $false, inference(negUnitSimplification, [status(thm)], [c_615, c_3638])).
% 12.18/4.29  tff(c_3642, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_563])).
% 12.18/4.29  tff(c_283, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_90, c_271])).
% 12.18/4.29  tff(c_4601, plain, (![C_446, A_447, B_448]: (v1_funct_1(k2_funct_1(C_446)) | k2_relset_1(A_447, B_448, C_446)!=B_448 | ~v2_funct_1(C_446) | ~m1_subset_1(C_446, k1_zfmisc_1(k2_zfmisc_1(A_447, B_448))) | ~v1_funct_2(C_446, A_447, B_448) | ~v1_funct_1(C_446))), inference(cnfTransformation, [status(thm)], [f_212])).
% 12.18/4.29  tff(c_4607, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_90, c_4601])).
% 12.18/4.29  tff(c_4616, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_3642, c_283, c_4607])).
% 12.18/4.29  tff(c_4620, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_4616])).
% 12.18/4.29  tff(c_166, plain, (![A_69, B_70, D_71]: (r2_relset_1(A_69, B_70, D_71, D_71) | ~m1_subset_1(D_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 12.18/4.29  tff(c_173, plain, (![A_29]: (r2_relset_1(A_29, A_29, k6_partfun1(A_29), k6_partfun1(A_29)))), inference(resolution, [status(thm)], [c_101, c_166])).
% 12.18/4.29  tff(c_4953, plain, (![F_481, E_482, C_479, B_478, D_480, A_477]: (k1_partfun1(A_477, B_478, C_479, D_480, E_482, F_481)=k5_relat_1(E_482, F_481) | ~m1_subset_1(F_481, k1_zfmisc_1(k2_zfmisc_1(C_479, D_480))) | ~v1_funct_1(F_481) | ~m1_subset_1(E_482, k1_zfmisc_1(k2_zfmisc_1(A_477, B_478))) | ~v1_funct_1(E_482))), inference(cnfTransformation, [status(thm)], [f_177])).
% 12.18/4.29  tff(c_4957, plain, (![A_477, B_478, E_482]: (k1_partfun1(A_477, B_478, '#skF_2', '#skF_1', E_482, '#skF_4')=k5_relat_1(E_482, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_482, k1_zfmisc_1(k2_zfmisc_1(A_477, B_478))) | ~v1_funct_1(E_482))), inference(resolution, [status(thm)], [c_90, c_4953])).
% 12.18/4.29  tff(c_4992, plain, (![A_485, B_486, E_487]: (k1_partfun1(A_485, B_486, '#skF_2', '#skF_1', E_487, '#skF_4')=k5_relat_1(E_487, '#skF_4') | ~m1_subset_1(E_487, k1_zfmisc_1(k2_zfmisc_1(A_485, B_486))) | ~v1_funct_1(E_487))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_4957])).
% 12.18/4.29  tff(c_5001, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_4992])).
% 12.18/4.29  tff(c_5008, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_5001])).
% 12.18/4.29  tff(c_3681, plain, (![D_354, C_355, A_356, B_357]: (D_354=C_355 | ~r2_relset_1(A_356, B_357, C_355, D_354) | ~m1_subset_1(D_354, k1_zfmisc_1(k2_zfmisc_1(A_356, B_357))) | ~m1_subset_1(C_355, k1_zfmisc_1(k2_zfmisc_1(A_356, B_357))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 12.18/4.29  tff(c_3689, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_86, c_3681])).
% 12.18/4.29  tff(c_3704, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_3689])).
% 12.18/4.29  tff(c_4760, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_3704])).
% 12.18/4.29  tff(c_5015, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_5008, c_4760])).
% 12.18/4.29  tff(c_5140, plain, (![B_500, C_497, E_496, D_499, A_495, F_498]: (m1_subset_1(k1_partfun1(A_495, B_500, C_497, D_499, E_496, F_498), k1_zfmisc_1(k2_zfmisc_1(A_495, D_499))) | ~m1_subset_1(F_498, k1_zfmisc_1(k2_zfmisc_1(C_497, D_499))) | ~v1_funct_1(F_498) | ~m1_subset_1(E_496, k1_zfmisc_1(k2_zfmisc_1(A_495, B_500))) | ~v1_funct_1(E_496))), inference(cnfTransformation, [status(thm)], [f_167])).
% 12.18/4.29  tff(c_5203, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5008, c_5140])).
% 12.18/4.29  tff(c_5231, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_96, c_94, c_90, c_5203])).
% 12.18/4.29  tff(c_5233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5015, c_5231])).
% 12.18/4.29  tff(c_5234, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_3704])).
% 12.18/4.29  tff(c_6263, plain, (![A_556, B_557, C_558, D_559]: (k2_relset_1(A_556, B_557, C_558)=B_557 | ~r2_relset_1(B_557, B_557, k1_partfun1(B_557, A_556, A_556, B_557, D_559, C_558), k6_partfun1(B_557)) | ~m1_subset_1(D_559, k1_zfmisc_1(k2_zfmisc_1(B_557, A_556))) | ~v1_funct_2(D_559, B_557, A_556) | ~v1_funct_1(D_559) | ~m1_subset_1(C_558, k1_zfmisc_1(k2_zfmisc_1(A_556, B_557))) | ~v1_funct_2(C_558, A_556, B_557) | ~v1_funct_1(C_558))), inference(cnfTransformation, [status(thm)], [f_196])).
% 12.18/4.29  tff(c_6269, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5234, c_6263])).
% 12.18/4.29  tff(c_6273, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_90, c_100, c_98, c_96, c_173, c_283, c_6269])).
% 12.18/4.29  tff(c_6275, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4620, c_6273])).
% 12.18/4.29  tff(c_6277, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_4616])).
% 12.18/4.29  tff(c_36, plain, (![A_13, B_15]: (k2_funct_1(A_13)=B_15 | k6_relat_1(k2_relat_1(A_13))!=k5_relat_1(B_15, A_13) | k2_relat_1(B_15)!=k1_relat_1(A_13) | ~v2_funct_1(A_13) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_115])).
% 12.18/4.29  tff(c_6423, plain, (![A_562, B_563]: (k2_funct_1(A_562)=B_563 | k6_partfun1(k2_relat_1(A_562))!=k5_relat_1(B_563, A_562) | k2_relat_1(B_563)!=k1_relat_1(A_562) | ~v2_funct_1(A_562) | ~v1_funct_1(B_563) | ~v1_relat_1(B_563) | ~v1_funct_1(A_562) | ~v1_relat_1(A_562))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_36])).
% 12.18/4.29  tff(c_6441, plain, (![B_563]: (k2_funct_1('#skF_3')=B_563 | k5_relat_1(B_563, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_563)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_563) | ~v1_relat_1(B_563) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_285, c_6423])).
% 12.18/4.29  tff(c_7053, plain, (![B_617]: (k2_funct_1('#skF_3')=B_617 | k5_relat_1(B_617, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_617)!='#skF_1' | ~v1_funct_1(B_617) | ~v1_relat_1(B_617))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_100, c_84, c_464, c_6441])).
% 12.18/4.29  tff(c_7068, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_155, c_7053])).
% 12.18/4.29  tff(c_7086, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_6277, c_7068])).
% 12.18/4.29  tff(c_7087, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_78, c_7086])).
% 12.18/4.29  tff(c_6427, plain, (![B_563]: (k2_funct_1('#skF_4')=B_563 | k5_relat_1(B_563, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_563)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_563) | ~v1_relat_1(B_563) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6277, c_6423])).
% 12.18/4.29  tff(c_7210, plain, (![B_634]: (k2_funct_1('#skF_4')=B_634 | k5_relat_1(B_634, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_634)!='#skF_2' | ~v1_funct_1(B_634) | ~v1_relat_1(B_634))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_94, c_3642, c_460, c_6427])).
% 12.18/4.29  tff(c_7222, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_156, c_7210])).
% 12.18/4.29  tff(c_7240, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_285, c_7222])).
% 12.18/4.29  tff(c_7245, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_7240])).
% 12.18/4.29  tff(c_6794, plain, (![F_597, C_595, B_594, D_596, E_598, A_593]: (k1_partfun1(A_593, B_594, C_595, D_596, E_598, F_597)=k5_relat_1(E_598, F_597) | ~m1_subset_1(F_597, k1_zfmisc_1(k2_zfmisc_1(C_595, D_596))) | ~v1_funct_1(F_597) | ~m1_subset_1(E_598, k1_zfmisc_1(k2_zfmisc_1(A_593, B_594))) | ~v1_funct_1(E_598))), inference(cnfTransformation, [status(thm)], [f_177])).
% 12.18/4.29  tff(c_6800, plain, (![A_593, B_594, E_598]: (k1_partfun1(A_593, B_594, '#skF_2', '#skF_1', E_598, '#skF_4')=k5_relat_1(E_598, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_598, k1_zfmisc_1(k2_zfmisc_1(A_593, B_594))) | ~v1_funct_1(E_598))), inference(resolution, [status(thm)], [c_90, c_6794])).
% 12.18/4.29  tff(c_6847, plain, (![A_602, B_603, E_604]: (k1_partfun1(A_602, B_603, '#skF_2', '#skF_1', E_604, '#skF_4')=k5_relat_1(E_604, '#skF_4') | ~m1_subset_1(E_604, k1_zfmisc_1(k2_zfmisc_1(A_602, B_603))) | ~v1_funct_1(E_604))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_6800])).
% 12.18/4.29  tff(c_6859, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_6847])).
% 12.18/4.29  tff(c_6867, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_6859])).
% 12.18/4.29  tff(c_6494, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_3704])).
% 12.18/4.29  tff(c_6874, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_6867, c_6494])).
% 12.18/4.29  tff(c_6886, plain, (![A_605, E_606, B_610, C_607, F_608, D_609]: (m1_subset_1(k1_partfun1(A_605, B_610, C_607, D_609, E_606, F_608), k1_zfmisc_1(k2_zfmisc_1(A_605, D_609))) | ~m1_subset_1(F_608, k1_zfmisc_1(k2_zfmisc_1(C_607, D_609))) | ~v1_funct_1(F_608) | ~m1_subset_1(E_606, k1_zfmisc_1(k2_zfmisc_1(A_605, B_610))) | ~v1_funct_1(E_606))), inference(cnfTransformation, [status(thm)], [f_167])).
% 12.18/4.29  tff(c_6937, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6867, c_6886])).
% 12.18/4.29  tff(c_6958, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_96, c_94, c_90, c_6937])).
% 12.18/4.29  tff(c_6961, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6874, c_6958])).
% 12.18/4.29  tff(c_6962, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_3704])).
% 12.18/4.29  tff(c_7280, plain, (![B_642, D_644, F_645, A_641, E_646, C_643]: (k1_partfun1(A_641, B_642, C_643, D_644, E_646, F_645)=k5_relat_1(E_646, F_645) | ~m1_subset_1(F_645, k1_zfmisc_1(k2_zfmisc_1(C_643, D_644))) | ~v1_funct_1(F_645) | ~m1_subset_1(E_646, k1_zfmisc_1(k2_zfmisc_1(A_641, B_642))) | ~v1_funct_1(E_646))), inference(cnfTransformation, [status(thm)], [f_177])).
% 12.18/4.29  tff(c_7286, plain, (![A_641, B_642, E_646]: (k1_partfun1(A_641, B_642, '#skF_2', '#skF_1', E_646, '#skF_4')=k5_relat_1(E_646, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_646, k1_zfmisc_1(k2_zfmisc_1(A_641, B_642))) | ~v1_funct_1(E_646))), inference(resolution, [status(thm)], [c_90, c_7280])).
% 12.18/4.29  tff(c_7321, plain, (![A_648, B_649, E_650]: (k1_partfun1(A_648, B_649, '#skF_2', '#skF_1', E_650, '#skF_4')=k5_relat_1(E_650, '#skF_4') | ~m1_subset_1(E_650, k1_zfmisc_1(k2_zfmisc_1(A_648, B_649))) | ~v1_funct_1(E_650))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_7286])).
% 12.18/4.29  tff(c_7333, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_7321])).
% 12.18/4.29  tff(c_7341, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_6962, c_7333])).
% 12.18/4.29  tff(c_7343, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7245, c_7341])).
% 12.18/4.29  tff(c_7344, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_7240])).
% 12.18/4.29  tff(c_34, plain, (![A_12]: (k5_relat_1(A_12, k2_funct_1(A_12))=k6_relat_1(k1_relat_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_98])).
% 12.18/4.29  tff(c_103, plain, (![A_12]: (k5_relat_1(A_12, k2_funct_1(A_12))=k6_partfun1(k1_relat_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_34])).
% 12.18/4.29  tff(c_7366, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k5_relat_1('#skF_4', '#skF_3') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7344, c_103])).
% 12.18/4.29  tff(c_7392, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_94, c_3642, c_460, c_7366])).
% 12.18/4.29  tff(c_7394, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7087, c_7392])).
% 12.18/4.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.18/4.29  
% 12.18/4.29  Inference rules
% 12.18/4.29  ----------------------
% 12.18/4.29  #Ref     : 0
% 12.18/4.29  #Sup     : 1489
% 12.18/4.29  #Fact    : 0
% 12.18/4.29  #Define  : 0
% 12.18/4.29  #Split   : 65
% 12.18/4.29  #Chain   : 0
% 12.18/4.29  #Close   : 0
% 12.18/4.29  
% 12.18/4.29  Ordering : KBO
% 12.18/4.29  
% 12.18/4.29  Simplification rules
% 12.18/4.29  ----------------------
% 12.18/4.29  #Subsume      : 143
% 12.18/4.29  #Demod        : 2562
% 12.18/4.29  #Tautology    : 540
% 12.18/4.29  #SimpNegUnit  : 51
% 12.18/4.29  #BackRed      : 48
% 12.18/4.29  
% 12.18/4.29  #Partial instantiations: 0
% 12.18/4.29  #Strategies tried      : 1
% 12.18/4.29  
% 12.18/4.29  Timing (in seconds)
% 12.18/4.29  ----------------------
% 12.32/4.29  Preprocessing        : 0.66
% 12.32/4.29  Parsing              : 0.34
% 12.32/4.29  CNF conversion       : 0.06
% 12.32/4.29  Main loop            : 2.75
% 12.32/4.29  Inferencing          : 0.95
% 12.32/4.29  Reduction            : 0.99
% 12.32/4.29  Demodulation         : 0.73
% 12.32/4.29  BG Simplification    : 0.11
% 12.32/4.29  Subsumption          : 0.49
% 12.32/4.29  Abstraction          : 0.12
% 12.32/4.29  MUC search           : 0.00
% 12.32/4.29  Cooper               : 0.00
% 12.32/4.29  Total                : 3.52
% 12.32/4.29  Index Insertion      : 0.00
% 12.32/4.30  Index Deletion       : 0.00
% 12.32/4.30  Index Matching       : 0.00
% 12.32/4.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
