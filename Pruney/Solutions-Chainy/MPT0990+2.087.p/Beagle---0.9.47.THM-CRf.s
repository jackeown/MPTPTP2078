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
% DateTime   : Thu Dec  3 10:13:08 EST 2020

% Result     : Theorem 13.52s
% Output     : CNFRefutation 13.52s
% Verified   : 
% Statistics : Number of formulae       :  194 (1390 expanded)
%              Number of leaves         :   47 ( 558 expanded)
%              Depth                    :   13
%              Number of atoms          :  626 (7704 expanded)
%              Number of equality atoms :  170 (2247 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_270,negated_conjecture,(
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

tff(f_133,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_137,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_228,axiom,(
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

tff(f_112,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_244,axiom,(
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

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B)
        & v2_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v2_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_funct_1)).

tff(f_167,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_145,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_157,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_212,axiom,(
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

tff(f_169,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_104,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_94,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
          & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_186,axiom,(
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

tff(f_84,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_129,axiom,(
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

tff(c_68,plain,(
    k2_funct_1('#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_84,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_80,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_109,plain,(
    ! [C_63,A_64,B_65] :
      ( v1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_116,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_109])).

tff(c_82,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_126,plain,(
    ! [A_70,B_71,C_72] :
      ( k2_relset_1(A_70,B_71,C_72) = k2_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_133,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_126])).

tff(c_15537,plain,(
    ! [C_585,A_586,B_587] :
      ( v1_funct_1(k2_funct_1(C_585))
      | k2_relset_1(A_586,B_587,C_585) != B_587
      | ~ v2_funct_1(C_585)
      | ~ m1_subset_1(C_585,k1_zfmisc_1(k2_zfmisc_1(A_586,B_587)))
      | ~ v1_funct_2(C_585,A_586,B_587)
      | ~ v1_funct_1(C_585) ) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_15543,plain,
    ( v1_funct_1(k2_funct_1('#skF_6'))
    | k2_relset_1('#skF_4','#skF_3','#skF_6') != '#skF_3'
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_15537])).

tff(c_15551,plain,
    ( v1_funct_1(k2_funct_1('#skF_6'))
    | k2_relat_1('#skF_6') != '#skF_3'
    | ~ v2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_133,c_15543])).

tff(c_15567,plain,(
    ~ v2_funct_1('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_15551])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_90,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_88,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_86,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_117,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_109])).

tff(c_74,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_28,plain,(
    ! [A_15] :
      ( v2_funct_1(k2_funct_1(A_15))
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_relat_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_78,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_15546,plain,
    ( v1_funct_1(k2_funct_1('#skF_5'))
    | k2_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_15537])).

tff(c_15554,plain,(
    v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_74,c_78,c_15546])).

tff(c_70,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_16857,plain,(
    ! [A_724,C_725,B_726] :
      ( k6_partfun1(A_724) = k5_relat_1(C_725,k2_funct_1(C_725))
      | k1_xboole_0 = B_726
      | ~ v2_funct_1(C_725)
      | k2_relset_1(A_724,B_726,C_725) != B_726
      | ~ m1_subset_1(C_725,k1_zfmisc_1(k2_zfmisc_1(A_724,B_726)))
      | ~ v1_funct_2(C_725,A_724,B_726)
      | ~ v1_funct_1(C_725) ) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_16865,plain,
    ( k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3')
    | k1_xboole_0 = '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_4'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_16857])).

tff(c_16877,plain,
    ( k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_78,c_74,c_16865])).

tff(c_16878,plain,(
    k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_16877])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( v2_funct_1(k5_relat_1(A_2,B_3))
      | ~ v2_funct_1(B_3)
      | ~ v1_funct_1(B_3)
      | ~ v1_relat_1(B_3)
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16884,plain,
    ( v2_funct_1(k6_partfun1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_16878,c_6])).

tff(c_16906,plain,
    ( v2_funct_1(k6_partfun1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_90,c_74,c_15554,c_16884])).

tff(c_17036,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_16906])).

tff(c_17039,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_17036])).

tff(c_17043,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_90,c_17039])).

tff(c_17044,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_5'))
    | v2_funct_1(k6_partfun1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_16906])).

tff(c_17051,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_17044])).

tff(c_17054,plain,
    ( ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_17051])).

tff(c_17058,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_90,c_74,c_17054])).

tff(c_17059,plain,(
    v2_funct_1(k6_partfun1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_17044])).

tff(c_539,plain,(
    ! [C_121,A_119,F_120,E_122,D_123,B_124] :
      ( k1_partfun1(A_119,B_124,C_121,D_123,E_122,F_120) = k5_relat_1(E_122,F_120)
      | ~ m1_subset_1(F_120,k1_zfmisc_1(k2_zfmisc_1(C_121,D_123)))
      | ~ v1_funct_1(F_120)
      | ~ m1_subset_1(E_122,k1_zfmisc_1(k2_zfmisc_1(A_119,B_124)))
      | ~ v1_funct_1(E_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_541,plain,(
    ! [A_119,B_124,E_122] :
      ( k1_partfun1(A_119,B_124,'#skF_4','#skF_3',E_122,'#skF_6') = k5_relat_1(E_122,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_122,k1_zfmisc_1(k2_zfmisc_1(A_119,B_124)))
      | ~ v1_funct_1(E_122) ) ),
    inference(resolution,[status(thm)],[c_80,c_539])).

tff(c_560,plain,(
    ! [A_125,B_126,E_127] :
      ( k1_partfun1(A_125,B_126,'#skF_4','#skF_3',E_127,'#skF_6') = k5_relat_1(E_127,'#skF_6')
      | ~ m1_subset_1(E_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126)))
      | ~ v1_funct_1(E_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_541])).

tff(c_566,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_560])).

tff(c_572,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_566])).

tff(c_76,plain,(
    r2_relset_1('#skF_3','#skF_3',k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k6_partfun1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_248,plain,(
    ! [D_88,C_89,A_90,B_91] :
      ( D_88 = C_89
      | ~ r2_relset_1(A_90,B_91,C_89,D_88)
      | ~ m1_subset_1(D_88,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91)))
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_263,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k6_partfun1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_76,c_248])).

tff(c_313,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_263])).

tff(c_579,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_572,c_313])).

tff(c_924,plain,(
    ! [E_155,F_154,B_152,D_151,C_156,A_153] :
      ( m1_subset_1(k1_partfun1(A_153,B_152,C_156,D_151,E_155,F_154),k1_zfmisc_1(k2_zfmisc_1(A_153,D_151)))
      | ~ m1_subset_1(F_154,k1_zfmisc_1(k2_zfmisc_1(C_156,D_151)))
      | ~ v1_funct_1(F_154)
      | ~ m1_subset_1(E_155,k1_zfmisc_1(k2_zfmisc_1(A_153,B_152)))
      | ~ v1_funct_1(E_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_973,plain,
    ( m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_572,c_924])).

tff(c_997,plain,(
    m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_84,c_80,c_973])).

tff(c_999,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_579,c_997])).

tff(c_1000,plain,
    ( ~ m1_subset_1(k6_partfun1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_263])).

tff(c_1013,plain,(
    ~ m1_subset_1(k6_partfun1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1000])).

tff(c_1105,plain,(
    ! [C_159,A_160,B_161] :
      ( v1_funct_1(k2_funct_1(C_159))
      | k2_relset_1(A_160,B_161,C_159) != B_161
      | ~ v2_funct_1(C_159)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161)))
      | ~ v1_funct_2(C_159,A_160,B_161)
      | ~ v1_funct_1(C_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_1114,plain,
    ( v1_funct_1(k2_funct_1('#skF_5'))
    | k2_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_1105])).

tff(c_1122,plain,(
    v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_74,c_78,c_1114])).

tff(c_58,plain,(
    ! [C_55,B_54,A_53] :
      ( m1_subset_1(k2_funct_1(C_55),k1_zfmisc_1(k2_zfmisc_1(B_54,A_53)))
      | k2_relset_1(A_53,B_54,C_55) != B_54
      | ~ v2_funct_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54)))
      | ~ v1_funct_2(C_55,A_53,B_54)
      | ~ v1_funct_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_1455,plain,(
    ! [C_211,A_209,F_210,E_212,B_214,D_213] :
      ( k1_partfun1(A_209,B_214,C_211,D_213,E_212,F_210) = k5_relat_1(E_212,F_210)
      | ~ m1_subset_1(F_210,k1_zfmisc_1(k2_zfmisc_1(C_211,D_213)))
      | ~ v1_funct_1(F_210)
      | ~ m1_subset_1(E_212,k1_zfmisc_1(k2_zfmisc_1(A_209,B_214)))
      | ~ v1_funct_1(E_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_9271,plain,(
    ! [E_460,B_462,A_459,C_458,A_461,B_463] :
      ( k1_partfun1(A_461,B_462,B_463,A_459,E_460,k2_funct_1(C_458)) = k5_relat_1(E_460,k2_funct_1(C_458))
      | ~ v1_funct_1(k2_funct_1(C_458))
      | ~ m1_subset_1(E_460,k1_zfmisc_1(k2_zfmisc_1(A_461,B_462)))
      | ~ v1_funct_1(E_460)
      | k2_relset_1(A_459,B_463,C_458) != B_463
      | ~ v2_funct_1(C_458)
      | ~ m1_subset_1(C_458,k1_zfmisc_1(k2_zfmisc_1(A_459,B_463)))
      | ~ v1_funct_2(C_458,A_459,B_463)
      | ~ v1_funct_1(C_458) ) ),
    inference(resolution,[status(thm)],[c_58,c_1455])).

tff(c_9301,plain,(
    ! [B_463,A_459,C_458] :
      ( k1_partfun1('#skF_4','#skF_3',B_463,A_459,'#skF_6',k2_funct_1(C_458)) = k5_relat_1('#skF_6',k2_funct_1(C_458))
      | ~ v1_funct_1(k2_funct_1(C_458))
      | ~ v1_funct_1('#skF_6')
      | k2_relset_1(A_459,B_463,C_458) != B_463
      | ~ v2_funct_1(C_458)
      | ~ m1_subset_1(C_458,k1_zfmisc_1(k2_zfmisc_1(A_459,B_463)))
      | ~ v1_funct_2(C_458,A_459,B_463)
      | ~ v1_funct_1(C_458) ) ),
    inference(resolution,[status(thm)],[c_80,c_9271])).

tff(c_11593,plain,(
    ! [B_550,A_551,C_552] :
      ( k1_partfun1('#skF_4','#skF_3',B_550,A_551,'#skF_6',k2_funct_1(C_552)) = k5_relat_1('#skF_6',k2_funct_1(C_552))
      | ~ v1_funct_1(k2_funct_1(C_552))
      | k2_relset_1(A_551,B_550,C_552) != B_550
      | ~ v2_funct_1(C_552)
      | ~ m1_subset_1(C_552,k1_zfmisc_1(k2_zfmisc_1(A_551,B_550)))
      | ~ v1_funct_2(C_552,A_551,B_550)
      | ~ v1_funct_1(C_552) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_9301])).

tff(c_11641,plain,
    ( k1_partfun1('#skF_4','#skF_3','#skF_4','#skF_3','#skF_6',k2_funct_1('#skF_5')) = k5_relat_1('#skF_6',k2_funct_1('#skF_5'))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | k2_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_11593])).

tff(c_11685,plain,(
    k1_partfun1('#skF_4','#skF_3','#skF_4','#skF_3','#skF_6',k2_funct_1('#skF_5')) = k5_relat_1('#skF_6',k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_74,c_78,c_1122,c_11641])).

tff(c_1337,plain,(
    ! [C_198,B_199,A_200] :
      ( m1_subset_1(k2_funct_1(C_198),k1_zfmisc_1(k2_zfmisc_1(B_199,A_200)))
      | k2_relset_1(A_200,B_199,C_198) != B_199
      | ~ v2_funct_1(C_198)
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(A_200,B_199)))
      | ~ v1_funct_2(C_198,A_200,B_199)
      | ~ v1_funct_1(C_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_42,plain,(
    ! [E_33,A_29,F_34,D_32,C_31,B_30] :
      ( v1_funct_1(k1_partfun1(A_29,B_30,C_31,D_32,E_33,F_34))
      | ~ m1_subset_1(F_34,k1_zfmisc_1(k2_zfmisc_1(C_31,D_32)))
      | ~ v1_funct_1(F_34)
      | ~ m1_subset_1(E_33,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30)))
      | ~ v1_funct_1(E_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_8965,plain,(
    ! [B_449,B_446,C_448,A_447,A_451,E_450] :
      ( v1_funct_1(k1_partfun1(A_447,B_446,B_449,A_451,E_450,k2_funct_1(C_448)))
      | ~ v1_funct_1(k2_funct_1(C_448))
      | ~ m1_subset_1(E_450,k1_zfmisc_1(k2_zfmisc_1(A_447,B_446)))
      | ~ v1_funct_1(E_450)
      | k2_relset_1(A_451,B_449,C_448) != B_449
      | ~ v2_funct_1(C_448)
      | ~ m1_subset_1(C_448,k1_zfmisc_1(k2_zfmisc_1(A_451,B_449)))
      | ~ v1_funct_2(C_448,A_451,B_449)
      | ~ v1_funct_1(C_448) ) ),
    inference(resolution,[status(thm)],[c_1337,c_42])).

tff(c_8995,plain,(
    ! [B_449,A_451,C_448] :
      ( v1_funct_1(k1_partfun1('#skF_4','#skF_3',B_449,A_451,'#skF_6',k2_funct_1(C_448)))
      | ~ v1_funct_1(k2_funct_1(C_448))
      | ~ v1_funct_1('#skF_6')
      | k2_relset_1(A_451,B_449,C_448) != B_449
      | ~ v2_funct_1(C_448)
      | ~ m1_subset_1(C_448,k1_zfmisc_1(k2_zfmisc_1(A_451,B_449)))
      | ~ v1_funct_2(C_448,A_451,B_449)
      | ~ v1_funct_1(C_448) ) ),
    inference(resolution,[status(thm)],[c_80,c_8965])).

tff(c_10874,plain,(
    ! [B_529,A_530,C_531] :
      ( v1_funct_1(k1_partfun1('#skF_4','#skF_3',B_529,A_530,'#skF_6',k2_funct_1(C_531)))
      | ~ v1_funct_1(k2_funct_1(C_531))
      | k2_relset_1(A_530,B_529,C_531) != B_529
      | ~ v2_funct_1(C_531)
      | ~ m1_subset_1(C_531,k1_zfmisc_1(k2_zfmisc_1(A_530,B_529)))
      | ~ v1_funct_2(C_531,A_530,B_529)
      | ~ v1_funct_1(C_531) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_8995])).

tff(c_10922,plain,
    ( v1_funct_1(k1_partfun1('#skF_4','#skF_3','#skF_4','#skF_3','#skF_6',k2_funct_1('#skF_5')))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | k2_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_10874])).

tff(c_10966,plain,(
    v1_funct_1(k1_partfun1('#skF_4','#skF_3','#skF_4','#skF_3','#skF_6',k2_funct_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_74,c_78,c_1122,c_10922])).

tff(c_11686,plain,(
    v1_funct_1(k5_relat_1('#skF_6',k2_funct_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11685,c_10966])).

tff(c_1789,plain,(
    ! [E_228,B_225,F_227,C_229,D_224,A_226] :
      ( m1_subset_1(k1_partfun1(A_226,B_225,C_229,D_224,E_228,F_227),k1_zfmisc_1(k2_zfmisc_1(A_226,D_224)))
      | ~ m1_subset_1(F_227,k1_zfmisc_1(k2_zfmisc_1(C_229,D_224)))
      | ~ v1_funct_1(F_227)
      | ~ m1_subset_1(E_228,k1_zfmisc_1(k2_zfmisc_1(A_226,B_225)))
      | ~ v1_funct_1(E_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_66,plain,(
    ! [A_56,C_58,B_57] :
      ( k6_partfun1(A_56) = k5_relat_1(C_58,k2_funct_1(C_58))
      | k1_xboole_0 = B_57
      | ~ v2_funct_1(C_58)
      | k2_relset_1(A_56,B_57,C_58) != B_57
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57)))
      | ~ v1_funct_2(C_58,A_56,B_57)
      | ~ v1_funct_1(C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_1834,plain,(
    ! [E_228,B_225,F_227,C_229,D_224,A_226] :
      ( k5_relat_1(k1_partfun1(A_226,B_225,C_229,D_224,E_228,F_227),k2_funct_1(k1_partfun1(A_226,B_225,C_229,D_224,E_228,F_227))) = k6_partfun1(A_226)
      | k1_xboole_0 = D_224
      | ~ v2_funct_1(k1_partfun1(A_226,B_225,C_229,D_224,E_228,F_227))
      | k2_relset_1(A_226,D_224,k1_partfun1(A_226,B_225,C_229,D_224,E_228,F_227)) != D_224
      | ~ v1_funct_2(k1_partfun1(A_226,B_225,C_229,D_224,E_228,F_227),A_226,D_224)
      | ~ v1_funct_1(k1_partfun1(A_226,B_225,C_229,D_224,E_228,F_227))
      | ~ m1_subset_1(F_227,k1_zfmisc_1(k2_zfmisc_1(C_229,D_224)))
      | ~ v1_funct_1(F_227)
      | ~ m1_subset_1(E_228,k1_zfmisc_1(k2_zfmisc_1(A_226,B_225)))
      | ~ v1_funct_1(E_228) ) ),
    inference(resolution,[status(thm)],[c_1789,c_66])).

tff(c_11690,plain,
    ( k5_relat_1(k5_relat_1('#skF_6',k2_funct_1('#skF_5')),k2_funct_1(k1_partfun1('#skF_4','#skF_3','#skF_4','#skF_3','#skF_6',k2_funct_1('#skF_5')))) = k6_partfun1('#skF_4')
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1(k1_partfun1('#skF_4','#skF_3','#skF_4','#skF_3','#skF_6',k2_funct_1('#skF_5')))
    | k2_relset_1('#skF_4','#skF_3',k1_partfun1('#skF_4','#skF_3','#skF_4','#skF_3','#skF_6',k2_funct_1('#skF_5'))) != '#skF_3'
    | ~ v1_funct_2(k1_partfun1('#skF_4','#skF_3','#skF_4','#skF_3','#skF_6',k2_funct_1('#skF_5')),'#skF_4','#skF_3')
    | ~ v1_funct_1(k1_partfun1('#skF_4','#skF_3','#skF_4','#skF_3','#skF_6',k2_funct_1('#skF_5')))
    | ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_11685,c_1834])).

tff(c_11719,plain,
    ( k5_relat_1(k5_relat_1('#skF_6',k2_funct_1('#skF_5')),k2_funct_1(k5_relat_1('#skF_6',k2_funct_1('#skF_5')))) = k6_partfun1('#skF_4')
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1(k5_relat_1('#skF_6',k2_funct_1('#skF_5')))
    | k2_relset_1('#skF_4','#skF_3',k5_relat_1('#skF_6',k2_funct_1('#skF_5'))) != '#skF_3'
    | ~ v1_funct_2(k5_relat_1('#skF_6',k2_funct_1('#skF_5')),'#skF_4','#skF_3')
    | ~ v1_funct_1(k5_relat_1('#skF_6',k2_funct_1('#skF_5')))
    | ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_1122,c_11685,c_11685,c_11685,c_11685,c_11685,c_11690])).

tff(c_11720,plain,
    ( k5_relat_1(k5_relat_1('#skF_6',k2_funct_1('#skF_5')),k2_funct_1(k5_relat_1('#skF_6',k2_funct_1('#skF_5')))) = k6_partfun1('#skF_4')
    | ~ v2_funct_1(k5_relat_1('#skF_6',k2_funct_1('#skF_5')))
    | k2_relset_1('#skF_4','#skF_3',k5_relat_1('#skF_6',k2_funct_1('#skF_5'))) != '#skF_3'
    | ~ v1_funct_2(k5_relat_1('#skF_6',k2_funct_1('#skF_5')),'#skF_4','#skF_3')
    | ~ v1_funct_1(k5_relat_1('#skF_6',k2_funct_1('#skF_5')))
    | ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_11719])).

tff(c_13556,plain,
    ( k5_relat_1(k5_relat_1('#skF_6',k2_funct_1('#skF_5')),k2_funct_1(k5_relat_1('#skF_6',k2_funct_1('#skF_5')))) = k6_partfun1('#skF_4')
    | ~ v2_funct_1(k5_relat_1('#skF_6',k2_funct_1('#skF_5')))
    | k2_relset_1('#skF_4','#skF_3',k5_relat_1('#skF_6',k2_funct_1('#skF_5'))) != '#skF_3'
    | ~ v1_funct_2(k5_relat_1('#skF_6',k2_funct_1('#skF_5')),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11686,c_11720])).

tff(c_13557,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_13556])).

tff(c_13560,plain,
    ( k2_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_13557])).

tff(c_13564,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_74,c_78,c_13560])).

tff(c_13566,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_13556])).

tff(c_1529,plain,(
    ! [A_218,C_219,B_220] :
      ( k6_partfun1(A_218) = k5_relat_1(C_219,k2_funct_1(C_219))
      | k1_xboole_0 = B_220
      | ~ v2_funct_1(C_219)
      | k2_relset_1(A_218,B_220,C_219) != B_220
      | ~ m1_subset_1(C_219,k1_zfmisc_1(k2_zfmisc_1(A_218,B_220)))
      | ~ v1_funct_2(C_219,A_218,B_220)
      | ~ v1_funct_1(C_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_1535,plain,
    ( k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3')
    | k1_xboole_0 = '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_4'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_1529])).

tff(c_1543,plain,
    ( k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_78,c_74,c_1535])).

tff(c_1544,plain,(
    k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1543])).

tff(c_9303,plain,(
    ! [B_463,A_459,C_458] :
      ( k1_partfun1('#skF_3','#skF_4',B_463,A_459,'#skF_5',k2_funct_1(C_458)) = k5_relat_1('#skF_5',k2_funct_1(C_458))
      | ~ v1_funct_1(k2_funct_1(C_458))
      | ~ v1_funct_1('#skF_5')
      | k2_relset_1(A_459,B_463,C_458) != B_463
      | ~ v2_funct_1(C_458)
      | ~ m1_subset_1(C_458,k1_zfmisc_1(k2_zfmisc_1(A_459,B_463)))
      | ~ v1_funct_2(C_458,A_459,B_463)
      | ~ v1_funct_1(C_458) ) ),
    inference(resolution,[status(thm)],[c_86,c_9271])).

tff(c_15276,plain,(
    ! [B_581,A_582,C_583] :
      ( k1_partfun1('#skF_3','#skF_4',B_581,A_582,'#skF_5',k2_funct_1(C_583)) = k5_relat_1('#skF_5',k2_funct_1(C_583))
      | ~ v1_funct_1(k2_funct_1(C_583))
      | k2_relset_1(A_582,B_581,C_583) != B_581
      | ~ v2_funct_1(C_583)
      | ~ m1_subset_1(C_583,k1_zfmisc_1(k2_zfmisc_1(A_582,B_581)))
      | ~ v1_funct_2(C_583,A_582,B_581)
      | ~ v1_funct_1(C_583) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_9303])).

tff(c_15336,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5',k2_funct_1('#skF_5')) = k5_relat_1('#skF_5',k2_funct_1('#skF_5'))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | k2_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_15276])).

tff(c_15392,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_74,c_78,c_1122,c_1544,c_15336])).

tff(c_40,plain,(
    ! [E_33,A_29,F_34,D_32,C_31,B_30] :
      ( m1_subset_1(k1_partfun1(A_29,B_30,C_31,D_32,E_33,F_34),k1_zfmisc_1(k2_zfmisc_1(A_29,D_32)))
      | ~ m1_subset_1(F_34,k1_zfmisc_1(k2_zfmisc_1(C_31,D_32)))
      | ~ v1_funct_1(F_34)
      | ~ m1_subset_1(E_33,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30)))
      | ~ v1_funct_1(E_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_15430,plain,
    ( m1_subset_1(k6_partfun1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_15392,c_40])).

tff(c_15465,plain,(
    m1_subset_1(k6_partfun1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_1122,c_13566,c_15430])).

tff(c_15467,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1013,c_15465])).

tff(c_15468,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1000])).

tff(c_17836,plain,(
    ! [E_755,C_757,B_756,A_753,D_754] :
      ( k1_xboole_0 = C_757
      | v2_funct_1(E_755)
      | k2_relset_1(A_753,B_756,D_754) != B_756
      | ~ v2_funct_1(k1_partfun1(A_753,B_756,B_756,C_757,D_754,E_755))
      | ~ m1_subset_1(E_755,k1_zfmisc_1(k2_zfmisc_1(B_756,C_757)))
      | ~ v1_funct_2(E_755,B_756,C_757)
      | ~ v1_funct_1(E_755)
      | ~ m1_subset_1(D_754,k1_zfmisc_1(k2_zfmisc_1(A_753,B_756)))
      | ~ v1_funct_2(D_754,A_753,B_756)
      | ~ v1_funct_1(D_754) ) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_17844,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_funct_1('#skF_6')
    | k2_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_4'
    | ~ v2_funct_1(k6_partfun1('#skF_3'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_15468,c_17836])).

tff(c_17855,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_84,c_82,c_80,c_17059,c_78,c_17844])).

tff(c_17857,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15567,c_72,c_17855])).

tff(c_17859,plain,(
    v2_funct_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_15551])).

tff(c_132,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_126])).

tff(c_135,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_132])).

tff(c_46,plain,(
    ! [A_41] : k6_relat_1(A_41) = k6_partfun1(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_24,plain,(
    ! [A_14] :
      ( k5_relat_1(k2_funct_1(A_14),A_14) = k6_relat_1(k2_relat_1(A_14))
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_93,plain,(
    ! [A_14] :
      ( k5_relat_1(k2_funct_1(A_14),A_14) = k6_partfun1(k2_relat_1(A_14))
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_24])).

tff(c_153,plain,(
    ! [A_74] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(A_74),A_74)) = k2_relat_1(A_74)
      | ~ v2_funct_1(A_74)
      | ~ v1_funct_1(A_74)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_264,plain,(
    ! [A_92] :
      ( k1_relat_1(k6_partfun1(k2_relat_1(A_92))) = k2_relat_1(A_92)
      | ~ v2_funct_1(A_92)
      | ~ v1_funct_1(A_92)
      | ~ v1_relat_1(A_92)
      | ~ v2_funct_1(A_92)
      | ~ v1_funct_1(A_92)
      | ~ v1_relat_1(A_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_153])).

tff(c_279,plain,
    ( k1_relat_1(k6_partfun1('#skF_4')) = k2_relat_1('#skF_5')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_264])).

tff(c_283,plain,(
    k1_relat_1(k6_partfun1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_90,c_74,c_117,c_90,c_74,c_135,c_279])).

tff(c_17858,plain,
    ( k2_relat_1('#skF_6') != '#skF_3'
    | v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_15551])).

tff(c_17860,plain,(
    k2_relat_1('#skF_6') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_17858])).

tff(c_15483,plain,(
    r2_relset_1('#skF_3','#skF_3',k6_partfun1('#skF_3'),k6_partfun1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15468,c_76])).

tff(c_18962,plain,(
    ! [A_835,B_836,C_837,D_838] :
      ( k2_relset_1(A_835,B_836,C_837) = B_836
      | ~ r2_relset_1(B_836,B_836,k1_partfun1(B_836,A_835,A_835,B_836,D_838,C_837),k6_partfun1(B_836))
      | ~ m1_subset_1(D_838,k1_zfmisc_1(k2_zfmisc_1(B_836,A_835)))
      | ~ v1_funct_2(D_838,B_836,A_835)
      | ~ v1_funct_1(D_838)
      | ~ m1_subset_1(C_837,k1_zfmisc_1(k2_zfmisc_1(A_835,B_836)))
      | ~ v1_funct_2(C_837,A_835,B_836)
      | ~ v1_funct_1(C_837) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_18971,plain,
    ( k2_relset_1('#skF_4','#skF_3','#skF_6') = '#skF_3'
    | ~ r2_relset_1('#skF_3','#skF_3',k6_partfun1('#skF_3'),k6_partfun1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_15468,c_18962])).

tff(c_18975,plain,(
    k2_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_90,c_88,c_86,c_15483,c_133,c_18971])).

tff(c_18977,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17860,c_18975])).

tff(c_18979,plain,(
    k2_relat_1('#skF_6') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_17858])).

tff(c_18980,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18979,c_133])).

tff(c_19708,plain,(
    ! [A_924,C_925,B_926] :
      ( k6_partfun1(A_924) = k5_relat_1(C_925,k2_funct_1(C_925))
      | k1_xboole_0 = B_926
      | ~ v2_funct_1(C_925)
      | k2_relset_1(A_924,B_926,C_925) != B_926
      | ~ m1_subset_1(C_925,k1_zfmisc_1(k2_zfmisc_1(A_924,B_926)))
      | ~ v1_funct_2(C_925,A_924,B_926)
      | ~ v1_funct_1(C_925) ) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_19714,plain,
    ( k5_relat_1('#skF_6',k2_funct_1('#skF_6')) = k6_partfun1('#skF_4')
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_6')
    | k2_relset_1('#skF_4','#skF_3','#skF_6') != '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_19708])).

tff(c_19724,plain,
    ( k5_relat_1('#skF_6',k2_funct_1('#skF_6')) = k6_partfun1('#skF_4')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_18980,c_17859,c_19714])).

tff(c_19725,plain,(
    k5_relat_1('#skF_6',k2_funct_1('#skF_6')) = k6_partfun1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_19724])).

tff(c_18,plain,(
    ! [A_12] :
      ( k1_relat_1(k5_relat_1(A_12,k2_funct_1(A_12))) = k1_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_19741,plain,
    ( k1_relat_1(k6_partfun1('#skF_4')) = k1_relat_1('#skF_6')
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_19725,c_18])).

tff(c_19761,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_84,c_17859,c_283,c_19741])).

tff(c_19559,plain,(
    ! [E_912,B_914,A_909,D_913,F_910,C_911] :
      ( k1_partfun1(A_909,B_914,C_911,D_913,E_912,F_910) = k5_relat_1(E_912,F_910)
      | ~ m1_subset_1(F_910,k1_zfmisc_1(k2_zfmisc_1(C_911,D_913)))
      | ~ v1_funct_1(F_910)
      | ~ m1_subset_1(E_912,k1_zfmisc_1(k2_zfmisc_1(A_909,B_914)))
      | ~ v1_funct_1(E_912) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_19563,plain,(
    ! [A_909,B_914,E_912] :
      ( k1_partfun1(A_909,B_914,'#skF_4','#skF_3',E_912,'#skF_6') = k5_relat_1(E_912,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_912,k1_zfmisc_1(k2_zfmisc_1(A_909,B_914)))
      | ~ v1_funct_1(E_912) ) ),
    inference(resolution,[status(thm)],[c_80,c_19559])).

tff(c_19585,plain,(
    ! [A_915,B_916,E_917] :
      ( k1_partfun1(A_915,B_916,'#skF_4','#skF_3',E_917,'#skF_6') = k5_relat_1(E_917,'#skF_6')
      | ~ m1_subset_1(E_917,k1_zfmisc_1(k2_zfmisc_1(A_915,B_916)))
      | ~ v1_funct_1(E_917) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_19563])).

tff(c_19594,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_19585])).

tff(c_19603,plain,(
    k5_relat_1('#skF_5','#skF_6') = k6_partfun1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_15468,c_19594])).

tff(c_162,plain,(
    ! [A_14] :
      ( k1_relat_1(k6_partfun1(k2_relat_1(A_14))) = k2_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_153])).

tff(c_18987,plain,
    ( k1_relat_1(k6_partfun1('#skF_3')) = k2_relat_1('#skF_6')
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_18979,c_162])).

tff(c_18993,plain,(
    k1_relat_1(k6_partfun1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_84,c_17859,c_116,c_84,c_17859,c_18979,c_18987])).

tff(c_19716,plain,
    ( k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3')
    | k1_xboole_0 = '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_4'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_19708])).

tff(c_19728,plain,
    ( k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_78,c_74,c_19716])).

tff(c_19729,plain,(
    k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_19728])).

tff(c_19809,plain,
    ( k1_relat_1(k6_partfun1('#skF_3')) = k1_relat_1('#skF_5')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_19729,c_18])).

tff(c_19829,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_90,c_74,c_18993,c_19809])).

tff(c_30,plain,(
    ! [A_16,B_18] :
      ( k2_funct_1(A_16) = B_18
      | k6_relat_1(k1_relat_1(A_16)) != k5_relat_1(A_16,B_18)
      | k2_relat_1(A_16) != k1_relat_1(B_18)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_91,plain,(
    ! [A_16,B_18] :
      ( k2_funct_1(A_16) = B_18
      | k6_partfun1(k1_relat_1(A_16)) != k5_relat_1(A_16,B_18)
      | k2_relat_1(A_16) != k1_relat_1(B_18)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_30])).

tff(c_19845,plain,(
    ! [B_18] :
      ( k2_funct_1('#skF_5') = B_18
      | k5_relat_1('#skF_5',B_18) != k6_partfun1('#skF_3')
      | k2_relat_1('#skF_5') != k1_relat_1(B_18)
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19829,c_91])).

tff(c_19962,plain,(
    ! [B_930] :
      ( k2_funct_1('#skF_5') = B_930
      | k5_relat_1('#skF_5',B_930) != k6_partfun1('#skF_3')
      | k1_relat_1(B_930) != '#skF_4'
      | ~ v1_funct_1(B_930)
      | ~ v1_relat_1(B_930) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_90,c_74,c_135,c_19845])).

tff(c_19986,plain,
    ( k2_funct_1('#skF_5') = '#skF_6'
    | k5_relat_1('#skF_5','#skF_6') != k6_partfun1('#skF_3')
    | k1_relat_1('#skF_6') != '#skF_4'
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_116,c_19962])).

tff(c_20008,plain,(
    k2_funct_1('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_19761,c_19603,c_19986])).

tff(c_20010,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_20008])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:11:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.52/6.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.52/6.56  
% 13.52/6.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.52/6.56  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 13.52/6.56  
% 13.52/6.56  %Foreground sorts:
% 13.52/6.56  
% 13.52/6.56  
% 13.52/6.56  %Background operators:
% 13.52/6.56  
% 13.52/6.56  
% 13.52/6.56  %Foreground operators:
% 13.52/6.56  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 13.52/6.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.52/6.56  tff('#skF_2', type, '#skF_2': $i > $i).
% 13.52/6.56  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 13.52/6.56  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 13.52/6.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.52/6.56  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 13.52/6.56  tff('#skF_1', type, '#skF_1': $i > $i).
% 13.52/6.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.52/6.56  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 13.52/6.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.52/6.56  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.52/6.56  tff('#skF_5', type, '#skF_5': $i).
% 13.52/6.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.52/6.56  tff('#skF_6', type, '#skF_6': $i).
% 13.52/6.56  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 13.52/6.56  tff('#skF_3', type, '#skF_3': $i).
% 13.52/6.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.52/6.56  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 13.52/6.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.52/6.56  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 13.52/6.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.52/6.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.52/6.56  tff('#skF_4', type, '#skF_4': $i).
% 13.52/6.56  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 13.52/6.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.52/6.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.52/6.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.52/6.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.52/6.56  
% 13.52/6.59  tff(f_270, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 13.52/6.59  tff(f_133, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 13.52/6.59  tff(f_137, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 13.52/6.59  tff(f_228, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 13.52/6.59  tff(f_112, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_1)).
% 13.52/6.59  tff(f_33, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 13.52/6.59  tff(f_244, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 13.52/6.59  tff(f_49, axiom, (![A, B]: ((((((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) & v2_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v2_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_funct_1)).
% 13.52/6.59  tff(f_167, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 13.52/6.59  tff(f_145, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 13.52/6.59  tff(f_157, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 13.52/6.59  tff(f_212, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 13.52/6.59  tff(f_169, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 13.52/6.59  tff(f_104, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 13.52/6.59  tff(f_94, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_funct_1)).
% 13.52/6.59  tff(f_186, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 13.52/6.59  tff(f_84, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 13.52/6.59  tff(f_129, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 13.52/6.59  tff(c_68, plain, (k2_funct_1('#skF_5')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_270])).
% 13.52/6.59  tff(c_84, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_270])).
% 13.52/6.59  tff(c_80, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_270])).
% 13.52/6.59  tff(c_109, plain, (![C_63, A_64, B_65]: (v1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 13.52/6.59  tff(c_116, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_80, c_109])).
% 13.52/6.59  tff(c_82, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_270])).
% 13.52/6.59  tff(c_126, plain, (![A_70, B_71, C_72]: (k2_relset_1(A_70, B_71, C_72)=k2_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 13.52/6.59  tff(c_133, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_80, c_126])).
% 13.52/6.59  tff(c_15537, plain, (![C_585, A_586, B_587]: (v1_funct_1(k2_funct_1(C_585)) | k2_relset_1(A_586, B_587, C_585)!=B_587 | ~v2_funct_1(C_585) | ~m1_subset_1(C_585, k1_zfmisc_1(k2_zfmisc_1(A_586, B_587))) | ~v1_funct_2(C_585, A_586, B_587) | ~v1_funct_1(C_585))), inference(cnfTransformation, [status(thm)], [f_228])).
% 13.52/6.59  tff(c_15543, plain, (v1_funct_1(k2_funct_1('#skF_6')) | k2_relset_1('#skF_4', '#skF_3', '#skF_6')!='#skF_3' | ~v2_funct_1('#skF_6') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_80, c_15537])).
% 13.52/6.59  tff(c_15551, plain, (v1_funct_1(k2_funct_1('#skF_6')) | k2_relat_1('#skF_6')!='#skF_3' | ~v2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_133, c_15543])).
% 13.52/6.59  tff(c_15567, plain, (~v2_funct_1('#skF_6')), inference(splitLeft, [status(thm)], [c_15551])).
% 13.52/6.59  tff(c_72, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_270])).
% 13.52/6.59  tff(c_90, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_270])).
% 13.52/6.59  tff(c_88, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_270])).
% 13.52/6.59  tff(c_86, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_270])).
% 13.52/6.59  tff(c_117, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_109])).
% 13.52/6.59  tff(c_74, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_270])).
% 13.52/6.59  tff(c_28, plain, (![A_15]: (v2_funct_1(k2_funct_1(A_15)) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_112])).
% 13.52/6.59  tff(c_4, plain, (![A_1]: (v1_relat_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.52/6.59  tff(c_78, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_270])).
% 13.52/6.59  tff(c_15546, plain, (v1_funct_1(k2_funct_1('#skF_5')) | k2_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_15537])).
% 13.52/6.59  tff(c_15554, plain, (v1_funct_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_74, c_78, c_15546])).
% 13.52/6.59  tff(c_70, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_270])).
% 13.52/6.59  tff(c_16857, plain, (![A_724, C_725, B_726]: (k6_partfun1(A_724)=k5_relat_1(C_725, k2_funct_1(C_725)) | k1_xboole_0=B_726 | ~v2_funct_1(C_725) | k2_relset_1(A_724, B_726, C_725)!=B_726 | ~m1_subset_1(C_725, k1_zfmisc_1(k2_zfmisc_1(A_724, B_726))) | ~v1_funct_2(C_725, A_724, B_726) | ~v1_funct_1(C_725))), inference(cnfTransformation, [status(thm)], [f_244])).
% 13.52/6.59  tff(c_16865, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3') | k1_xboole_0='#skF_4' | ~v2_funct_1('#skF_5') | k2_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_4' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_16857])).
% 13.52/6.59  tff(c_16877, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_78, c_74, c_16865])).
% 13.52/6.59  tff(c_16878, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_70, c_16877])).
% 13.52/6.59  tff(c_6, plain, (![A_2, B_3]: (v2_funct_1(k5_relat_1(A_2, B_3)) | ~v2_funct_1(B_3) | ~v1_funct_1(B_3) | ~v1_relat_1(B_3) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.52/6.59  tff(c_16884, plain, (v2_funct_1(k6_partfun1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_5')) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_16878, c_6])).
% 13.52/6.59  tff(c_16906, plain, (v2_funct_1(k6_partfun1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_90, c_74, c_15554, c_16884])).
% 13.52/6.59  tff(c_17036, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_16906])).
% 13.52/6.59  tff(c_17039, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_4, c_17036])).
% 13.52/6.59  tff(c_17043, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_117, c_90, c_17039])).
% 13.52/6.59  tff(c_17044, plain, (~v2_funct_1(k2_funct_1('#skF_5')) | v2_funct_1(k6_partfun1('#skF_3'))), inference(splitRight, [status(thm)], [c_16906])).
% 13.52/6.59  tff(c_17051, plain, (~v2_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_17044])).
% 13.52/6.59  tff(c_17054, plain, (~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_17051])).
% 13.52/6.59  tff(c_17058, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_117, c_90, c_74, c_17054])).
% 13.52/6.59  tff(c_17059, plain, (v2_funct_1(k6_partfun1('#skF_3'))), inference(splitRight, [status(thm)], [c_17044])).
% 13.52/6.59  tff(c_539, plain, (![C_121, A_119, F_120, E_122, D_123, B_124]: (k1_partfun1(A_119, B_124, C_121, D_123, E_122, F_120)=k5_relat_1(E_122, F_120) | ~m1_subset_1(F_120, k1_zfmisc_1(k2_zfmisc_1(C_121, D_123))) | ~v1_funct_1(F_120) | ~m1_subset_1(E_122, k1_zfmisc_1(k2_zfmisc_1(A_119, B_124))) | ~v1_funct_1(E_122))), inference(cnfTransformation, [status(thm)], [f_167])).
% 13.52/6.59  tff(c_541, plain, (![A_119, B_124, E_122]: (k1_partfun1(A_119, B_124, '#skF_4', '#skF_3', E_122, '#skF_6')=k5_relat_1(E_122, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_122, k1_zfmisc_1(k2_zfmisc_1(A_119, B_124))) | ~v1_funct_1(E_122))), inference(resolution, [status(thm)], [c_80, c_539])).
% 13.52/6.59  tff(c_560, plain, (![A_125, B_126, E_127]: (k1_partfun1(A_125, B_126, '#skF_4', '#skF_3', E_127, '#skF_6')=k5_relat_1(E_127, '#skF_6') | ~m1_subset_1(E_127, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))) | ~v1_funct_1(E_127))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_541])).
% 13.52/6.59  tff(c_566, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_560])).
% 13.52/6.59  tff(c_572, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_566])).
% 13.52/6.59  tff(c_76, plain, (r2_relset_1('#skF_3', '#skF_3', k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k6_partfun1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_270])).
% 13.52/6.59  tff(c_248, plain, (![D_88, C_89, A_90, B_91]: (D_88=C_89 | ~r2_relset_1(A_90, B_91, C_89, D_88) | ~m1_subset_1(D_88, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 13.52/6.59  tff(c_263, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k6_partfun1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_76, c_248])).
% 13.52/6.59  tff(c_313, plain, (~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(splitLeft, [status(thm)], [c_263])).
% 13.52/6.59  tff(c_579, plain, (~m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_572, c_313])).
% 13.52/6.59  tff(c_924, plain, (![E_155, F_154, B_152, D_151, C_156, A_153]: (m1_subset_1(k1_partfun1(A_153, B_152, C_156, D_151, E_155, F_154), k1_zfmisc_1(k2_zfmisc_1(A_153, D_151))) | ~m1_subset_1(F_154, k1_zfmisc_1(k2_zfmisc_1(C_156, D_151))) | ~v1_funct_1(F_154) | ~m1_subset_1(E_155, k1_zfmisc_1(k2_zfmisc_1(A_153, B_152))) | ~v1_funct_1(E_155))), inference(cnfTransformation, [status(thm)], [f_157])).
% 13.52/6.59  tff(c_973, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_572, c_924])).
% 13.52/6.59  tff(c_997, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_84, c_80, c_973])).
% 13.52/6.59  tff(c_999, plain, $false, inference(negUnitSimplification, [status(thm)], [c_579, c_997])).
% 13.52/6.59  tff(c_1000, plain, (~m1_subset_1(k6_partfun1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3')), inference(splitRight, [status(thm)], [c_263])).
% 13.52/6.59  tff(c_1013, plain, (~m1_subset_1(k6_partfun1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(splitLeft, [status(thm)], [c_1000])).
% 13.52/6.59  tff(c_1105, plain, (![C_159, A_160, B_161]: (v1_funct_1(k2_funct_1(C_159)) | k2_relset_1(A_160, B_161, C_159)!=B_161 | ~v2_funct_1(C_159) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))) | ~v1_funct_2(C_159, A_160, B_161) | ~v1_funct_1(C_159))), inference(cnfTransformation, [status(thm)], [f_228])).
% 13.52/6.59  tff(c_1114, plain, (v1_funct_1(k2_funct_1('#skF_5')) | k2_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_1105])).
% 13.52/6.59  tff(c_1122, plain, (v1_funct_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_74, c_78, c_1114])).
% 13.52/6.59  tff(c_58, plain, (![C_55, B_54, A_53]: (m1_subset_1(k2_funct_1(C_55), k1_zfmisc_1(k2_zfmisc_1(B_54, A_53))) | k2_relset_1(A_53, B_54, C_55)!=B_54 | ~v2_funct_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))) | ~v1_funct_2(C_55, A_53, B_54) | ~v1_funct_1(C_55))), inference(cnfTransformation, [status(thm)], [f_228])).
% 13.52/6.59  tff(c_1455, plain, (![C_211, A_209, F_210, E_212, B_214, D_213]: (k1_partfun1(A_209, B_214, C_211, D_213, E_212, F_210)=k5_relat_1(E_212, F_210) | ~m1_subset_1(F_210, k1_zfmisc_1(k2_zfmisc_1(C_211, D_213))) | ~v1_funct_1(F_210) | ~m1_subset_1(E_212, k1_zfmisc_1(k2_zfmisc_1(A_209, B_214))) | ~v1_funct_1(E_212))), inference(cnfTransformation, [status(thm)], [f_167])).
% 13.52/6.59  tff(c_9271, plain, (![E_460, B_462, A_459, C_458, A_461, B_463]: (k1_partfun1(A_461, B_462, B_463, A_459, E_460, k2_funct_1(C_458))=k5_relat_1(E_460, k2_funct_1(C_458)) | ~v1_funct_1(k2_funct_1(C_458)) | ~m1_subset_1(E_460, k1_zfmisc_1(k2_zfmisc_1(A_461, B_462))) | ~v1_funct_1(E_460) | k2_relset_1(A_459, B_463, C_458)!=B_463 | ~v2_funct_1(C_458) | ~m1_subset_1(C_458, k1_zfmisc_1(k2_zfmisc_1(A_459, B_463))) | ~v1_funct_2(C_458, A_459, B_463) | ~v1_funct_1(C_458))), inference(resolution, [status(thm)], [c_58, c_1455])).
% 13.52/6.59  tff(c_9301, plain, (![B_463, A_459, C_458]: (k1_partfun1('#skF_4', '#skF_3', B_463, A_459, '#skF_6', k2_funct_1(C_458))=k5_relat_1('#skF_6', k2_funct_1(C_458)) | ~v1_funct_1(k2_funct_1(C_458)) | ~v1_funct_1('#skF_6') | k2_relset_1(A_459, B_463, C_458)!=B_463 | ~v2_funct_1(C_458) | ~m1_subset_1(C_458, k1_zfmisc_1(k2_zfmisc_1(A_459, B_463))) | ~v1_funct_2(C_458, A_459, B_463) | ~v1_funct_1(C_458))), inference(resolution, [status(thm)], [c_80, c_9271])).
% 13.52/6.59  tff(c_11593, plain, (![B_550, A_551, C_552]: (k1_partfun1('#skF_4', '#skF_3', B_550, A_551, '#skF_6', k2_funct_1(C_552))=k5_relat_1('#skF_6', k2_funct_1(C_552)) | ~v1_funct_1(k2_funct_1(C_552)) | k2_relset_1(A_551, B_550, C_552)!=B_550 | ~v2_funct_1(C_552) | ~m1_subset_1(C_552, k1_zfmisc_1(k2_zfmisc_1(A_551, B_550))) | ~v1_funct_2(C_552, A_551, B_550) | ~v1_funct_1(C_552))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_9301])).
% 13.52/6.59  tff(c_11641, plain, (k1_partfun1('#skF_4', '#skF_3', '#skF_4', '#skF_3', '#skF_6', k2_funct_1('#skF_5'))=k5_relat_1('#skF_6', k2_funct_1('#skF_5')) | ~v1_funct_1(k2_funct_1('#skF_5')) | k2_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_11593])).
% 13.52/6.59  tff(c_11685, plain, (k1_partfun1('#skF_4', '#skF_3', '#skF_4', '#skF_3', '#skF_6', k2_funct_1('#skF_5'))=k5_relat_1('#skF_6', k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_74, c_78, c_1122, c_11641])).
% 13.52/6.59  tff(c_1337, plain, (![C_198, B_199, A_200]: (m1_subset_1(k2_funct_1(C_198), k1_zfmisc_1(k2_zfmisc_1(B_199, A_200))) | k2_relset_1(A_200, B_199, C_198)!=B_199 | ~v2_funct_1(C_198) | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(A_200, B_199))) | ~v1_funct_2(C_198, A_200, B_199) | ~v1_funct_1(C_198))), inference(cnfTransformation, [status(thm)], [f_228])).
% 13.52/6.59  tff(c_42, plain, (![E_33, A_29, F_34, D_32, C_31, B_30]: (v1_funct_1(k1_partfun1(A_29, B_30, C_31, D_32, E_33, F_34)) | ~m1_subset_1(F_34, k1_zfmisc_1(k2_zfmisc_1(C_31, D_32))) | ~v1_funct_1(F_34) | ~m1_subset_1(E_33, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))) | ~v1_funct_1(E_33))), inference(cnfTransformation, [status(thm)], [f_157])).
% 13.52/6.59  tff(c_8965, plain, (![B_449, B_446, C_448, A_447, A_451, E_450]: (v1_funct_1(k1_partfun1(A_447, B_446, B_449, A_451, E_450, k2_funct_1(C_448))) | ~v1_funct_1(k2_funct_1(C_448)) | ~m1_subset_1(E_450, k1_zfmisc_1(k2_zfmisc_1(A_447, B_446))) | ~v1_funct_1(E_450) | k2_relset_1(A_451, B_449, C_448)!=B_449 | ~v2_funct_1(C_448) | ~m1_subset_1(C_448, k1_zfmisc_1(k2_zfmisc_1(A_451, B_449))) | ~v1_funct_2(C_448, A_451, B_449) | ~v1_funct_1(C_448))), inference(resolution, [status(thm)], [c_1337, c_42])).
% 13.52/6.59  tff(c_8995, plain, (![B_449, A_451, C_448]: (v1_funct_1(k1_partfun1('#skF_4', '#skF_3', B_449, A_451, '#skF_6', k2_funct_1(C_448))) | ~v1_funct_1(k2_funct_1(C_448)) | ~v1_funct_1('#skF_6') | k2_relset_1(A_451, B_449, C_448)!=B_449 | ~v2_funct_1(C_448) | ~m1_subset_1(C_448, k1_zfmisc_1(k2_zfmisc_1(A_451, B_449))) | ~v1_funct_2(C_448, A_451, B_449) | ~v1_funct_1(C_448))), inference(resolution, [status(thm)], [c_80, c_8965])).
% 13.52/6.59  tff(c_10874, plain, (![B_529, A_530, C_531]: (v1_funct_1(k1_partfun1('#skF_4', '#skF_3', B_529, A_530, '#skF_6', k2_funct_1(C_531))) | ~v1_funct_1(k2_funct_1(C_531)) | k2_relset_1(A_530, B_529, C_531)!=B_529 | ~v2_funct_1(C_531) | ~m1_subset_1(C_531, k1_zfmisc_1(k2_zfmisc_1(A_530, B_529))) | ~v1_funct_2(C_531, A_530, B_529) | ~v1_funct_1(C_531))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_8995])).
% 13.52/6.59  tff(c_10922, plain, (v1_funct_1(k1_partfun1('#skF_4', '#skF_3', '#skF_4', '#skF_3', '#skF_6', k2_funct_1('#skF_5'))) | ~v1_funct_1(k2_funct_1('#skF_5')) | k2_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_10874])).
% 13.52/6.59  tff(c_10966, plain, (v1_funct_1(k1_partfun1('#skF_4', '#skF_3', '#skF_4', '#skF_3', '#skF_6', k2_funct_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_74, c_78, c_1122, c_10922])).
% 13.52/6.59  tff(c_11686, plain, (v1_funct_1(k5_relat_1('#skF_6', k2_funct_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_11685, c_10966])).
% 13.52/6.59  tff(c_1789, plain, (![E_228, B_225, F_227, C_229, D_224, A_226]: (m1_subset_1(k1_partfun1(A_226, B_225, C_229, D_224, E_228, F_227), k1_zfmisc_1(k2_zfmisc_1(A_226, D_224))) | ~m1_subset_1(F_227, k1_zfmisc_1(k2_zfmisc_1(C_229, D_224))) | ~v1_funct_1(F_227) | ~m1_subset_1(E_228, k1_zfmisc_1(k2_zfmisc_1(A_226, B_225))) | ~v1_funct_1(E_228))), inference(cnfTransformation, [status(thm)], [f_157])).
% 13.52/6.59  tff(c_66, plain, (![A_56, C_58, B_57]: (k6_partfun1(A_56)=k5_relat_1(C_58, k2_funct_1(C_58)) | k1_xboole_0=B_57 | ~v2_funct_1(C_58) | k2_relset_1(A_56, B_57, C_58)!=B_57 | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))) | ~v1_funct_2(C_58, A_56, B_57) | ~v1_funct_1(C_58))), inference(cnfTransformation, [status(thm)], [f_244])).
% 13.52/6.59  tff(c_1834, plain, (![E_228, B_225, F_227, C_229, D_224, A_226]: (k5_relat_1(k1_partfun1(A_226, B_225, C_229, D_224, E_228, F_227), k2_funct_1(k1_partfun1(A_226, B_225, C_229, D_224, E_228, F_227)))=k6_partfun1(A_226) | k1_xboole_0=D_224 | ~v2_funct_1(k1_partfun1(A_226, B_225, C_229, D_224, E_228, F_227)) | k2_relset_1(A_226, D_224, k1_partfun1(A_226, B_225, C_229, D_224, E_228, F_227))!=D_224 | ~v1_funct_2(k1_partfun1(A_226, B_225, C_229, D_224, E_228, F_227), A_226, D_224) | ~v1_funct_1(k1_partfun1(A_226, B_225, C_229, D_224, E_228, F_227)) | ~m1_subset_1(F_227, k1_zfmisc_1(k2_zfmisc_1(C_229, D_224))) | ~v1_funct_1(F_227) | ~m1_subset_1(E_228, k1_zfmisc_1(k2_zfmisc_1(A_226, B_225))) | ~v1_funct_1(E_228))), inference(resolution, [status(thm)], [c_1789, c_66])).
% 13.52/6.59  tff(c_11690, plain, (k5_relat_1(k5_relat_1('#skF_6', k2_funct_1('#skF_5')), k2_funct_1(k1_partfun1('#skF_4', '#skF_3', '#skF_4', '#skF_3', '#skF_6', k2_funct_1('#skF_5'))))=k6_partfun1('#skF_4') | k1_xboole_0='#skF_3' | ~v2_funct_1(k1_partfun1('#skF_4', '#skF_3', '#skF_4', '#skF_3', '#skF_6', k2_funct_1('#skF_5'))) | k2_relset_1('#skF_4', '#skF_3', k1_partfun1('#skF_4', '#skF_3', '#skF_4', '#skF_3', '#skF_6', k2_funct_1('#skF_5')))!='#skF_3' | ~v1_funct_2(k1_partfun1('#skF_4', '#skF_3', '#skF_4', '#skF_3', '#skF_6', k2_funct_1('#skF_5')), '#skF_4', '#skF_3') | ~v1_funct_1(k1_partfun1('#skF_4', '#skF_3', '#skF_4', '#skF_3', '#skF_6', k2_funct_1('#skF_5'))) | ~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_11685, c_1834])).
% 13.52/6.59  tff(c_11719, plain, (k5_relat_1(k5_relat_1('#skF_6', k2_funct_1('#skF_5')), k2_funct_1(k5_relat_1('#skF_6', k2_funct_1('#skF_5'))))=k6_partfun1('#skF_4') | k1_xboole_0='#skF_3' | ~v2_funct_1(k5_relat_1('#skF_6', k2_funct_1('#skF_5'))) | k2_relset_1('#skF_4', '#skF_3', k5_relat_1('#skF_6', k2_funct_1('#skF_5')))!='#skF_3' | ~v1_funct_2(k5_relat_1('#skF_6', k2_funct_1('#skF_5')), '#skF_4', '#skF_3') | ~v1_funct_1(k5_relat_1('#skF_6', k2_funct_1('#skF_5'))) | ~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_1122, c_11685, c_11685, c_11685, c_11685, c_11685, c_11690])).
% 13.52/6.59  tff(c_11720, plain, (k5_relat_1(k5_relat_1('#skF_6', k2_funct_1('#skF_5')), k2_funct_1(k5_relat_1('#skF_6', k2_funct_1('#skF_5'))))=k6_partfun1('#skF_4') | ~v2_funct_1(k5_relat_1('#skF_6', k2_funct_1('#skF_5'))) | k2_relset_1('#skF_4', '#skF_3', k5_relat_1('#skF_6', k2_funct_1('#skF_5')))!='#skF_3' | ~v1_funct_2(k5_relat_1('#skF_6', k2_funct_1('#skF_5')), '#skF_4', '#skF_3') | ~v1_funct_1(k5_relat_1('#skF_6', k2_funct_1('#skF_5'))) | ~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_72, c_11719])).
% 13.52/6.59  tff(c_13556, plain, (k5_relat_1(k5_relat_1('#skF_6', k2_funct_1('#skF_5')), k2_funct_1(k5_relat_1('#skF_6', k2_funct_1('#skF_5'))))=k6_partfun1('#skF_4') | ~v2_funct_1(k5_relat_1('#skF_6', k2_funct_1('#skF_5'))) | k2_relset_1('#skF_4', '#skF_3', k5_relat_1('#skF_6', k2_funct_1('#skF_5')))!='#skF_3' | ~v1_funct_2(k5_relat_1('#skF_6', k2_funct_1('#skF_5')), '#skF_4', '#skF_3') | ~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_11686, c_11720])).
% 13.52/6.59  tff(c_13557, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_13556])).
% 13.52/6.59  tff(c_13560, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_4' | ~v2_funct_1('#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_13557])).
% 13.52/6.59  tff(c_13564, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_74, c_78, c_13560])).
% 13.52/6.59  tff(c_13566, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_13556])).
% 13.52/6.59  tff(c_1529, plain, (![A_218, C_219, B_220]: (k6_partfun1(A_218)=k5_relat_1(C_219, k2_funct_1(C_219)) | k1_xboole_0=B_220 | ~v2_funct_1(C_219) | k2_relset_1(A_218, B_220, C_219)!=B_220 | ~m1_subset_1(C_219, k1_zfmisc_1(k2_zfmisc_1(A_218, B_220))) | ~v1_funct_2(C_219, A_218, B_220) | ~v1_funct_1(C_219))), inference(cnfTransformation, [status(thm)], [f_244])).
% 13.52/6.59  tff(c_1535, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3') | k1_xboole_0='#skF_4' | ~v2_funct_1('#skF_5') | k2_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_4' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_1529])).
% 13.52/6.59  tff(c_1543, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_78, c_74, c_1535])).
% 13.52/6.59  tff(c_1544, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_70, c_1543])).
% 13.52/6.59  tff(c_9303, plain, (![B_463, A_459, C_458]: (k1_partfun1('#skF_3', '#skF_4', B_463, A_459, '#skF_5', k2_funct_1(C_458))=k5_relat_1('#skF_5', k2_funct_1(C_458)) | ~v1_funct_1(k2_funct_1(C_458)) | ~v1_funct_1('#skF_5') | k2_relset_1(A_459, B_463, C_458)!=B_463 | ~v2_funct_1(C_458) | ~m1_subset_1(C_458, k1_zfmisc_1(k2_zfmisc_1(A_459, B_463))) | ~v1_funct_2(C_458, A_459, B_463) | ~v1_funct_1(C_458))), inference(resolution, [status(thm)], [c_86, c_9271])).
% 13.52/6.59  tff(c_15276, plain, (![B_581, A_582, C_583]: (k1_partfun1('#skF_3', '#skF_4', B_581, A_582, '#skF_5', k2_funct_1(C_583))=k5_relat_1('#skF_5', k2_funct_1(C_583)) | ~v1_funct_1(k2_funct_1(C_583)) | k2_relset_1(A_582, B_581, C_583)!=B_581 | ~v2_funct_1(C_583) | ~m1_subset_1(C_583, k1_zfmisc_1(k2_zfmisc_1(A_582, B_581))) | ~v1_funct_2(C_583, A_582, B_581) | ~v1_funct_1(C_583))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_9303])).
% 13.52/6.59  tff(c_15336, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', k2_funct_1('#skF_5'))=k5_relat_1('#skF_5', k2_funct_1('#skF_5')) | ~v1_funct_1(k2_funct_1('#skF_5')) | k2_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_15276])).
% 13.52/6.59  tff(c_15392, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_74, c_78, c_1122, c_1544, c_15336])).
% 13.52/6.59  tff(c_40, plain, (![E_33, A_29, F_34, D_32, C_31, B_30]: (m1_subset_1(k1_partfun1(A_29, B_30, C_31, D_32, E_33, F_34), k1_zfmisc_1(k2_zfmisc_1(A_29, D_32))) | ~m1_subset_1(F_34, k1_zfmisc_1(k2_zfmisc_1(C_31, D_32))) | ~v1_funct_1(F_34) | ~m1_subset_1(E_33, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))) | ~v1_funct_1(E_33))), inference(cnfTransformation, [status(thm)], [f_157])).
% 13.52/6.59  tff(c_15430, plain, (m1_subset_1(k6_partfun1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_15392, c_40])).
% 13.52/6.59  tff(c_15465, plain, (m1_subset_1(k6_partfun1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_1122, c_13566, c_15430])).
% 13.52/6.59  tff(c_15467, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1013, c_15465])).
% 13.52/6.59  tff(c_15468, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3')), inference(splitRight, [status(thm)], [c_1000])).
% 13.52/6.59  tff(c_17836, plain, (![E_755, C_757, B_756, A_753, D_754]: (k1_xboole_0=C_757 | v2_funct_1(E_755) | k2_relset_1(A_753, B_756, D_754)!=B_756 | ~v2_funct_1(k1_partfun1(A_753, B_756, B_756, C_757, D_754, E_755)) | ~m1_subset_1(E_755, k1_zfmisc_1(k2_zfmisc_1(B_756, C_757))) | ~v1_funct_2(E_755, B_756, C_757) | ~v1_funct_1(E_755) | ~m1_subset_1(D_754, k1_zfmisc_1(k2_zfmisc_1(A_753, B_756))) | ~v1_funct_2(D_754, A_753, B_756) | ~v1_funct_1(D_754))), inference(cnfTransformation, [status(thm)], [f_212])).
% 13.52/6.59  tff(c_17844, plain, (k1_xboole_0='#skF_3' | v2_funct_1('#skF_6') | k2_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_4' | ~v2_funct_1(k6_partfun1('#skF_3')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_15468, c_17836])).
% 13.52/6.59  tff(c_17855, plain, (k1_xboole_0='#skF_3' | v2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_84, c_82, c_80, c_17059, c_78, c_17844])).
% 13.52/6.59  tff(c_17857, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15567, c_72, c_17855])).
% 13.52/6.59  tff(c_17859, plain, (v2_funct_1('#skF_6')), inference(splitRight, [status(thm)], [c_15551])).
% 13.52/6.59  tff(c_132, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_126])).
% 13.52/6.59  tff(c_135, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_132])).
% 13.52/6.59  tff(c_46, plain, (![A_41]: (k6_relat_1(A_41)=k6_partfun1(A_41))), inference(cnfTransformation, [status(thm)], [f_169])).
% 13.52/6.59  tff(c_24, plain, (![A_14]: (k5_relat_1(k2_funct_1(A_14), A_14)=k6_relat_1(k2_relat_1(A_14)) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_104])).
% 13.52/6.59  tff(c_93, plain, (![A_14]: (k5_relat_1(k2_funct_1(A_14), A_14)=k6_partfun1(k2_relat_1(A_14)) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_24])).
% 13.52/6.59  tff(c_153, plain, (![A_74]: (k1_relat_1(k5_relat_1(k2_funct_1(A_74), A_74))=k2_relat_1(A_74) | ~v2_funct_1(A_74) | ~v1_funct_1(A_74) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.52/6.59  tff(c_264, plain, (![A_92]: (k1_relat_1(k6_partfun1(k2_relat_1(A_92)))=k2_relat_1(A_92) | ~v2_funct_1(A_92) | ~v1_funct_1(A_92) | ~v1_relat_1(A_92) | ~v2_funct_1(A_92) | ~v1_funct_1(A_92) | ~v1_relat_1(A_92))), inference(superposition, [status(thm), theory('equality')], [c_93, c_153])).
% 13.52/6.59  tff(c_279, plain, (k1_relat_1(k6_partfun1('#skF_4'))=k2_relat_1('#skF_5') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_135, c_264])).
% 13.52/6.59  tff(c_283, plain, (k1_relat_1(k6_partfun1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_117, c_90, c_74, c_117, c_90, c_74, c_135, c_279])).
% 13.52/6.59  tff(c_17858, plain, (k2_relat_1('#skF_6')!='#skF_3' | v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_15551])).
% 13.52/6.59  tff(c_17860, plain, (k2_relat_1('#skF_6')!='#skF_3'), inference(splitLeft, [status(thm)], [c_17858])).
% 13.52/6.59  tff(c_15483, plain, (r2_relset_1('#skF_3', '#skF_3', k6_partfun1('#skF_3'), k6_partfun1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_15468, c_76])).
% 13.52/6.59  tff(c_18962, plain, (![A_835, B_836, C_837, D_838]: (k2_relset_1(A_835, B_836, C_837)=B_836 | ~r2_relset_1(B_836, B_836, k1_partfun1(B_836, A_835, A_835, B_836, D_838, C_837), k6_partfun1(B_836)) | ~m1_subset_1(D_838, k1_zfmisc_1(k2_zfmisc_1(B_836, A_835))) | ~v1_funct_2(D_838, B_836, A_835) | ~v1_funct_1(D_838) | ~m1_subset_1(C_837, k1_zfmisc_1(k2_zfmisc_1(A_835, B_836))) | ~v1_funct_2(C_837, A_835, B_836) | ~v1_funct_1(C_837))), inference(cnfTransformation, [status(thm)], [f_186])).
% 13.52/6.59  tff(c_18971, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_6')='#skF_3' | ~r2_relset_1('#skF_3', '#skF_3', k6_partfun1('#skF_3'), k6_partfun1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_15468, c_18962])).
% 13.52/6.59  tff(c_18975, plain, (k2_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_90, c_88, c_86, c_15483, c_133, c_18971])).
% 13.52/6.59  tff(c_18977, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17860, c_18975])).
% 13.52/6.59  tff(c_18979, plain, (k2_relat_1('#skF_6')='#skF_3'), inference(splitRight, [status(thm)], [c_17858])).
% 13.52/6.59  tff(c_18980, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18979, c_133])).
% 13.52/6.59  tff(c_19708, plain, (![A_924, C_925, B_926]: (k6_partfun1(A_924)=k5_relat_1(C_925, k2_funct_1(C_925)) | k1_xboole_0=B_926 | ~v2_funct_1(C_925) | k2_relset_1(A_924, B_926, C_925)!=B_926 | ~m1_subset_1(C_925, k1_zfmisc_1(k2_zfmisc_1(A_924, B_926))) | ~v1_funct_2(C_925, A_924, B_926) | ~v1_funct_1(C_925))), inference(cnfTransformation, [status(thm)], [f_244])).
% 13.52/6.59  tff(c_19714, plain, (k5_relat_1('#skF_6', k2_funct_1('#skF_6'))=k6_partfun1('#skF_4') | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_6') | k2_relset_1('#skF_4', '#skF_3', '#skF_6')!='#skF_3' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_80, c_19708])).
% 13.52/6.59  tff(c_19724, plain, (k5_relat_1('#skF_6', k2_funct_1('#skF_6'))=k6_partfun1('#skF_4') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_18980, c_17859, c_19714])).
% 13.52/6.59  tff(c_19725, plain, (k5_relat_1('#skF_6', k2_funct_1('#skF_6'))=k6_partfun1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_72, c_19724])).
% 13.52/6.59  tff(c_18, plain, (![A_12]: (k1_relat_1(k5_relat_1(A_12, k2_funct_1(A_12)))=k1_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_84])).
% 13.52/6.59  tff(c_19741, plain, (k1_relat_1(k6_partfun1('#skF_4'))=k1_relat_1('#skF_6') | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_19725, c_18])).
% 13.52/6.59  tff(c_19761, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_84, c_17859, c_283, c_19741])).
% 13.52/6.59  tff(c_19559, plain, (![E_912, B_914, A_909, D_913, F_910, C_911]: (k1_partfun1(A_909, B_914, C_911, D_913, E_912, F_910)=k5_relat_1(E_912, F_910) | ~m1_subset_1(F_910, k1_zfmisc_1(k2_zfmisc_1(C_911, D_913))) | ~v1_funct_1(F_910) | ~m1_subset_1(E_912, k1_zfmisc_1(k2_zfmisc_1(A_909, B_914))) | ~v1_funct_1(E_912))), inference(cnfTransformation, [status(thm)], [f_167])).
% 13.52/6.59  tff(c_19563, plain, (![A_909, B_914, E_912]: (k1_partfun1(A_909, B_914, '#skF_4', '#skF_3', E_912, '#skF_6')=k5_relat_1(E_912, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_912, k1_zfmisc_1(k2_zfmisc_1(A_909, B_914))) | ~v1_funct_1(E_912))), inference(resolution, [status(thm)], [c_80, c_19559])).
% 13.52/6.59  tff(c_19585, plain, (![A_915, B_916, E_917]: (k1_partfun1(A_915, B_916, '#skF_4', '#skF_3', E_917, '#skF_6')=k5_relat_1(E_917, '#skF_6') | ~m1_subset_1(E_917, k1_zfmisc_1(k2_zfmisc_1(A_915, B_916))) | ~v1_funct_1(E_917))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_19563])).
% 13.52/6.59  tff(c_19594, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_19585])).
% 13.52/6.59  tff(c_19603, plain, (k5_relat_1('#skF_5', '#skF_6')=k6_partfun1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_15468, c_19594])).
% 13.52/6.59  tff(c_162, plain, (![A_14]: (k1_relat_1(k6_partfun1(k2_relat_1(A_14)))=k2_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(superposition, [status(thm), theory('equality')], [c_93, c_153])).
% 13.52/6.59  tff(c_18987, plain, (k1_relat_1(k6_partfun1('#skF_3'))=k2_relat_1('#skF_6') | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_18979, c_162])).
% 13.52/6.59  tff(c_18993, plain, (k1_relat_1(k6_partfun1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_84, c_17859, c_116, c_84, c_17859, c_18979, c_18987])).
% 13.52/6.59  tff(c_19716, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3') | k1_xboole_0='#skF_4' | ~v2_funct_1('#skF_5') | k2_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_4' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_19708])).
% 13.52/6.59  tff(c_19728, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_78, c_74, c_19716])).
% 13.52/6.59  tff(c_19729, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_70, c_19728])).
% 13.52/6.59  tff(c_19809, plain, (k1_relat_1(k6_partfun1('#skF_3'))=k1_relat_1('#skF_5') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_19729, c_18])).
% 13.52/6.59  tff(c_19829, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_117, c_90, c_74, c_18993, c_19809])).
% 13.52/6.59  tff(c_30, plain, (![A_16, B_18]: (k2_funct_1(A_16)=B_18 | k6_relat_1(k1_relat_1(A_16))!=k5_relat_1(A_16, B_18) | k2_relat_1(A_16)!=k1_relat_1(B_18) | ~v2_funct_1(A_16) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_129])).
% 13.52/6.59  tff(c_91, plain, (![A_16, B_18]: (k2_funct_1(A_16)=B_18 | k6_partfun1(k1_relat_1(A_16))!=k5_relat_1(A_16, B_18) | k2_relat_1(A_16)!=k1_relat_1(B_18) | ~v2_funct_1(A_16) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_30])).
% 13.52/6.59  tff(c_19845, plain, (![B_18]: (k2_funct_1('#skF_5')=B_18 | k5_relat_1('#skF_5', B_18)!=k6_partfun1('#skF_3') | k2_relat_1('#skF_5')!=k1_relat_1(B_18) | ~v2_funct_1('#skF_5') | ~v1_funct_1(B_18) | ~v1_relat_1(B_18) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_19829, c_91])).
% 13.52/6.59  tff(c_19962, plain, (![B_930]: (k2_funct_1('#skF_5')=B_930 | k5_relat_1('#skF_5', B_930)!=k6_partfun1('#skF_3') | k1_relat_1(B_930)!='#skF_4' | ~v1_funct_1(B_930) | ~v1_relat_1(B_930))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_90, c_74, c_135, c_19845])).
% 13.52/6.59  tff(c_19986, plain, (k2_funct_1('#skF_5')='#skF_6' | k5_relat_1('#skF_5', '#skF_6')!=k6_partfun1('#skF_3') | k1_relat_1('#skF_6')!='#skF_4' | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_116, c_19962])).
% 13.52/6.59  tff(c_20008, plain, (k2_funct_1('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_19761, c_19603, c_19986])).
% 13.52/6.59  tff(c_20010, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_20008])).
% 13.52/6.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.52/6.59  
% 13.52/6.59  Inference rules
% 13.52/6.59  ----------------------
% 13.52/6.59  #Ref     : 0
% 13.52/6.59  #Sup     : 3956
% 13.52/6.59  #Fact    : 0
% 13.52/6.59  #Define  : 0
% 13.52/6.59  #Split   : 84
% 13.52/6.59  #Chain   : 0
% 13.52/6.59  #Close   : 0
% 13.52/6.59  
% 13.52/6.59  Ordering : KBO
% 13.52/6.59  
% 13.52/6.59  Simplification rules
% 13.52/6.59  ----------------------
% 13.52/6.59  #Subsume      : 697
% 13.52/6.59  #Demod        : 8542
% 13.52/6.59  #Tautology    : 838
% 13.52/6.59  #SimpNegUnit  : 412
% 13.52/6.59  #BackRed      : 99
% 13.52/6.59  
% 13.52/6.59  #Partial instantiations: 0
% 13.52/6.59  #Strategies tried      : 1
% 13.52/6.59  
% 13.52/6.59  Timing (in seconds)
% 13.52/6.59  ----------------------
% 13.52/6.59  Preprocessing        : 0.40
% 13.52/6.59  Parsing              : 0.21
% 13.52/6.59  CNF conversion       : 0.03
% 13.52/6.59  Main loop            : 5.40
% 13.52/6.59  Inferencing          : 1.33
% 13.52/6.59  Reduction            : 2.80
% 13.52/6.59  Demodulation         : 2.32
% 13.52/6.59  BG Simplification    : 0.11
% 13.52/6.59  Subsumption          : 0.94
% 13.52/6.59  Abstraction          : 0.17
% 13.52/6.59  MUC search           : 0.00
% 13.52/6.59  Cooper               : 0.00
% 13.52/6.59  Total                : 5.87
% 13.52/6.59  Index Insertion      : 0.00
% 13.52/6.59  Index Deletion       : 0.00
% 13.52/6.59  Index Matching       : 0.00
% 13.52/6.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
