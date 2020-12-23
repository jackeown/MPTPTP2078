%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:58 EST 2020

% Result     : Theorem 34.63s
% Output     : CNFRefutation 34.75s
% Verified   : 
% Statistics : Number of formulae       :  344 (4997 expanded)
%              Number of leaves         :   47 (1720 expanded)
%              Depth                    :   28
%              Number of atoms          : 1029 (19975 expanded)
%              Number of equality atoms :  266 (4900 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_256,negated_conjecture,(
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

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_121,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_143,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_162,axiom,(
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

tff(f_230,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_145,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_204,axiom,(
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

tff(f_113,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_133,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_33,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_220,axiom,(
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

tff(f_188,axiom,(
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

tff(f_91,axiom,(
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

tff(f_54,axiom,(
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

tff(f_74,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(c_74,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_86,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_119,plain,(
    ! [C_63,A_64,B_65] :
      ( v1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_127,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_119])).

tff(c_90,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_128,plain,(
    ! [C_66,B_67,A_68] :
      ( v5_relat_1(C_66,B_67)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_68,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_136,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_86,c_128])).

tff(c_160,plain,(
    ! [B_75,A_76] :
      ( k2_relat_1(B_75) = A_76
      | ~ v2_funct_2(B_75,A_76)
      | ~ v5_relat_1(B_75,A_76)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_163,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_136,c_160])).

tff(c_169,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_163])).

tff(c_173,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_169])).

tff(c_88,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_96,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_94,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_92,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_2432,plain,(
    ! [C_215,D_217,F_214,E_212,A_216,B_213] :
      ( k1_partfun1(A_216,B_213,C_215,D_217,E_212,F_214) = k5_relat_1(E_212,F_214)
      | ~ m1_subset_1(F_214,k1_zfmisc_1(k2_zfmisc_1(C_215,D_217)))
      | ~ v1_funct_1(F_214)
      | ~ m1_subset_1(E_212,k1_zfmisc_1(k2_zfmisc_1(A_216,B_213)))
      | ~ v1_funct_1(E_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_2450,plain,(
    ! [A_216,B_213,E_212] :
      ( k1_partfun1(A_216,B_213,'#skF_2','#skF_1',E_212,'#skF_4') = k5_relat_1(E_212,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_212,k1_zfmisc_1(k2_zfmisc_1(A_216,B_213)))
      | ~ v1_funct_1(E_212) ) ),
    inference(resolution,[status(thm)],[c_86,c_2432])).

tff(c_2752,plain,(
    ! [A_224,B_225,E_226] :
      ( k1_partfun1(A_224,B_225,'#skF_2','#skF_1',E_226,'#skF_4') = k5_relat_1(E_226,'#skF_4')
      | ~ m1_subset_1(E_226,k1_zfmisc_1(k2_zfmisc_1(A_224,B_225)))
      | ~ v1_funct_1(E_226) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_2450])).

tff(c_2779,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_2752])).

tff(c_2801,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_2779])).

tff(c_82,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_2813,plain,(
    r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2801,c_82])).

tff(c_292,plain,(
    ! [A_89,B_90,C_91] :
      ( k2_relset_1(A_89,B_90,C_91) = k2_relat_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_301,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_292])).

tff(c_3532,plain,(
    ! [A_247,B_248,C_249,D_250] :
      ( k2_relset_1(A_247,B_248,C_249) = B_248
      | ~ r2_relset_1(B_248,B_248,k1_partfun1(B_248,A_247,A_247,B_248,D_250,C_249),k6_partfun1(B_248))
      | ~ m1_subset_1(D_250,k1_zfmisc_1(k2_zfmisc_1(B_248,A_247)))
      | ~ v1_funct_2(D_250,B_248,A_247)
      | ~ v1_funct_1(D_250)
      | ~ m1_subset_1(C_249,k1_zfmisc_1(k2_zfmisc_1(A_247,B_248)))
      | ~ v1_funct_2(C_249,A_247,B_248)
      | ~ v1_funct_1(C_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_3538,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_4'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2801,c_3532])).

tff(c_3543,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_96,c_94,c_92,c_2813,c_301,c_3538])).

tff(c_306,plain,(
    ! [A_92] :
      ( m1_subset_1(A_92,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_92),k2_relat_1(A_92))))
      | ~ v1_funct_1(A_92)
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_26,plain,(
    ! [C_16,B_15,A_14] :
      ( v5_relat_1(C_16,B_15)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_372,plain,(
    ! [A_94] :
      ( v5_relat_1(A_94,k2_relat_1(A_94))
      | ~ v1_funct_1(A_94)
      | ~ v1_relat_1(A_94) ) ),
    inference(resolution,[status(thm)],[c_306,c_26])).

tff(c_36,plain,(
    ! [B_25] :
      ( v2_funct_2(B_25,k2_relat_1(B_25))
      | ~ v5_relat_1(B_25,k2_relat_1(B_25))
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_387,plain,(
    ! [A_94] :
      ( v2_funct_2(A_94,k2_relat_1(A_94))
      | ~ v1_funct_1(A_94)
      | ~ v1_relat_1(A_94) ) ),
    inference(resolution,[status(thm)],[c_372,c_36])).

tff(c_3568,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3543,c_387])).

tff(c_3596,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_90,c_3568])).

tff(c_3598,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_3596])).

tff(c_3599,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_16,plain,(
    ! [A_6] :
      ( k1_relat_1(k2_funct_1(A_6)) = k2_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3720,plain,(
    ! [A_265] :
      ( m1_subset_1(A_265,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_265),k2_relat_1(A_265))))
      | ~ v1_funct_1(A_265)
      | ~ v1_relat_1(A_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_28,plain,(
    ! [C_16,A_14,B_15] :
      ( v4_relat_1(C_16,A_14)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_3840,plain,(
    ! [A_268] :
      ( v4_relat_1(A_268,k1_relat_1(A_268))
      | ~ v1_funct_1(A_268)
      | ~ v1_relat_1(A_268) ) ),
    inference(resolution,[status(thm)],[c_3720,c_28])).

tff(c_3909,plain,(
    ! [A_273] :
      ( v4_relat_1(k2_funct_1(A_273),k2_relat_1(A_273))
      | ~ v1_funct_1(k2_funct_1(A_273))
      | ~ v1_relat_1(k2_funct_1(A_273))
      | ~ v2_funct_1(A_273)
      | ~ v1_funct_1(A_273)
      | ~ v1_relat_1(A_273) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_3840])).

tff(c_3918,plain,
    ( v4_relat_1(k2_funct_1('#skF_4'),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3599,c_3909])).

tff(c_3922,plain,
    ( v4_relat_1(k2_funct_1('#skF_4'),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_90,c_3918])).

tff(c_3955,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3922])).

tff(c_78,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_46,plain,(
    ! [A_38] : k6_relat_1(A_38) = k6_partfun1(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_8,plain,(
    ! [A_2] : v2_funct_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_100,plain,(
    ! [A_2] : v2_funct_1(k6_partfun1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8])).

tff(c_84,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_80,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_58,plain,(
    ! [C_52,B_51,A_50] :
      ( m1_subset_1(k2_funct_1(C_52),k1_zfmisc_1(k2_zfmisc_1(B_51,A_50)))
      | k2_relset_1(A_50,B_51,C_52) != B_51
      | ~ v2_funct_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51)))
      | ~ v1_funct_2(C_52,A_50,B_51)
      | ~ v1_funct_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_4556,plain,(
    ! [A_314,B_311,D_315,F_312,C_313,E_310] :
      ( k1_partfun1(A_314,B_311,C_313,D_315,E_310,F_312) = k5_relat_1(E_310,F_312)
      | ~ m1_subset_1(F_312,k1_zfmisc_1(k2_zfmisc_1(C_313,D_315)))
      | ~ v1_funct_1(F_312)
      | ~ m1_subset_1(E_310,k1_zfmisc_1(k2_zfmisc_1(A_314,B_311)))
      | ~ v1_funct_1(E_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_4572,plain,(
    ! [A_314,B_311,E_310] :
      ( k1_partfun1(A_314,B_311,'#skF_2','#skF_1',E_310,'#skF_4') = k5_relat_1(E_310,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_310,k1_zfmisc_1(k2_zfmisc_1(A_314,B_311)))
      | ~ v1_funct_1(E_310) ) ),
    inference(resolution,[status(thm)],[c_86,c_4556])).

tff(c_5080,plain,(
    ! [A_331,B_332,E_333] :
      ( k1_partfun1(A_331,B_332,'#skF_2','#skF_1',E_333,'#skF_4') = k5_relat_1(E_333,'#skF_4')
      | ~ m1_subset_1(E_333,k1_zfmisc_1(k2_zfmisc_1(A_331,B_332)))
      | ~ v1_funct_1(E_333) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_4572])).

tff(c_5104,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_5080])).

tff(c_5123,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_5104])).

tff(c_3979,plain,(
    ! [D_280,C_281,A_282,B_283] :
      ( D_280 = C_281
      | ~ r2_relset_1(A_282,B_283,C_281,D_280)
      | ~ m1_subset_1(D_280,k1_zfmisc_1(k2_zfmisc_1(A_282,B_283)))
      | ~ m1_subset_1(C_281,k1_zfmisc_1(k2_zfmisc_1(A_282,B_283))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_4010,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_82,c_3979])).

tff(c_4069,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_4010])).

tff(c_5128,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5123,c_4069])).

tff(c_5142,plain,(
    ! [E_339,C_338,A_336,F_337,D_334,B_335] :
      ( m1_subset_1(k1_partfun1(A_336,B_335,C_338,D_334,E_339,F_337),k1_zfmisc_1(k2_zfmisc_1(A_336,D_334)))
      | ~ m1_subset_1(F_337,k1_zfmisc_1(k2_zfmisc_1(C_338,D_334)))
      | ~ v1_funct_1(F_337)
      | ~ m1_subset_1(E_339,k1_zfmisc_1(k2_zfmisc_1(A_336,B_335)))
      | ~ v1_funct_1(E_339) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_5188,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5123,c_5142])).

tff(c_5216,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_92,c_90,c_86,c_5188])).

tff(c_5218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5128,c_5216])).

tff(c_5219,plain,
    ( ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_4010])).

tff(c_5244,plain,(
    ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_5219])).

tff(c_126,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_119])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_funct_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_relat_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_135,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_92,c_128])).

tff(c_166,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_135,c_160])).

tff(c_172,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_166])).

tff(c_3615,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_3639,plain,(
    ! [A_255,B_256,C_257] :
      ( k2_relset_1(A_255,B_256,C_257) = k2_relat_1(C_257)
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(A_255,B_256))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3642,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_3639])).

tff(c_3647,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_3642])).

tff(c_3656,plain,
    ( v2_funct_2('#skF_3',k2_relat_1('#skF_3'))
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3647,c_36])).

tff(c_3662,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_135,c_3647,c_3656])).

tff(c_3664,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3615,c_3662])).

tff(c_3665,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_3915,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3665,c_3909])).

tff(c_3920,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_96,c_80,c_3915])).

tff(c_3923,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3920])).

tff(c_3927,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_3923])).

tff(c_3931,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_96,c_3927])).

tff(c_3932,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_3'))
    | v4_relat_1(k2_funct_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_3920])).

tff(c_3934,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3932])).

tff(c_3937,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_3934])).

tff(c_3941,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_96,c_3937])).

tff(c_3943,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3932])).

tff(c_76,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_5950,plain,(
    ! [A_388,C_389,B_390] :
      ( k6_partfun1(A_388) = k5_relat_1(C_389,k2_funct_1(C_389))
      | k1_xboole_0 = B_390
      | ~ v2_funct_1(C_389)
      | k2_relset_1(A_388,B_390,C_389) != B_390
      | ~ m1_subset_1(C_389,k1_zfmisc_1(k2_zfmisc_1(A_388,B_390)))
      | ~ v1_funct_2(C_389,A_388,B_390)
      | ~ v1_funct_1(C_389) ) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_5962,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_5950])).

tff(c_5981,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_84,c_80,c_5962])).

tff(c_5982,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_5981])).

tff(c_5615,plain,(
    ! [C_377,B_378,A_379] :
      ( m1_subset_1(k2_funct_1(C_377),k1_zfmisc_1(k2_zfmisc_1(B_378,A_379)))
      | k2_relset_1(A_379,B_378,C_377) != B_378
      | ~ v2_funct_1(C_377)
      | ~ m1_subset_1(C_377,k1_zfmisc_1(k2_zfmisc_1(A_379,B_378)))
      | ~ v1_funct_2(C_377,A_379,B_378)
      | ~ v1_funct_1(C_377) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_44,plain,(
    ! [B_33,C_34,E_36,F_37,A_32,D_35] :
      ( k1_partfun1(A_32,B_33,C_34,D_35,E_36,F_37) = k5_relat_1(E_36,F_37)
      | ~ m1_subset_1(F_37,k1_zfmisc_1(k2_zfmisc_1(C_34,D_35)))
      | ~ v1_funct_1(F_37)
      | ~ m1_subset_1(E_36,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | ~ v1_funct_1(E_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_12709,plain,(
    ! [B_587,E_586,A_588,B_590,A_591,C_589] :
      ( k1_partfun1(A_588,B_587,B_590,A_591,E_586,k2_funct_1(C_589)) = k5_relat_1(E_586,k2_funct_1(C_589))
      | ~ v1_funct_1(k2_funct_1(C_589))
      | ~ m1_subset_1(E_586,k1_zfmisc_1(k2_zfmisc_1(A_588,B_587)))
      | ~ v1_funct_1(E_586)
      | k2_relset_1(A_591,B_590,C_589) != B_590
      | ~ v2_funct_1(C_589)
      | ~ m1_subset_1(C_589,k1_zfmisc_1(k2_zfmisc_1(A_591,B_590)))
      | ~ v1_funct_2(C_589,A_591,B_590)
      | ~ v1_funct_1(C_589) ) ),
    inference(resolution,[status(thm)],[c_5615,c_44])).

tff(c_12747,plain,(
    ! [B_590,A_591,C_589] :
      ( k1_partfun1('#skF_1','#skF_2',B_590,A_591,'#skF_3',k2_funct_1(C_589)) = k5_relat_1('#skF_3',k2_funct_1(C_589))
      | ~ v1_funct_1(k2_funct_1(C_589))
      | ~ v1_funct_1('#skF_3')
      | k2_relset_1(A_591,B_590,C_589) != B_590
      | ~ v2_funct_1(C_589)
      | ~ m1_subset_1(C_589,k1_zfmisc_1(k2_zfmisc_1(A_591,B_590)))
      | ~ v1_funct_2(C_589,A_591,B_590)
      | ~ v1_funct_1(C_589) ) ),
    inference(resolution,[status(thm)],[c_92,c_12709])).

tff(c_12980,plain,(
    ! [B_598,A_599,C_600] :
      ( k1_partfun1('#skF_1','#skF_2',B_598,A_599,'#skF_3',k2_funct_1(C_600)) = k5_relat_1('#skF_3',k2_funct_1(C_600))
      | ~ v1_funct_1(k2_funct_1(C_600))
      | k2_relset_1(A_599,B_598,C_600) != B_598
      | ~ v2_funct_1(C_600)
      | ~ m1_subset_1(C_600,k1_zfmisc_1(k2_zfmisc_1(A_599,B_598)))
      | ~ v1_funct_2(C_600,A_599,B_598)
      | ~ v1_funct_1(C_600) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_12747])).

tff(c_13037,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_12980])).

tff(c_13087,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_80,c_84,c_3943,c_5982,c_13037])).

tff(c_40,plain,(
    ! [B_27,D_29,A_26,E_30,F_31,C_28] :
      ( m1_subset_1(k1_partfun1(A_26,B_27,C_28,D_29,E_30,F_31),k1_zfmisc_1(k2_zfmisc_1(A_26,D_29)))
      | ~ m1_subset_1(F_31,k1_zfmisc_1(k2_zfmisc_1(C_28,D_29)))
      | ~ v1_funct_1(F_31)
      | ~ m1_subset_1(E_30,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ v1_funct_1(E_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_13109,plain,
    ( m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13087,c_40])).

tff(c_13126,plain,
    ( m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_92,c_3943,c_13109])).

tff(c_13127,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_5244,c_13126])).

tff(c_13131,plain,
    ( k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_13127])).

tff(c_13135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_92,c_80,c_84,c_13131])).

tff(c_13136,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_5219])).

tff(c_14874,plain,(
    ! [D_674,E_677,A_678,C_675,B_676] :
      ( k1_xboole_0 = C_675
      | v2_funct_1(E_677)
      | k2_relset_1(A_678,B_676,D_674) != B_676
      | ~ v2_funct_1(k1_partfun1(A_678,B_676,B_676,C_675,D_674,E_677))
      | ~ m1_subset_1(E_677,k1_zfmisc_1(k2_zfmisc_1(B_676,C_675)))
      | ~ v1_funct_2(E_677,B_676,C_675)
      | ~ v1_funct_1(E_677)
      | ~ m1_subset_1(D_674,k1_zfmisc_1(k2_zfmisc_1(A_678,B_676)))
      | ~ v1_funct_2(D_674,A_678,B_676)
      | ~ v1_funct_1(D_674) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_14882,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_13136,c_14874])).

tff(c_14893,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_92,c_90,c_88,c_86,c_100,c_84,c_14882])).

tff(c_14895,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3955,c_78,c_14893])).

tff(c_14897,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_3922])).

tff(c_3705,plain,(
    ! [A_262,B_263,C_264] :
      ( k2_relset_1(A_262,B_263,C_264) = k2_relat_1(C_264)
      | ~ m1_subset_1(C_264,k1_zfmisc_1(k2_zfmisc_1(A_262,B_263))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3711,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_3705])).

tff(c_3715,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3599,c_3711])).

tff(c_22,plain,(
    ! [A_8,B_10] :
      ( k2_funct_1(A_8) = B_10
      | k6_relat_1(k2_relat_1(A_8)) != k5_relat_1(B_10,A_8)
      | k2_relat_1(B_10) != k1_relat_1(A_8)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(B_10)
      | ~ v1_relat_1(B_10)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_30526,plain,(
    ! [A_1161,B_1162] :
      ( k2_funct_1(A_1161) = B_1162
      | k6_partfun1(k2_relat_1(A_1161)) != k5_relat_1(B_1162,A_1161)
      | k2_relat_1(B_1162) != k1_relat_1(A_1161)
      | ~ v2_funct_1(A_1161)
      | ~ v1_funct_1(B_1162)
      | ~ v1_relat_1(B_1162)
      | ~ v1_funct_1(A_1161)
      | ~ v1_relat_1(A_1161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_22])).

tff(c_30536,plain,(
    ! [B_1162] :
      ( k2_funct_1('#skF_4') = B_1162
      | k5_relat_1(B_1162,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_1162) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_1162)
      | ~ v1_relat_1(B_1162)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3599,c_30526])).

tff(c_30553,plain,(
    ! [B_1163] :
      ( k2_funct_1('#skF_4') = B_1163
      | k5_relat_1(B_1163,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_1163) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_1163)
      | ~ v1_relat_1(B_1163) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_90,c_14897,c_30536])).

tff(c_30565,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_126,c_30553])).

tff(c_30584,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k1_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_3665,c_30565])).

tff(c_30588,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_30584])).

tff(c_14896,plain,
    ( ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | v4_relat_1(k2_funct_1('#skF_4'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_3922])).

tff(c_14898,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_14896])).

tff(c_14901,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2,c_14898])).

tff(c_14905,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_90,c_14901])).

tff(c_14907,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_14896])).

tff(c_30589,plain,(
    ! [C_1164,B_1165,A_1166] :
      ( v1_funct_2(k2_funct_1(C_1164),B_1165,A_1166)
      | k2_relset_1(A_1166,B_1165,C_1164) != B_1165
      | ~ v2_funct_1(C_1164)
      | ~ m1_subset_1(C_1164,k1_zfmisc_1(k2_zfmisc_1(A_1166,B_1165)))
      | ~ v1_funct_2(C_1164,A_1166,B_1165)
      | ~ v1_funct_1(C_1164) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_30607,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_1','#skF_2')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_30589])).

tff(c_30623,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_14897,c_3715,c_30607])).

tff(c_3933,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3920])).

tff(c_30534,plain,(
    ! [B_1162] :
      ( k2_funct_1('#skF_3') = B_1162
      | k5_relat_1(B_1162,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_1162) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_1162)
      | ~ v1_relat_1(B_1162)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3665,c_30526])).

tff(c_30625,plain,(
    ! [B_1167] :
      ( k2_funct_1('#skF_3') = B_1167
      | k5_relat_1(B_1167,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_1167) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_1167)
      | ~ v1_relat_1(B_1167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_96,c_80,c_30534])).

tff(c_30634,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_127,c_30625])).

tff(c_30653,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_3599,c_30634])).

tff(c_30654,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_30653])).

tff(c_30665,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_30654])).

tff(c_30604,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_30589])).

tff(c_30620,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_80,c_84,c_30604])).

tff(c_15829,plain,(
    ! [E_745,C_744,B_741,D_740,A_742,F_743] :
      ( m1_subset_1(k1_partfun1(A_742,B_741,C_744,D_740,E_745,F_743),k1_zfmisc_1(k2_zfmisc_1(A_742,D_740)))
      | ~ m1_subset_1(F_743,k1_zfmisc_1(k2_zfmisc_1(C_744,D_740)))
      | ~ v1_funct_1(F_743)
      | ~ m1_subset_1(E_745,k1_zfmisc_1(k2_zfmisc_1(A_742,B_741)))
      | ~ v1_funct_1(E_745) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_14941,plain,(
    ! [D_683,C_684,A_685,B_686] :
      ( D_683 = C_684
      | ~ r2_relset_1(A_685,B_686,C_684,D_683)
      | ~ m1_subset_1(D_683,k1_zfmisc_1(k2_zfmisc_1(A_685,B_686)))
      | ~ m1_subset_1(C_684,k1_zfmisc_1(k2_zfmisc_1(A_685,B_686))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_14972,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_82,c_14941])).

tff(c_14974,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_14972])).

tff(c_15861,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_15829,c_14974])).

tff(c_15890,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_92,c_90,c_86,c_15861])).

tff(c_15891,plain,
    ( ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_14972])).

tff(c_15912,plain,(
    ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_15891])).

tff(c_16939,plain,(
    ! [A_813,C_814,B_815] :
      ( k6_partfun1(A_813) = k5_relat_1(C_814,k2_funct_1(C_814))
      | k1_xboole_0 = B_815
      | ~ v2_funct_1(C_814)
      | k2_relset_1(A_813,B_815,C_814) != B_815
      | ~ m1_subset_1(C_814,k1_zfmisc_1(k2_zfmisc_1(A_813,B_815)))
      | ~ v1_funct_2(C_814,A_813,B_815)
      | ~ v1_funct_1(C_814) ) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_16951,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_16939])).

tff(c_16970,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_84,c_80,c_16951])).

tff(c_16971,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_16970])).

tff(c_16607,plain,(
    ! [C_803,B_804,A_805] :
      ( m1_subset_1(k2_funct_1(C_803),k1_zfmisc_1(k2_zfmisc_1(B_804,A_805)))
      | k2_relset_1(A_805,B_804,C_803) != B_804
      | ~ v2_funct_1(C_803)
      | ~ m1_subset_1(C_803,k1_zfmisc_1(k2_zfmisc_1(A_805,B_804)))
      | ~ v1_funct_2(C_803,A_805,B_804)
      | ~ v1_funct_1(C_803) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_28533,plain,(
    ! [C_1069,B_1071,A_1072,A_1074,B_1073,E_1070] :
      ( k1_partfun1(A_1072,B_1071,B_1073,A_1074,E_1070,k2_funct_1(C_1069)) = k5_relat_1(E_1070,k2_funct_1(C_1069))
      | ~ v1_funct_1(k2_funct_1(C_1069))
      | ~ m1_subset_1(E_1070,k1_zfmisc_1(k2_zfmisc_1(A_1072,B_1071)))
      | ~ v1_funct_1(E_1070)
      | k2_relset_1(A_1074,B_1073,C_1069) != B_1073
      | ~ v2_funct_1(C_1069)
      | ~ m1_subset_1(C_1069,k1_zfmisc_1(k2_zfmisc_1(A_1074,B_1073)))
      | ~ v1_funct_2(C_1069,A_1074,B_1073)
      | ~ v1_funct_1(C_1069) ) ),
    inference(resolution,[status(thm)],[c_16607,c_44])).

tff(c_28569,plain,(
    ! [B_1073,A_1074,C_1069] :
      ( k1_partfun1('#skF_1','#skF_2',B_1073,A_1074,'#skF_3',k2_funct_1(C_1069)) = k5_relat_1('#skF_3',k2_funct_1(C_1069))
      | ~ v1_funct_1(k2_funct_1(C_1069))
      | ~ v1_funct_1('#skF_3')
      | k2_relset_1(A_1074,B_1073,C_1069) != B_1073
      | ~ v2_funct_1(C_1069)
      | ~ m1_subset_1(C_1069,k1_zfmisc_1(k2_zfmisc_1(A_1074,B_1073)))
      | ~ v1_funct_2(C_1069,A_1074,B_1073)
      | ~ v1_funct_1(C_1069) ) ),
    inference(resolution,[status(thm)],[c_92,c_28533])).

tff(c_29967,plain,(
    ! [B_1126,A_1127,C_1128] :
      ( k1_partfun1('#skF_1','#skF_2',B_1126,A_1127,'#skF_3',k2_funct_1(C_1128)) = k5_relat_1('#skF_3',k2_funct_1(C_1128))
      | ~ v1_funct_1(k2_funct_1(C_1128))
      | k2_relset_1(A_1127,B_1126,C_1128) != B_1126
      | ~ v2_funct_1(C_1128)
      | ~ m1_subset_1(C_1128,k1_zfmisc_1(k2_zfmisc_1(A_1127,B_1126)))
      | ~ v1_funct_2(C_1128,A_1127,B_1126)
      | ~ v1_funct_1(C_1128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_28569])).

tff(c_30021,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_29967])).

tff(c_30068,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_80,c_84,c_3943,c_16971,c_30021])).

tff(c_30094,plain,
    ( m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30068,c_40])).

tff(c_30115,plain,
    ( m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_92,c_3943,c_30094])).

tff(c_30116,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_15912,c_30115])).

tff(c_30120,plain,
    ( k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_30116])).

tff(c_30124,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_92,c_80,c_84,c_30120])).

tff(c_30126,plain,(
    m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_15891])).

tff(c_32,plain,(
    ! [A_20,B_21,D_23] :
      ( r2_relset_1(A_20,B_21,D_23,D_23)
      | ~ m1_subset_1(D_23,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_30142,plain,(
    r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_30126,c_32])).

tff(c_14,plain,(
    ! [A_6] :
      ( k2_relat_1(k2_funct_1(A_6)) = k1_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_30967,plain,(
    ! [A_1197,C_1198,B_1199] :
      ( k6_partfun1(A_1197) = k5_relat_1(C_1198,k2_funct_1(C_1198))
      | k1_xboole_0 = B_1199
      | ~ v2_funct_1(C_1198)
      | k2_relset_1(A_1197,B_1199,C_1198) != B_1199
      | ~ m1_subset_1(C_1198,k1_zfmisc_1(k2_zfmisc_1(A_1197,B_1199)))
      | ~ v1_funct_2(C_1198,A_1197,B_1199)
      | ~ v1_funct_1(C_1198) ) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_30979,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_30967])).

tff(c_30998,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_84,c_80,c_30979])).

tff(c_30999,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_30998])).

tff(c_10,plain,(
    ! [A_3,B_5] :
      ( v2_funct_1(A_3)
      | k2_relat_1(B_5) != k1_relat_1(A_3)
      | ~ v2_funct_1(k5_relat_1(B_5,A_3))
      | ~ v1_funct_1(B_5)
      | ~ v1_relat_1(B_5)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_31007,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_30999,c_10])).

tff(c_31020,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3933,c_3943,c_126,c_96,c_100,c_3665,c_31007])).

tff(c_31074,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_31020])).

tff(c_31077,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_31074])).

tff(c_31080,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_96,c_80,c_3665,c_31077])).

tff(c_31082,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_31020])).

tff(c_68,plain,(
    ! [A_56] :
      ( m1_subset_1(A_56,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_56),k2_relat_1(A_56))))
      | ~ v1_funct_1(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_31150,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3')))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_31082,c_68])).

tff(c_31181,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3933,c_3943,c_31150])).

tff(c_31683,plain,(
    v5_relat_1(k2_funct_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_31181,c_26])).

tff(c_31694,plain,
    ( v2_funct_2(k2_funct_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_31683,c_36])).

tff(c_31704,plain,(
    v2_funct_2(k2_funct_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3933,c_31694])).

tff(c_31715,plain,
    ( v2_funct_2(k2_funct_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_31704])).

tff(c_31717,plain,(
    v2_funct_2(k2_funct_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_96,c_80,c_31715])).

tff(c_31697,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_31683])).

tff(c_31706,plain,(
    v5_relat_1(k2_funct_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_96,c_80,c_31697])).

tff(c_38,plain,(
    ! [B_25,A_24] :
      ( k2_relat_1(B_25) = A_24
      | ~ v2_funct_2(B_25,A_24)
      | ~ v5_relat_1(B_25,A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_31709,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v2_funct_2(k2_funct_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_31706,c_38])).

tff(c_31712,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v2_funct_2(k2_funct_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3933,c_31709])).

tff(c_32739,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31717,c_31712])).

tff(c_30737,plain,(
    ! [C_1177,B_1178,A_1179] :
      ( m1_subset_1(k2_funct_1(C_1177),k1_zfmisc_1(k2_zfmisc_1(B_1178,A_1179)))
      | k2_relset_1(A_1179,B_1178,C_1177) != B_1178
      | ~ v2_funct_1(C_1177)
      | ~ m1_subset_1(C_1177,k1_zfmisc_1(k2_zfmisc_1(A_1179,B_1178)))
      | ~ v1_funct_2(C_1177,A_1179,B_1178)
      | ~ v1_funct_1(C_1177) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_30,plain,(
    ! [A_17,B_18,C_19] :
      ( k2_relset_1(A_17,B_18,C_19) = k2_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_37740,plain,(
    ! [B_1363,A_1364,C_1365] :
      ( k2_relset_1(B_1363,A_1364,k2_funct_1(C_1365)) = k2_relat_1(k2_funct_1(C_1365))
      | k2_relset_1(A_1364,B_1363,C_1365) != B_1363
      | ~ v2_funct_1(C_1365)
      | ~ m1_subset_1(C_1365,k1_zfmisc_1(k2_zfmisc_1(A_1364,B_1363)))
      | ~ v1_funct_2(C_1365,A_1364,B_1363)
      | ~ v1_funct_1(C_1365) ) ),
    inference(resolution,[status(thm)],[c_30737,c_30])).

tff(c_37797,plain,
    ( k2_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_37740])).

tff(c_37847,plain,(
    k2_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_80,c_84,c_32739,c_37797])).

tff(c_30847,plain,(
    ! [D_1190,C_1188,E_1185,F_1187,A_1189,B_1186] :
      ( k1_partfun1(A_1189,B_1186,C_1188,D_1190,E_1185,F_1187) = k5_relat_1(E_1185,F_1187)
      | ~ m1_subset_1(F_1187,k1_zfmisc_1(k2_zfmisc_1(C_1188,D_1190)))
      | ~ v1_funct_1(F_1187)
      | ~ m1_subset_1(E_1185,k1_zfmisc_1(k2_zfmisc_1(A_1189,B_1186)))
      | ~ v1_funct_1(E_1185) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_39453,plain,(
    ! [C_1401,A_1399,B_1402,B_1400,E_1398,A_1403] :
      ( k1_partfun1(A_1403,B_1400,B_1402,A_1399,E_1398,k2_funct_1(C_1401)) = k5_relat_1(E_1398,k2_funct_1(C_1401))
      | ~ v1_funct_1(k2_funct_1(C_1401))
      | ~ m1_subset_1(E_1398,k1_zfmisc_1(k2_zfmisc_1(A_1403,B_1400)))
      | ~ v1_funct_1(E_1398)
      | k2_relset_1(A_1399,B_1402,C_1401) != B_1402
      | ~ v2_funct_1(C_1401)
      | ~ m1_subset_1(C_1401,k1_zfmisc_1(k2_zfmisc_1(A_1399,B_1402)))
      | ~ v1_funct_2(C_1401,A_1399,B_1402)
      | ~ v1_funct_1(C_1401) ) ),
    inference(resolution,[status(thm)],[c_58,c_30847])).

tff(c_39491,plain,(
    ! [B_1402,A_1399,C_1401] :
      ( k1_partfun1('#skF_1','#skF_2',B_1402,A_1399,'#skF_3',k2_funct_1(C_1401)) = k5_relat_1('#skF_3',k2_funct_1(C_1401))
      | ~ v1_funct_1(k2_funct_1(C_1401))
      | ~ v1_funct_1('#skF_3')
      | k2_relset_1(A_1399,B_1402,C_1401) != B_1402
      | ~ v2_funct_1(C_1401)
      | ~ m1_subset_1(C_1401,k1_zfmisc_1(k2_zfmisc_1(A_1399,B_1402)))
      | ~ v1_funct_2(C_1401,A_1399,B_1402)
      | ~ v1_funct_1(C_1401) ) ),
    inference(resolution,[status(thm)],[c_92,c_39453])).

tff(c_53967,plain,(
    ! [B_1587,A_1588,C_1589] :
      ( k1_partfun1('#skF_1','#skF_2',B_1587,A_1588,'#skF_3',k2_funct_1(C_1589)) = k5_relat_1('#skF_3',k2_funct_1(C_1589))
      | ~ v1_funct_1(k2_funct_1(C_1589))
      | k2_relset_1(A_1588,B_1587,C_1589) != B_1587
      | ~ v2_funct_1(C_1589)
      | ~ m1_subset_1(C_1589,k1_zfmisc_1(k2_zfmisc_1(A_1588,B_1587)))
      | ~ v1_funct_2(C_1589,A_1588,B_1587)
      | ~ v1_funct_1(C_1589) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_39491])).

tff(c_54084,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_53967])).

tff(c_54192,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_80,c_84,c_3943,c_30999,c_54084])).

tff(c_48,plain,(
    ! [A_39,B_40,C_41,D_43] :
      ( k2_relset_1(A_39,B_40,C_41) = B_40
      | ~ r2_relset_1(B_40,B_40,k1_partfun1(B_40,A_39,A_39,B_40,D_43,C_41),k6_partfun1(B_40))
      | ~ m1_subset_1(D_43,k1_zfmisc_1(k2_zfmisc_1(B_40,A_39)))
      | ~ v1_funct_2(D_43,B_40,A_39)
      | ~ v1_funct_1(D_43)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40)))
      | ~ v1_funct_2(C_41,A_39,B_40)
      | ~ v1_funct_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_54228,plain,
    ( k2_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_54192,c_48])).

tff(c_54262,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3943,c_30620,c_96,c_94,c_92,c_30142,c_37847,c_54228])).

tff(c_54263,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_30665,c_54262])).

tff(c_54272,plain,
    ( k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_54263])).

tff(c_54276,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_92,c_80,c_84,c_54272])).

tff(c_54278,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_30654])).

tff(c_3817,plain,(
    ! [A_267] :
      ( v5_relat_1(A_267,k2_relat_1(A_267))
      | ~ v1_funct_1(A_267)
      | ~ v1_relat_1(A_267) ) ),
    inference(resolution,[status(thm)],[c_3720,c_26])).

tff(c_3844,plain,(
    ! [A_269] :
      ( v2_funct_2(A_269,k2_relat_1(A_269))
      | ~ v1_funct_1(A_269)
      | ~ v1_relat_1(A_269) ) ),
    inference(resolution,[status(thm)],[c_3817,c_36])).

tff(c_3847,plain,(
    ! [A_6] :
      ( v2_funct_2(k2_funct_1(A_6),k1_relat_1(A_6))
      | ~ v1_funct_1(k2_funct_1(A_6))
      | ~ v1_relat_1(k2_funct_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_3844])).

tff(c_54299,plain,
    ( v2_funct_2(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_54278,c_3847])).

tff(c_54323,plain,(
    v2_funct_2(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_96,c_80,c_3933,c_3943,c_54299])).

tff(c_3826,plain,(
    ! [A_6] :
      ( v5_relat_1(k2_funct_1(A_6),k1_relat_1(A_6))
      | ~ v1_funct_1(k2_funct_1(A_6))
      | ~ v1_relat_1(k2_funct_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_3817])).

tff(c_54302,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_54278,c_3826])).

tff(c_54325,plain,(
    v5_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_96,c_80,c_3933,c_3943,c_54302])).

tff(c_54339,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_54325,c_38])).

tff(c_54342,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3933,c_54323,c_54339])).

tff(c_54372,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_54342,c_68])).

tff(c_54404,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3933,c_3943,c_54372])).

tff(c_54481,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_54404])).

tff(c_54500,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_96,c_80,c_3665,c_54481])).

tff(c_54915,plain,(
    ! [B_1614,C_1615,A_1616] :
      ( k6_partfun1(B_1614) = k5_relat_1(k2_funct_1(C_1615),C_1615)
      | k1_xboole_0 = B_1614
      | ~ v2_funct_1(C_1615)
      | k2_relset_1(A_1616,B_1614,C_1615) != B_1614
      | ~ m1_subset_1(C_1615,k1_zfmisc_1(k2_zfmisc_1(A_1616,B_1614)))
      | ~ v1_funct_2(C_1615,A_1616,B_1614)
      | ~ v1_funct_1(C_1615) ) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_54929,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_54915])).

tff(c_54952,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_84,c_80,c_54929])).

tff(c_54953,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_54952])).

tff(c_54660,plain,(
    ! [F_1604,B_1603,D_1607,E_1602,C_1605,A_1606] :
      ( k1_partfun1(A_1606,B_1603,C_1605,D_1607,E_1602,F_1604) = k5_relat_1(E_1602,F_1604)
      | ~ m1_subset_1(F_1604,k1_zfmisc_1(k2_zfmisc_1(C_1605,D_1607)))
      | ~ v1_funct_1(F_1604)
      | ~ m1_subset_1(E_1602,k1_zfmisc_1(k2_zfmisc_1(A_1606,B_1603)))
      | ~ v1_funct_1(E_1602) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_54674,plain,(
    ! [A_1606,B_1603,E_1602] :
      ( k1_partfun1(A_1606,B_1603,'#skF_1','#skF_2',E_1602,'#skF_3') = k5_relat_1(E_1602,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_1602,k1_zfmisc_1(k2_zfmisc_1(A_1606,B_1603)))
      | ~ v1_funct_1(E_1602) ) ),
    inference(resolution,[status(thm)],[c_92,c_54660])).

tff(c_55850,plain,(
    ! [A_1648,B_1649,E_1650] :
      ( k1_partfun1(A_1648,B_1649,'#skF_1','#skF_2',E_1650,'#skF_3') = k5_relat_1(E_1650,'#skF_3')
      | ~ m1_subset_1(E_1650,k1_zfmisc_1(k2_zfmisc_1(A_1648,B_1649)))
      | ~ v1_funct_1(E_1650) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_54674])).

tff(c_55871,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_54500,c_55850])).

tff(c_55906,plain,(
    k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3943,c_54953,c_55871])).

tff(c_56307,plain,
    ( m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_55906,c_40])).

tff(c_56319,plain,(
    m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3943,c_54500,c_96,c_92,c_56307])).

tff(c_56394,plain,(
    r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_56319,c_32])).

tff(c_14906,plain,
    ( ~ v1_relat_1(k2_funct_1('#skF_4'))
    | v4_relat_1(k2_funct_1('#skF_4'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_14896])).

tff(c_14908,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_14906])).

tff(c_14911,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_14908])).

tff(c_14915,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_90,c_14911])).

tff(c_14917,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_14906])).

tff(c_54744,plain,(
    ! [A_1611,C_1612,B_1613] :
      ( k6_partfun1(A_1611) = k5_relat_1(C_1612,k2_funct_1(C_1612))
      | k1_xboole_0 = B_1613
      | ~ v2_funct_1(C_1612)
      | k2_relset_1(A_1611,B_1613,C_1612) != B_1613
      | ~ m1_subset_1(C_1612,k1_zfmisc_1(k2_zfmisc_1(A_1611,B_1613)))
      | ~ v1_funct_2(C_1612,A_1611,B_1613)
      | ~ v1_funct_1(C_1612) ) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_54760,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_54744])).

tff(c_54785,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_3715,c_14897,c_54760])).

tff(c_54786,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_54785])).

tff(c_54814,plain,
    ( v2_funct_1(k2_funct_1('#skF_4'))
    | k1_relat_1(k2_funct_1('#skF_4')) != k2_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_54786,c_10])).

tff(c_54827,plain,
    ( v2_funct_1(k2_funct_1('#skF_4'))
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14917,c_14907,c_127,c_90,c_100,c_3599,c_54814])).

tff(c_54847,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_54827])).

tff(c_54850,plain,
    ( k2_relat_1('#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_54847])).

tff(c_54853,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_90,c_14897,c_3599,c_54850])).

tff(c_54855,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_54827])).

tff(c_54880,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1',k2_relat_1(k2_funct_1('#skF_4')))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_54855,c_68])).

tff(c_54907,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1',k2_relat_1(k2_funct_1('#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14917,c_14907,c_54880])).

tff(c_55223,plain,(
    v5_relat_1(k2_funct_1('#skF_4'),k2_relat_1(k2_funct_1('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_54907,c_26])).

tff(c_55233,plain,
    ( v2_funct_2(k2_funct_1('#skF_4'),k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_55223,c_36])).

tff(c_55243,plain,(
    v2_funct_2(k2_funct_1('#skF_4'),k2_relat_1(k2_funct_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14917,c_55233])).

tff(c_55255,plain,
    ( v2_funct_2(k2_funct_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_55243])).

tff(c_55257,plain,(
    v2_funct_2(k2_funct_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_90,c_14897,c_55255])).

tff(c_55236,plain,
    ( v5_relat_1(k2_funct_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_55223])).

tff(c_55245,plain,(
    v5_relat_1(k2_funct_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_90,c_14897,c_55236])).

tff(c_55249,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4')
    | ~ v2_funct_2(k2_funct_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_55245,c_38])).

tff(c_55252,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4')
    | ~ v2_funct_2(k2_funct_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14917,c_55249])).

tff(c_55528,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55257,c_55252])).

tff(c_54603,plain,(
    ! [C_1599,B_1600,A_1601] :
      ( m1_subset_1(k2_funct_1(C_1599),k1_zfmisc_1(k2_zfmisc_1(B_1600,A_1601)))
      | k2_relset_1(A_1601,B_1600,C_1599) != B_1600
      | ~ v2_funct_1(C_1599)
      | ~ m1_subset_1(C_1599,k1_zfmisc_1(k2_zfmisc_1(A_1601,B_1600)))
      | ~ v1_funct_2(C_1599,A_1601,B_1600)
      | ~ v1_funct_1(C_1599) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_60334,plain,(
    ! [B_1743,A_1744,C_1745] :
      ( k2_relset_1(B_1743,A_1744,k2_funct_1(C_1745)) = k2_relat_1(k2_funct_1(C_1745))
      | k2_relset_1(A_1744,B_1743,C_1745) != B_1743
      | ~ v2_funct_1(C_1745)
      | ~ m1_subset_1(C_1745,k1_zfmisc_1(k2_zfmisc_1(A_1744,B_1743)))
      | ~ v1_funct_2(C_1745,A_1744,B_1743)
      | ~ v1_funct_1(C_1745) ) ),
    inference(resolution,[status(thm)],[c_54603,c_30])).

tff(c_60394,plain,
    ( k2_relset_1('#skF_1','#skF_2',k2_funct_1('#skF_4')) = k2_relat_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_60334])).

tff(c_60444,plain,(
    k2_relset_1('#skF_1','#skF_2',k2_funct_1('#skF_4')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_14897,c_3715,c_55528,c_60394])).

tff(c_62429,plain,(
    ! [A_1792,A_1788,B_1789,B_1791,C_1790,E_1787] :
      ( k1_partfun1(A_1792,B_1789,B_1791,A_1788,E_1787,k2_funct_1(C_1790)) = k5_relat_1(E_1787,k2_funct_1(C_1790))
      | ~ v1_funct_1(k2_funct_1(C_1790))
      | ~ m1_subset_1(E_1787,k1_zfmisc_1(k2_zfmisc_1(A_1792,B_1789)))
      | ~ v1_funct_1(E_1787)
      | k2_relset_1(A_1788,B_1791,C_1790) != B_1791
      | ~ v2_funct_1(C_1790)
      | ~ m1_subset_1(C_1790,k1_zfmisc_1(k2_zfmisc_1(A_1788,B_1791)))
      | ~ v1_funct_2(C_1790,A_1788,B_1791)
      | ~ v1_funct_1(C_1790) ) ),
    inference(resolution,[status(thm)],[c_58,c_54660])).

tff(c_62469,plain,(
    ! [B_1791,A_1788,C_1790] :
      ( k1_partfun1('#skF_2','#skF_1',B_1791,A_1788,'#skF_4',k2_funct_1(C_1790)) = k5_relat_1('#skF_4',k2_funct_1(C_1790))
      | ~ v1_funct_1(k2_funct_1(C_1790))
      | ~ v1_funct_1('#skF_4')
      | k2_relset_1(A_1788,B_1791,C_1790) != B_1791
      | ~ v2_funct_1(C_1790)
      | ~ m1_subset_1(C_1790,k1_zfmisc_1(k2_zfmisc_1(A_1788,B_1791)))
      | ~ v1_funct_2(C_1790,A_1788,B_1791)
      | ~ v1_funct_1(C_1790) ) ),
    inference(resolution,[status(thm)],[c_86,c_62429])).

tff(c_77811,plain,(
    ! [B_1984,A_1985,C_1986] :
      ( k1_partfun1('#skF_2','#skF_1',B_1984,A_1985,'#skF_4',k2_funct_1(C_1986)) = k5_relat_1('#skF_4',k2_funct_1(C_1986))
      | ~ v1_funct_1(k2_funct_1(C_1986))
      | k2_relset_1(A_1985,B_1984,C_1986) != B_1984
      | ~ v2_funct_1(C_1986)
      | ~ m1_subset_1(C_1986,k1_zfmisc_1(k2_zfmisc_1(A_1985,B_1984)))
      | ~ v1_funct_2(C_1986,A_1985,B_1984)
      | ~ v1_funct_1(C_1986) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_62469])).

tff(c_77937,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4',k2_funct_1('#skF_4')) = k5_relat_1('#skF_4',k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_77811])).

tff(c_78051,plain,(
    k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_14897,c_3715,c_14907,c_54786,c_77937])).

tff(c_78084,plain,
    ( k2_relset_1('#skF_1','#skF_2',k2_funct_1('#skF_4')) = '#skF_2'
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_1','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_78051,c_48])).

tff(c_78118,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14907,c_30623,c_90,c_88,c_86,c_56394,c_60444,c_78084])).

tff(c_78119,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_30588,c_78118])).

tff(c_78128,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_78119])).

tff(c_78132,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_14897,c_3715,c_78128])).

tff(c_78133,plain,
    ( k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30584])).

tff(c_78192,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_78133])).

tff(c_30125,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_15891])).

tff(c_78529,plain,(
    ! [C_2005,F_2004,D_2007,B_2003,E_2002,A_2006] :
      ( k1_partfun1(A_2006,B_2003,C_2005,D_2007,E_2002,F_2004) = k5_relat_1(E_2002,F_2004)
      | ~ m1_subset_1(F_2004,k1_zfmisc_1(k2_zfmisc_1(C_2005,D_2007)))
      | ~ v1_funct_1(F_2004)
      | ~ m1_subset_1(E_2002,k1_zfmisc_1(k2_zfmisc_1(A_2006,B_2003)))
      | ~ v1_funct_1(E_2002) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_78543,plain,(
    ! [A_2006,B_2003,E_2002] :
      ( k1_partfun1(A_2006,B_2003,'#skF_2','#skF_1',E_2002,'#skF_4') = k5_relat_1(E_2002,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_2002,k1_zfmisc_1(k2_zfmisc_1(A_2006,B_2003)))
      | ~ v1_funct_1(E_2002) ) ),
    inference(resolution,[status(thm)],[c_86,c_78529])).

tff(c_79739,plain,(
    ! [A_2048,B_2049,E_2050] :
      ( k1_partfun1(A_2048,B_2049,'#skF_2','#skF_1',E_2050,'#skF_4') = k5_relat_1(E_2050,'#skF_4')
      | ~ m1_subset_1(E_2050,k1_zfmisc_1(k2_zfmisc_1(A_2048,B_2049)))
      | ~ v1_funct_1(E_2050) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_78543])).

tff(c_79781,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_79739])).

tff(c_79820,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_30125,c_79781])).

tff(c_79822,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78192,c_79820])).

tff(c_79823,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_78133])).

tff(c_79872,plain,
    ( k2_relat_1('#skF_4') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_79823,c_16])).

tff(c_79906,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_90,c_14897,c_3599,c_79872])).

tff(c_78134,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_30584])).

tff(c_20,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,k2_funct_1(A_7)) = k6_relat_1(k1_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_98,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,k2_funct_1(A_7)) = k6_partfun1(k1_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_20])).

tff(c_85654,plain,(
    ! [A_2201] :
      ( k2_funct_1(k2_funct_1(A_2201)) = A_2201
      | k6_partfun1(k2_relat_1(k2_funct_1(A_2201))) != k6_partfun1(k1_relat_1(A_2201))
      | k1_relat_1(k2_funct_1(A_2201)) != k2_relat_1(A_2201)
      | ~ v2_funct_1(k2_funct_1(A_2201))
      | ~ v1_funct_1(A_2201)
      | ~ v1_relat_1(A_2201)
      | ~ v1_funct_1(k2_funct_1(A_2201))
      | ~ v1_relat_1(k2_funct_1(A_2201))
      | ~ v2_funct_1(A_2201)
      | ~ v1_funct_1(A_2201)
      | ~ v1_relat_1(A_2201) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_30526])).

tff(c_85663,plain,
    ( k2_funct_1(k2_funct_1('#skF_4')) = '#skF_4'
    | k6_partfun1(k2_relat_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_4'))
    | k1_relat_1(k2_funct_1('#skF_4')) != k2_relat_1('#skF_4')
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_79823,c_85654])).

tff(c_85672,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_90,c_14897,c_126,c_79823,c_96,c_79823,c_127,c_90,c_80,c_79823,c_3599,c_79906,c_79823,c_3665,c_78134,c_79823,c_85663])).

tff(c_85674,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_85672])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:48:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 34.63/25.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 34.75/25.13  
% 34.75/25.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 34.75/25.14  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 34.75/25.14  
% 34.75/25.14  %Foreground sorts:
% 34.75/25.14  
% 34.75/25.14  
% 34.75/25.14  %Background operators:
% 34.75/25.14  
% 34.75/25.14  
% 34.75/25.14  %Foreground operators:
% 34.75/25.14  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 34.75/25.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 34.75/25.14  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 34.75/25.14  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 34.75/25.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 34.75/25.14  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 34.75/25.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 34.75/25.14  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 34.75/25.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 34.75/25.14  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 34.75/25.14  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 34.75/25.14  tff('#skF_2', type, '#skF_2': $i).
% 34.75/25.14  tff('#skF_3', type, '#skF_3': $i).
% 34.75/25.14  tff('#skF_1', type, '#skF_1': $i).
% 34.75/25.14  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 34.75/25.14  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 34.75/25.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 34.75/25.14  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 34.75/25.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 34.75/25.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 34.75/25.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 34.75/25.14  tff('#skF_4', type, '#skF_4': $i).
% 34.75/25.14  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 34.75/25.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 34.75/25.14  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 34.75/25.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 34.75/25.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 34.75/25.14  
% 34.75/25.18  tff(f_256, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 34.75/25.18  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 34.75/25.18  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 34.75/25.18  tff(f_121, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 34.75/25.18  tff(f_143, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 34.75/25.18  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 34.75/25.18  tff(f_162, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 34.75/25.18  tff(f_230, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 34.75/25.18  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 34.75/25.18  tff(f_145, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 34.75/25.18  tff(f_37, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 34.75/25.18  tff(f_204, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 34.75/25.18  tff(f_113, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 34.75/25.18  tff(f_133, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 34.75/25.18  tff(f_33, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 34.75/25.18  tff(f_220, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 34.75/25.18  tff(f_188, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 34.75/25.18  tff(f_91, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 34.75/25.18  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 34.75/25.18  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 34.75/25.18  tff(c_74, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_256])).
% 34.75/25.18  tff(c_86, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_256])).
% 34.75/25.18  tff(c_119, plain, (![C_63, A_64, B_65]: (v1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 34.75/25.18  tff(c_127, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_86, c_119])).
% 34.75/25.18  tff(c_90, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_256])).
% 34.75/25.18  tff(c_128, plain, (![C_66, B_67, A_68]: (v5_relat_1(C_66, B_67) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_68, B_67))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 34.75/25.18  tff(c_136, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_86, c_128])).
% 34.75/25.18  tff(c_160, plain, (![B_75, A_76]: (k2_relat_1(B_75)=A_76 | ~v2_funct_2(B_75, A_76) | ~v5_relat_1(B_75, A_76) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_121])).
% 34.75/25.18  tff(c_163, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_136, c_160])).
% 34.75/25.18  tff(c_169, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_163])).
% 34.75/25.18  tff(c_173, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_169])).
% 34.75/25.18  tff(c_88, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_256])).
% 34.75/25.18  tff(c_96, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_256])).
% 34.75/25.18  tff(c_94, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_256])).
% 34.75/25.18  tff(c_92, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_256])).
% 34.75/25.18  tff(c_2432, plain, (![C_215, D_217, F_214, E_212, A_216, B_213]: (k1_partfun1(A_216, B_213, C_215, D_217, E_212, F_214)=k5_relat_1(E_212, F_214) | ~m1_subset_1(F_214, k1_zfmisc_1(k2_zfmisc_1(C_215, D_217))) | ~v1_funct_1(F_214) | ~m1_subset_1(E_212, k1_zfmisc_1(k2_zfmisc_1(A_216, B_213))) | ~v1_funct_1(E_212))), inference(cnfTransformation, [status(thm)], [f_143])).
% 34.75/25.18  tff(c_2450, plain, (![A_216, B_213, E_212]: (k1_partfun1(A_216, B_213, '#skF_2', '#skF_1', E_212, '#skF_4')=k5_relat_1(E_212, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_212, k1_zfmisc_1(k2_zfmisc_1(A_216, B_213))) | ~v1_funct_1(E_212))), inference(resolution, [status(thm)], [c_86, c_2432])).
% 34.75/25.18  tff(c_2752, plain, (![A_224, B_225, E_226]: (k1_partfun1(A_224, B_225, '#skF_2', '#skF_1', E_226, '#skF_4')=k5_relat_1(E_226, '#skF_4') | ~m1_subset_1(E_226, k1_zfmisc_1(k2_zfmisc_1(A_224, B_225))) | ~v1_funct_1(E_226))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_2450])).
% 34.75/25.18  tff(c_2779, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_2752])).
% 34.75/25.18  tff(c_2801, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_2779])).
% 34.75/25.18  tff(c_82, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_256])).
% 34.75/25.18  tff(c_2813, plain, (r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2801, c_82])).
% 34.75/25.18  tff(c_292, plain, (![A_89, B_90, C_91]: (k2_relset_1(A_89, B_90, C_91)=k2_relat_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 34.75/25.18  tff(c_301, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_86, c_292])).
% 34.75/25.18  tff(c_3532, plain, (![A_247, B_248, C_249, D_250]: (k2_relset_1(A_247, B_248, C_249)=B_248 | ~r2_relset_1(B_248, B_248, k1_partfun1(B_248, A_247, A_247, B_248, D_250, C_249), k6_partfun1(B_248)) | ~m1_subset_1(D_250, k1_zfmisc_1(k2_zfmisc_1(B_248, A_247))) | ~v1_funct_2(D_250, B_248, A_247) | ~v1_funct_1(D_250) | ~m1_subset_1(C_249, k1_zfmisc_1(k2_zfmisc_1(A_247, B_248))) | ~v1_funct_2(C_249, A_247, B_248) | ~v1_funct_1(C_249))), inference(cnfTransformation, [status(thm)], [f_162])).
% 34.75/25.18  tff(c_3538, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_4'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2801, c_3532])).
% 34.75/25.18  tff(c_3543, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_96, c_94, c_92, c_2813, c_301, c_3538])).
% 34.75/25.18  tff(c_306, plain, (![A_92]: (m1_subset_1(A_92, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_92), k2_relat_1(A_92)))) | ~v1_funct_1(A_92) | ~v1_relat_1(A_92))), inference(cnfTransformation, [status(thm)], [f_230])).
% 34.75/25.18  tff(c_26, plain, (![C_16, B_15, A_14]: (v5_relat_1(C_16, B_15) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 34.75/25.18  tff(c_372, plain, (![A_94]: (v5_relat_1(A_94, k2_relat_1(A_94)) | ~v1_funct_1(A_94) | ~v1_relat_1(A_94))), inference(resolution, [status(thm)], [c_306, c_26])).
% 34.75/25.18  tff(c_36, plain, (![B_25]: (v2_funct_2(B_25, k2_relat_1(B_25)) | ~v5_relat_1(B_25, k2_relat_1(B_25)) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_121])).
% 34.75/25.18  tff(c_387, plain, (![A_94]: (v2_funct_2(A_94, k2_relat_1(A_94)) | ~v1_funct_1(A_94) | ~v1_relat_1(A_94))), inference(resolution, [status(thm)], [c_372, c_36])).
% 34.75/25.18  tff(c_3568, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3543, c_387])).
% 34.75/25.18  tff(c_3596, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_90, c_3568])).
% 34.75/25.18  tff(c_3598, plain, $false, inference(negUnitSimplification, [status(thm)], [c_173, c_3596])).
% 34.75/25.18  tff(c_3599, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_169])).
% 34.75/25.18  tff(c_16, plain, (![A_6]: (k1_relat_1(k2_funct_1(A_6))=k2_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_64])).
% 34.75/25.18  tff(c_3720, plain, (![A_265]: (m1_subset_1(A_265, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_265), k2_relat_1(A_265)))) | ~v1_funct_1(A_265) | ~v1_relat_1(A_265))), inference(cnfTransformation, [status(thm)], [f_230])).
% 34.75/25.18  tff(c_28, plain, (![C_16, A_14, B_15]: (v4_relat_1(C_16, A_14) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 34.75/25.18  tff(c_3840, plain, (![A_268]: (v4_relat_1(A_268, k1_relat_1(A_268)) | ~v1_funct_1(A_268) | ~v1_relat_1(A_268))), inference(resolution, [status(thm)], [c_3720, c_28])).
% 34.75/25.18  tff(c_3909, plain, (![A_273]: (v4_relat_1(k2_funct_1(A_273), k2_relat_1(A_273)) | ~v1_funct_1(k2_funct_1(A_273)) | ~v1_relat_1(k2_funct_1(A_273)) | ~v2_funct_1(A_273) | ~v1_funct_1(A_273) | ~v1_relat_1(A_273))), inference(superposition, [status(thm), theory('equality')], [c_16, c_3840])).
% 34.75/25.18  tff(c_3918, plain, (v4_relat_1(k2_funct_1('#skF_4'), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3599, c_3909])).
% 34.75/25.18  tff(c_3922, plain, (v4_relat_1(k2_funct_1('#skF_4'), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_90, c_3918])).
% 34.75/25.18  tff(c_3955, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_3922])).
% 34.75/25.18  tff(c_78, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_256])).
% 34.75/25.18  tff(c_46, plain, (![A_38]: (k6_relat_1(A_38)=k6_partfun1(A_38))), inference(cnfTransformation, [status(thm)], [f_145])).
% 34.75/25.18  tff(c_8, plain, (![A_2]: (v2_funct_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 34.75/25.18  tff(c_100, plain, (![A_2]: (v2_funct_1(k6_partfun1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8])).
% 34.75/25.18  tff(c_84, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_256])).
% 34.75/25.18  tff(c_80, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_256])).
% 34.75/25.18  tff(c_58, plain, (![C_52, B_51, A_50]: (m1_subset_1(k2_funct_1(C_52), k1_zfmisc_1(k2_zfmisc_1(B_51, A_50))) | k2_relset_1(A_50, B_51, C_52)!=B_51 | ~v2_funct_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))) | ~v1_funct_2(C_52, A_50, B_51) | ~v1_funct_1(C_52))), inference(cnfTransformation, [status(thm)], [f_204])).
% 34.75/25.18  tff(c_4556, plain, (![A_314, B_311, D_315, F_312, C_313, E_310]: (k1_partfun1(A_314, B_311, C_313, D_315, E_310, F_312)=k5_relat_1(E_310, F_312) | ~m1_subset_1(F_312, k1_zfmisc_1(k2_zfmisc_1(C_313, D_315))) | ~v1_funct_1(F_312) | ~m1_subset_1(E_310, k1_zfmisc_1(k2_zfmisc_1(A_314, B_311))) | ~v1_funct_1(E_310))), inference(cnfTransformation, [status(thm)], [f_143])).
% 34.75/25.18  tff(c_4572, plain, (![A_314, B_311, E_310]: (k1_partfun1(A_314, B_311, '#skF_2', '#skF_1', E_310, '#skF_4')=k5_relat_1(E_310, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_310, k1_zfmisc_1(k2_zfmisc_1(A_314, B_311))) | ~v1_funct_1(E_310))), inference(resolution, [status(thm)], [c_86, c_4556])).
% 34.75/25.18  tff(c_5080, plain, (![A_331, B_332, E_333]: (k1_partfun1(A_331, B_332, '#skF_2', '#skF_1', E_333, '#skF_4')=k5_relat_1(E_333, '#skF_4') | ~m1_subset_1(E_333, k1_zfmisc_1(k2_zfmisc_1(A_331, B_332))) | ~v1_funct_1(E_333))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_4572])).
% 34.75/25.18  tff(c_5104, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_5080])).
% 34.75/25.18  tff(c_5123, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_5104])).
% 34.75/25.18  tff(c_3979, plain, (![D_280, C_281, A_282, B_283]: (D_280=C_281 | ~r2_relset_1(A_282, B_283, C_281, D_280) | ~m1_subset_1(D_280, k1_zfmisc_1(k2_zfmisc_1(A_282, B_283))) | ~m1_subset_1(C_281, k1_zfmisc_1(k2_zfmisc_1(A_282, B_283))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 34.75/25.18  tff(c_4010, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_82, c_3979])).
% 34.75/25.18  tff(c_4069, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_4010])).
% 34.75/25.18  tff(c_5128, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_5123, c_4069])).
% 34.75/25.18  tff(c_5142, plain, (![E_339, C_338, A_336, F_337, D_334, B_335]: (m1_subset_1(k1_partfun1(A_336, B_335, C_338, D_334, E_339, F_337), k1_zfmisc_1(k2_zfmisc_1(A_336, D_334))) | ~m1_subset_1(F_337, k1_zfmisc_1(k2_zfmisc_1(C_338, D_334))) | ~v1_funct_1(F_337) | ~m1_subset_1(E_339, k1_zfmisc_1(k2_zfmisc_1(A_336, B_335))) | ~v1_funct_1(E_339))), inference(cnfTransformation, [status(thm)], [f_133])).
% 34.75/25.18  tff(c_5188, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5123, c_5142])).
% 34.75/25.18  tff(c_5216, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_92, c_90, c_86, c_5188])).
% 34.75/25.18  tff(c_5218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5128, c_5216])).
% 34.75/25.18  tff(c_5219, plain, (~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_4010])).
% 34.75/25.18  tff(c_5244, plain, (~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_5219])).
% 34.75/25.18  tff(c_126, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_119])).
% 34.75/25.18  tff(c_2, plain, (![A_1]: (v1_funct_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 34.75/25.18  tff(c_4, plain, (![A_1]: (v1_relat_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 34.75/25.18  tff(c_135, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_92, c_128])).
% 34.75/25.18  tff(c_166, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_135, c_160])).
% 34.75/25.18  tff(c_172, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_166])).
% 34.75/25.18  tff(c_3615, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_172])).
% 34.75/25.18  tff(c_3639, plain, (![A_255, B_256, C_257]: (k2_relset_1(A_255, B_256, C_257)=k2_relat_1(C_257) | ~m1_subset_1(C_257, k1_zfmisc_1(k2_zfmisc_1(A_255, B_256))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 34.75/25.18  tff(c_3642, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_3639])).
% 34.75/25.18  tff(c_3647, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_3642])).
% 34.75/25.18  tff(c_3656, plain, (v2_funct_2('#skF_3', k2_relat_1('#skF_3')) | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3647, c_36])).
% 34.75/25.18  tff(c_3662, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_135, c_3647, c_3656])).
% 34.75/25.18  tff(c_3664, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3615, c_3662])).
% 34.75/25.18  tff(c_3665, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_172])).
% 34.75/25.18  tff(c_3915, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3665, c_3909])).
% 34.75/25.18  tff(c_3920, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_96, c_80, c_3915])).
% 34.75/25.18  tff(c_3923, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_3920])).
% 34.75/25.18  tff(c_3927, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4, c_3923])).
% 34.75/25.18  tff(c_3931, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_96, c_3927])).
% 34.75/25.18  tff(c_3932, plain, (~v1_funct_1(k2_funct_1('#skF_3')) | v4_relat_1(k2_funct_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_3920])).
% 34.75/25.18  tff(c_3934, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_3932])).
% 34.75/25.18  tff(c_3937, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2, c_3934])).
% 34.75/25.18  tff(c_3941, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_96, c_3937])).
% 34.75/25.18  tff(c_3943, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_3932])).
% 34.75/25.18  tff(c_76, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_256])).
% 34.75/25.18  tff(c_5950, plain, (![A_388, C_389, B_390]: (k6_partfun1(A_388)=k5_relat_1(C_389, k2_funct_1(C_389)) | k1_xboole_0=B_390 | ~v2_funct_1(C_389) | k2_relset_1(A_388, B_390, C_389)!=B_390 | ~m1_subset_1(C_389, k1_zfmisc_1(k2_zfmisc_1(A_388, B_390))) | ~v1_funct_2(C_389, A_388, B_390) | ~v1_funct_1(C_389))), inference(cnfTransformation, [status(thm)], [f_220])).
% 34.75/25.18  tff(c_5962, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_5950])).
% 34.75/25.18  tff(c_5981, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_84, c_80, c_5962])).
% 34.75/25.18  tff(c_5982, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_76, c_5981])).
% 34.75/25.18  tff(c_5615, plain, (![C_377, B_378, A_379]: (m1_subset_1(k2_funct_1(C_377), k1_zfmisc_1(k2_zfmisc_1(B_378, A_379))) | k2_relset_1(A_379, B_378, C_377)!=B_378 | ~v2_funct_1(C_377) | ~m1_subset_1(C_377, k1_zfmisc_1(k2_zfmisc_1(A_379, B_378))) | ~v1_funct_2(C_377, A_379, B_378) | ~v1_funct_1(C_377))), inference(cnfTransformation, [status(thm)], [f_204])).
% 34.75/25.18  tff(c_44, plain, (![B_33, C_34, E_36, F_37, A_32, D_35]: (k1_partfun1(A_32, B_33, C_34, D_35, E_36, F_37)=k5_relat_1(E_36, F_37) | ~m1_subset_1(F_37, k1_zfmisc_1(k2_zfmisc_1(C_34, D_35))) | ~v1_funct_1(F_37) | ~m1_subset_1(E_36, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | ~v1_funct_1(E_36))), inference(cnfTransformation, [status(thm)], [f_143])).
% 34.75/25.18  tff(c_12709, plain, (![B_587, E_586, A_588, B_590, A_591, C_589]: (k1_partfun1(A_588, B_587, B_590, A_591, E_586, k2_funct_1(C_589))=k5_relat_1(E_586, k2_funct_1(C_589)) | ~v1_funct_1(k2_funct_1(C_589)) | ~m1_subset_1(E_586, k1_zfmisc_1(k2_zfmisc_1(A_588, B_587))) | ~v1_funct_1(E_586) | k2_relset_1(A_591, B_590, C_589)!=B_590 | ~v2_funct_1(C_589) | ~m1_subset_1(C_589, k1_zfmisc_1(k2_zfmisc_1(A_591, B_590))) | ~v1_funct_2(C_589, A_591, B_590) | ~v1_funct_1(C_589))), inference(resolution, [status(thm)], [c_5615, c_44])).
% 34.75/25.18  tff(c_12747, plain, (![B_590, A_591, C_589]: (k1_partfun1('#skF_1', '#skF_2', B_590, A_591, '#skF_3', k2_funct_1(C_589))=k5_relat_1('#skF_3', k2_funct_1(C_589)) | ~v1_funct_1(k2_funct_1(C_589)) | ~v1_funct_1('#skF_3') | k2_relset_1(A_591, B_590, C_589)!=B_590 | ~v2_funct_1(C_589) | ~m1_subset_1(C_589, k1_zfmisc_1(k2_zfmisc_1(A_591, B_590))) | ~v1_funct_2(C_589, A_591, B_590) | ~v1_funct_1(C_589))), inference(resolution, [status(thm)], [c_92, c_12709])).
% 34.75/25.18  tff(c_12980, plain, (![B_598, A_599, C_600]: (k1_partfun1('#skF_1', '#skF_2', B_598, A_599, '#skF_3', k2_funct_1(C_600))=k5_relat_1('#skF_3', k2_funct_1(C_600)) | ~v1_funct_1(k2_funct_1(C_600)) | k2_relset_1(A_599, B_598, C_600)!=B_598 | ~v2_funct_1(C_600) | ~m1_subset_1(C_600, k1_zfmisc_1(k2_zfmisc_1(A_599, B_598))) | ~v1_funct_2(C_600, A_599, B_598) | ~v1_funct_1(C_600))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_12747])).
% 34.75/25.18  tff(c_13037, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_12980])).
% 34.75/25.18  tff(c_13087, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_80, c_84, c_3943, c_5982, c_13037])).
% 34.75/25.18  tff(c_40, plain, (![B_27, D_29, A_26, E_30, F_31, C_28]: (m1_subset_1(k1_partfun1(A_26, B_27, C_28, D_29, E_30, F_31), k1_zfmisc_1(k2_zfmisc_1(A_26, D_29))) | ~m1_subset_1(F_31, k1_zfmisc_1(k2_zfmisc_1(C_28, D_29))) | ~v1_funct_1(F_31) | ~m1_subset_1(E_30, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~v1_funct_1(E_30))), inference(cnfTransformation, [status(thm)], [f_133])).
% 34.75/25.18  tff(c_13109, plain, (m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13087, c_40])).
% 34.75/25.18  tff(c_13126, plain, (m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_92, c_3943, c_13109])).
% 34.75/25.18  tff(c_13127, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_5244, c_13126])).
% 34.75/25.18  tff(c_13131, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_13127])).
% 34.75/25.18  tff(c_13135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_92, c_80, c_84, c_13131])).
% 34.75/25.18  tff(c_13136, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_5219])).
% 34.75/25.18  tff(c_14874, plain, (![D_674, E_677, A_678, C_675, B_676]: (k1_xboole_0=C_675 | v2_funct_1(E_677) | k2_relset_1(A_678, B_676, D_674)!=B_676 | ~v2_funct_1(k1_partfun1(A_678, B_676, B_676, C_675, D_674, E_677)) | ~m1_subset_1(E_677, k1_zfmisc_1(k2_zfmisc_1(B_676, C_675))) | ~v1_funct_2(E_677, B_676, C_675) | ~v1_funct_1(E_677) | ~m1_subset_1(D_674, k1_zfmisc_1(k2_zfmisc_1(A_678, B_676))) | ~v1_funct_2(D_674, A_678, B_676) | ~v1_funct_1(D_674))), inference(cnfTransformation, [status(thm)], [f_188])).
% 34.75/25.18  tff(c_14882, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13136, c_14874])).
% 34.75/25.18  tff(c_14893, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_92, c_90, c_88, c_86, c_100, c_84, c_14882])).
% 34.75/25.18  tff(c_14895, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3955, c_78, c_14893])).
% 34.75/25.18  tff(c_14897, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_3922])).
% 34.75/25.18  tff(c_3705, plain, (![A_262, B_263, C_264]: (k2_relset_1(A_262, B_263, C_264)=k2_relat_1(C_264) | ~m1_subset_1(C_264, k1_zfmisc_1(k2_zfmisc_1(A_262, B_263))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 34.75/25.18  tff(c_3711, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_86, c_3705])).
% 34.75/25.18  tff(c_3715, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3599, c_3711])).
% 34.75/25.18  tff(c_22, plain, (![A_8, B_10]: (k2_funct_1(A_8)=B_10 | k6_relat_1(k2_relat_1(A_8))!=k5_relat_1(B_10, A_8) | k2_relat_1(B_10)!=k1_relat_1(A_8) | ~v2_funct_1(A_8) | ~v1_funct_1(B_10) | ~v1_relat_1(B_10) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_91])).
% 34.75/25.18  tff(c_30526, plain, (![A_1161, B_1162]: (k2_funct_1(A_1161)=B_1162 | k6_partfun1(k2_relat_1(A_1161))!=k5_relat_1(B_1162, A_1161) | k2_relat_1(B_1162)!=k1_relat_1(A_1161) | ~v2_funct_1(A_1161) | ~v1_funct_1(B_1162) | ~v1_relat_1(B_1162) | ~v1_funct_1(A_1161) | ~v1_relat_1(A_1161))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_22])).
% 34.75/25.18  tff(c_30536, plain, (![B_1162]: (k2_funct_1('#skF_4')=B_1162 | k5_relat_1(B_1162, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_1162)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_1162) | ~v1_relat_1(B_1162) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3599, c_30526])).
% 34.75/25.18  tff(c_30553, plain, (![B_1163]: (k2_funct_1('#skF_4')=B_1163 | k5_relat_1(B_1163, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_1163)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_1163) | ~v1_relat_1(B_1163))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_90, c_14897, c_30536])).
% 34.75/25.18  tff(c_30565, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_126, c_30553])).
% 34.75/25.18  tff(c_30584, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k1_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_3665, c_30565])).
% 34.75/25.18  tff(c_30588, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitLeft, [status(thm)], [c_30584])).
% 34.75/25.18  tff(c_14896, plain, (~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | v4_relat_1(k2_funct_1('#skF_4'), '#skF_1')), inference(splitRight, [status(thm)], [c_3922])).
% 34.75/25.18  tff(c_14898, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_14896])).
% 34.75/25.18  tff(c_14901, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2, c_14898])).
% 34.75/25.18  tff(c_14905, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_127, c_90, c_14901])).
% 34.75/25.18  tff(c_14907, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_14896])).
% 34.75/25.18  tff(c_30589, plain, (![C_1164, B_1165, A_1166]: (v1_funct_2(k2_funct_1(C_1164), B_1165, A_1166) | k2_relset_1(A_1166, B_1165, C_1164)!=B_1165 | ~v2_funct_1(C_1164) | ~m1_subset_1(C_1164, k1_zfmisc_1(k2_zfmisc_1(A_1166, B_1165))) | ~v1_funct_2(C_1164, A_1166, B_1165) | ~v1_funct_1(C_1164))), inference(cnfTransformation, [status(thm)], [f_204])).
% 34.75/25.18  tff(c_30607, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_1', '#skF_2') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_86, c_30589])).
% 34.75/25.18  tff(c_30623, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_14897, c_3715, c_30607])).
% 34.75/25.18  tff(c_3933, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_3920])).
% 34.75/25.18  tff(c_30534, plain, (![B_1162]: (k2_funct_1('#skF_3')=B_1162 | k5_relat_1(B_1162, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_1162)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_1162) | ~v1_relat_1(B_1162) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3665, c_30526])).
% 34.75/25.18  tff(c_30625, plain, (![B_1167]: (k2_funct_1('#skF_3')=B_1167 | k5_relat_1(B_1167, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_1167)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_1167) | ~v1_relat_1(B_1167))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_96, c_80, c_30534])).
% 34.75/25.18  tff(c_30634, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_127, c_30625])).
% 34.75/25.18  tff(c_30653, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_3599, c_30634])).
% 34.75/25.18  tff(c_30654, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_74, c_30653])).
% 34.75/25.18  tff(c_30665, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_30654])).
% 34.75/25.18  tff(c_30604, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_30589])).
% 34.75/25.18  tff(c_30620, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_80, c_84, c_30604])).
% 34.75/25.18  tff(c_15829, plain, (![E_745, C_744, B_741, D_740, A_742, F_743]: (m1_subset_1(k1_partfun1(A_742, B_741, C_744, D_740, E_745, F_743), k1_zfmisc_1(k2_zfmisc_1(A_742, D_740))) | ~m1_subset_1(F_743, k1_zfmisc_1(k2_zfmisc_1(C_744, D_740))) | ~v1_funct_1(F_743) | ~m1_subset_1(E_745, k1_zfmisc_1(k2_zfmisc_1(A_742, B_741))) | ~v1_funct_1(E_745))), inference(cnfTransformation, [status(thm)], [f_133])).
% 34.75/25.18  tff(c_14941, plain, (![D_683, C_684, A_685, B_686]: (D_683=C_684 | ~r2_relset_1(A_685, B_686, C_684, D_683) | ~m1_subset_1(D_683, k1_zfmisc_1(k2_zfmisc_1(A_685, B_686))) | ~m1_subset_1(C_684, k1_zfmisc_1(k2_zfmisc_1(A_685, B_686))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 34.75/25.18  tff(c_14972, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_82, c_14941])).
% 34.75/25.18  tff(c_14974, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_14972])).
% 34.75/25.18  tff(c_15861, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_15829, c_14974])).
% 34.75/25.18  tff(c_15890, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_92, c_90, c_86, c_15861])).
% 34.75/25.18  tff(c_15891, plain, (~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_14972])).
% 34.75/25.18  tff(c_15912, plain, (~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_15891])).
% 34.75/25.18  tff(c_16939, plain, (![A_813, C_814, B_815]: (k6_partfun1(A_813)=k5_relat_1(C_814, k2_funct_1(C_814)) | k1_xboole_0=B_815 | ~v2_funct_1(C_814) | k2_relset_1(A_813, B_815, C_814)!=B_815 | ~m1_subset_1(C_814, k1_zfmisc_1(k2_zfmisc_1(A_813, B_815))) | ~v1_funct_2(C_814, A_813, B_815) | ~v1_funct_1(C_814))), inference(cnfTransformation, [status(thm)], [f_220])).
% 34.75/25.18  tff(c_16951, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_16939])).
% 34.75/25.18  tff(c_16970, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_84, c_80, c_16951])).
% 34.75/25.18  tff(c_16971, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_76, c_16970])).
% 34.75/25.18  tff(c_16607, plain, (![C_803, B_804, A_805]: (m1_subset_1(k2_funct_1(C_803), k1_zfmisc_1(k2_zfmisc_1(B_804, A_805))) | k2_relset_1(A_805, B_804, C_803)!=B_804 | ~v2_funct_1(C_803) | ~m1_subset_1(C_803, k1_zfmisc_1(k2_zfmisc_1(A_805, B_804))) | ~v1_funct_2(C_803, A_805, B_804) | ~v1_funct_1(C_803))), inference(cnfTransformation, [status(thm)], [f_204])).
% 34.75/25.18  tff(c_28533, plain, (![C_1069, B_1071, A_1072, A_1074, B_1073, E_1070]: (k1_partfun1(A_1072, B_1071, B_1073, A_1074, E_1070, k2_funct_1(C_1069))=k5_relat_1(E_1070, k2_funct_1(C_1069)) | ~v1_funct_1(k2_funct_1(C_1069)) | ~m1_subset_1(E_1070, k1_zfmisc_1(k2_zfmisc_1(A_1072, B_1071))) | ~v1_funct_1(E_1070) | k2_relset_1(A_1074, B_1073, C_1069)!=B_1073 | ~v2_funct_1(C_1069) | ~m1_subset_1(C_1069, k1_zfmisc_1(k2_zfmisc_1(A_1074, B_1073))) | ~v1_funct_2(C_1069, A_1074, B_1073) | ~v1_funct_1(C_1069))), inference(resolution, [status(thm)], [c_16607, c_44])).
% 34.75/25.18  tff(c_28569, plain, (![B_1073, A_1074, C_1069]: (k1_partfun1('#skF_1', '#skF_2', B_1073, A_1074, '#skF_3', k2_funct_1(C_1069))=k5_relat_1('#skF_3', k2_funct_1(C_1069)) | ~v1_funct_1(k2_funct_1(C_1069)) | ~v1_funct_1('#skF_3') | k2_relset_1(A_1074, B_1073, C_1069)!=B_1073 | ~v2_funct_1(C_1069) | ~m1_subset_1(C_1069, k1_zfmisc_1(k2_zfmisc_1(A_1074, B_1073))) | ~v1_funct_2(C_1069, A_1074, B_1073) | ~v1_funct_1(C_1069))), inference(resolution, [status(thm)], [c_92, c_28533])).
% 34.75/25.18  tff(c_29967, plain, (![B_1126, A_1127, C_1128]: (k1_partfun1('#skF_1', '#skF_2', B_1126, A_1127, '#skF_3', k2_funct_1(C_1128))=k5_relat_1('#skF_3', k2_funct_1(C_1128)) | ~v1_funct_1(k2_funct_1(C_1128)) | k2_relset_1(A_1127, B_1126, C_1128)!=B_1126 | ~v2_funct_1(C_1128) | ~m1_subset_1(C_1128, k1_zfmisc_1(k2_zfmisc_1(A_1127, B_1126))) | ~v1_funct_2(C_1128, A_1127, B_1126) | ~v1_funct_1(C_1128))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_28569])).
% 34.75/25.18  tff(c_30021, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_29967])).
% 34.75/25.18  tff(c_30068, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_80, c_84, c_3943, c_16971, c_30021])).
% 34.75/25.18  tff(c_30094, plain, (m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30068, c_40])).
% 34.75/25.18  tff(c_30115, plain, (m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_92, c_3943, c_30094])).
% 34.75/25.18  tff(c_30116, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_15912, c_30115])).
% 34.75/25.18  tff(c_30120, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_30116])).
% 34.75/25.18  tff(c_30124, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_92, c_80, c_84, c_30120])).
% 34.75/25.18  tff(c_30126, plain, (m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitRight, [status(thm)], [c_15891])).
% 34.75/25.18  tff(c_32, plain, (![A_20, B_21, D_23]: (r2_relset_1(A_20, B_21, D_23, D_23) | ~m1_subset_1(D_23, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 34.75/25.18  tff(c_30142, plain, (r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1'))), inference(resolution, [status(thm)], [c_30126, c_32])).
% 34.75/25.18  tff(c_14, plain, (![A_6]: (k2_relat_1(k2_funct_1(A_6))=k1_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_64])).
% 34.75/25.18  tff(c_30967, plain, (![A_1197, C_1198, B_1199]: (k6_partfun1(A_1197)=k5_relat_1(C_1198, k2_funct_1(C_1198)) | k1_xboole_0=B_1199 | ~v2_funct_1(C_1198) | k2_relset_1(A_1197, B_1199, C_1198)!=B_1199 | ~m1_subset_1(C_1198, k1_zfmisc_1(k2_zfmisc_1(A_1197, B_1199))) | ~v1_funct_2(C_1198, A_1197, B_1199) | ~v1_funct_1(C_1198))), inference(cnfTransformation, [status(thm)], [f_220])).
% 34.75/25.18  tff(c_30979, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_30967])).
% 34.75/25.18  tff(c_30998, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_84, c_80, c_30979])).
% 34.75/25.18  tff(c_30999, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_76, c_30998])).
% 34.75/25.18  tff(c_10, plain, (![A_3, B_5]: (v2_funct_1(A_3) | k2_relat_1(B_5)!=k1_relat_1(A_3) | ~v2_funct_1(k5_relat_1(B_5, A_3)) | ~v1_funct_1(B_5) | ~v1_relat_1(B_5) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_54])).
% 34.75/25.18  tff(c_31007, plain, (v2_funct_1(k2_funct_1('#skF_3')) | k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_30999, c_10])).
% 34.75/25.18  tff(c_31020, plain, (v2_funct_1(k2_funct_1('#skF_3')) | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3933, c_3943, c_126, c_96, c_100, c_3665, c_31007])).
% 34.75/25.18  tff(c_31074, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_31020])).
% 34.75/25.18  tff(c_31077, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_31074])).
% 34.75/25.18  tff(c_31080, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_96, c_80, c_3665, c_31077])).
% 34.75/25.18  tff(c_31082, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_31020])).
% 34.75/25.18  tff(c_68, plain, (![A_56]: (m1_subset_1(A_56, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_56), k2_relat_1(A_56)))) | ~v1_funct_1(A_56) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_230])).
% 34.75/25.18  tff(c_31150, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3'))))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_31082, c_68])).
% 34.75/25.18  tff(c_31181, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_3933, c_3943, c_31150])).
% 34.75/25.18  tff(c_31683, plain, (v5_relat_1(k2_funct_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_31181, c_26])).
% 34.75/25.18  tff(c_31694, plain, (v2_funct_2(k2_funct_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_31683, c_36])).
% 34.75/25.18  tff(c_31704, plain, (v2_funct_2(k2_funct_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_3933, c_31694])).
% 34.75/25.18  tff(c_31715, plain, (v2_funct_2(k2_funct_1('#skF_3'), k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14, c_31704])).
% 34.75/25.18  tff(c_31717, plain, (v2_funct_2(k2_funct_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_96, c_80, c_31715])).
% 34.75/25.18  tff(c_31697, plain, (v5_relat_1(k2_funct_1('#skF_3'), k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14, c_31683])).
% 34.75/25.18  tff(c_31706, plain, (v5_relat_1(k2_funct_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_96, c_80, c_31697])).
% 34.75/25.18  tff(c_38, plain, (![B_25, A_24]: (k2_relat_1(B_25)=A_24 | ~v2_funct_2(B_25, A_24) | ~v5_relat_1(B_25, A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_121])).
% 34.75/25.18  tff(c_31709, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~v2_funct_2(k2_funct_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_31706, c_38])).
% 34.75/25.18  tff(c_31712, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~v2_funct_2(k2_funct_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3933, c_31709])).
% 34.75/25.18  tff(c_32739, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_31717, c_31712])).
% 34.75/25.18  tff(c_30737, plain, (![C_1177, B_1178, A_1179]: (m1_subset_1(k2_funct_1(C_1177), k1_zfmisc_1(k2_zfmisc_1(B_1178, A_1179))) | k2_relset_1(A_1179, B_1178, C_1177)!=B_1178 | ~v2_funct_1(C_1177) | ~m1_subset_1(C_1177, k1_zfmisc_1(k2_zfmisc_1(A_1179, B_1178))) | ~v1_funct_2(C_1177, A_1179, B_1178) | ~v1_funct_1(C_1177))), inference(cnfTransformation, [status(thm)], [f_204])).
% 34.75/25.18  tff(c_30, plain, (![A_17, B_18, C_19]: (k2_relset_1(A_17, B_18, C_19)=k2_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 34.75/25.18  tff(c_37740, plain, (![B_1363, A_1364, C_1365]: (k2_relset_1(B_1363, A_1364, k2_funct_1(C_1365))=k2_relat_1(k2_funct_1(C_1365)) | k2_relset_1(A_1364, B_1363, C_1365)!=B_1363 | ~v2_funct_1(C_1365) | ~m1_subset_1(C_1365, k1_zfmisc_1(k2_zfmisc_1(A_1364, B_1363))) | ~v1_funct_2(C_1365, A_1364, B_1363) | ~v1_funct_1(C_1365))), inference(resolution, [status(thm)], [c_30737, c_30])).
% 34.75/25.18  tff(c_37797, plain, (k2_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_37740])).
% 34.75/25.18  tff(c_37847, plain, (k2_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_80, c_84, c_32739, c_37797])).
% 34.75/25.18  tff(c_30847, plain, (![D_1190, C_1188, E_1185, F_1187, A_1189, B_1186]: (k1_partfun1(A_1189, B_1186, C_1188, D_1190, E_1185, F_1187)=k5_relat_1(E_1185, F_1187) | ~m1_subset_1(F_1187, k1_zfmisc_1(k2_zfmisc_1(C_1188, D_1190))) | ~v1_funct_1(F_1187) | ~m1_subset_1(E_1185, k1_zfmisc_1(k2_zfmisc_1(A_1189, B_1186))) | ~v1_funct_1(E_1185))), inference(cnfTransformation, [status(thm)], [f_143])).
% 34.75/25.18  tff(c_39453, plain, (![C_1401, A_1399, B_1402, B_1400, E_1398, A_1403]: (k1_partfun1(A_1403, B_1400, B_1402, A_1399, E_1398, k2_funct_1(C_1401))=k5_relat_1(E_1398, k2_funct_1(C_1401)) | ~v1_funct_1(k2_funct_1(C_1401)) | ~m1_subset_1(E_1398, k1_zfmisc_1(k2_zfmisc_1(A_1403, B_1400))) | ~v1_funct_1(E_1398) | k2_relset_1(A_1399, B_1402, C_1401)!=B_1402 | ~v2_funct_1(C_1401) | ~m1_subset_1(C_1401, k1_zfmisc_1(k2_zfmisc_1(A_1399, B_1402))) | ~v1_funct_2(C_1401, A_1399, B_1402) | ~v1_funct_1(C_1401))), inference(resolution, [status(thm)], [c_58, c_30847])).
% 34.75/25.18  tff(c_39491, plain, (![B_1402, A_1399, C_1401]: (k1_partfun1('#skF_1', '#skF_2', B_1402, A_1399, '#skF_3', k2_funct_1(C_1401))=k5_relat_1('#skF_3', k2_funct_1(C_1401)) | ~v1_funct_1(k2_funct_1(C_1401)) | ~v1_funct_1('#skF_3') | k2_relset_1(A_1399, B_1402, C_1401)!=B_1402 | ~v2_funct_1(C_1401) | ~m1_subset_1(C_1401, k1_zfmisc_1(k2_zfmisc_1(A_1399, B_1402))) | ~v1_funct_2(C_1401, A_1399, B_1402) | ~v1_funct_1(C_1401))), inference(resolution, [status(thm)], [c_92, c_39453])).
% 34.75/25.18  tff(c_53967, plain, (![B_1587, A_1588, C_1589]: (k1_partfun1('#skF_1', '#skF_2', B_1587, A_1588, '#skF_3', k2_funct_1(C_1589))=k5_relat_1('#skF_3', k2_funct_1(C_1589)) | ~v1_funct_1(k2_funct_1(C_1589)) | k2_relset_1(A_1588, B_1587, C_1589)!=B_1587 | ~v2_funct_1(C_1589) | ~m1_subset_1(C_1589, k1_zfmisc_1(k2_zfmisc_1(A_1588, B_1587))) | ~v1_funct_2(C_1589, A_1588, B_1587) | ~v1_funct_1(C_1589))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_39491])).
% 34.75/25.18  tff(c_54084, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_53967])).
% 34.75/25.18  tff(c_54192, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_80, c_84, c_3943, c_30999, c_54084])).
% 34.75/25.18  tff(c_48, plain, (![A_39, B_40, C_41, D_43]: (k2_relset_1(A_39, B_40, C_41)=B_40 | ~r2_relset_1(B_40, B_40, k1_partfun1(B_40, A_39, A_39, B_40, D_43, C_41), k6_partfun1(B_40)) | ~m1_subset_1(D_43, k1_zfmisc_1(k2_zfmisc_1(B_40, A_39))) | ~v1_funct_2(D_43, B_40, A_39) | ~v1_funct_1(D_43) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))) | ~v1_funct_2(C_41, A_39, B_40) | ~v1_funct_1(C_41))), inference(cnfTransformation, [status(thm)], [f_162])).
% 34.75/25.18  tff(c_54228, plain, (k2_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_54192, c_48])).
% 34.75/25.18  tff(c_54262, plain, (k1_relat_1('#skF_3')='#skF_1' | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3943, c_30620, c_96, c_94, c_92, c_30142, c_37847, c_54228])).
% 34.75/25.18  tff(c_54263, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_30665, c_54262])).
% 34.75/25.18  tff(c_54272, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_54263])).
% 34.75/25.18  tff(c_54276, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_92, c_80, c_84, c_54272])).
% 34.75/25.18  tff(c_54278, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_30654])).
% 34.75/25.18  tff(c_3817, plain, (![A_267]: (v5_relat_1(A_267, k2_relat_1(A_267)) | ~v1_funct_1(A_267) | ~v1_relat_1(A_267))), inference(resolution, [status(thm)], [c_3720, c_26])).
% 34.75/25.18  tff(c_3844, plain, (![A_269]: (v2_funct_2(A_269, k2_relat_1(A_269)) | ~v1_funct_1(A_269) | ~v1_relat_1(A_269))), inference(resolution, [status(thm)], [c_3817, c_36])).
% 34.75/25.18  tff(c_3847, plain, (![A_6]: (v2_funct_2(k2_funct_1(A_6), k1_relat_1(A_6)) | ~v1_funct_1(k2_funct_1(A_6)) | ~v1_relat_1(k2_funct_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(superposition, [status(thm), theory('equality')], [c_14, c_3844])).
% 34.75/25.18  tff(c_54299, plain, (v2_funct_2(k2_funct_1('#skF_3'), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_54278, c_3847])).
% 34.75/25.18  tff(c_54323, plain, (v2_funct_2(k2_funct_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_96, c_80, c_3933, c_3943, c_54299])).
% 34.75/25.18  tff(c_3826, plain, (![A_6]: (v5_relat_1(k2_funct_1(A_6), k1_relat_1(A_6)) | ~v1_funct_1(k2_funct_1(A_6)) | ~v1_relat_1(k2_funct_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(superposition, [status(thm), theory('equality')], [c_14, c_3817])).
% 34.75/25.18  tff(c_54302, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_54278, c_3826])).
% 34.75/25.18  tff(c_54325, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_96, c_80, c_3933, c_3943, c_54302])).
% 34.75/25.18  tff(c_54339, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_54325, c_38])).
% 34.75/25.18  tff(c_54342, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3933, c_54323, c_54339])).
% 34.75/25.18  tff(c_54372, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_54342, c_68])).
% 34.75/25.18  tff(c_54404, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3933, c_3943, c_54372])).
% 34.75/25.18  tff(c_54481, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_54404])).
% 34.75/25.18  tff(c_54500, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_96, c_80, c_3665, c_54481])).
% 34.75/25.18  tff(c_54915, plain, (![B_1614, C_1615, A_1616]: (k6_partfun1(B_1614)=k5_relat_1(k2_funct_1(C_1615), C_1615) | k1_xboole_0=B_1614 | ~v2_funct_1(C_1615) | k2_relset_1(A_1616, B_1614, C_1615)!=B_1614 | ~m1_subset_1(C_1615, k1_zfmisc_1(k2_zfmisc_1(A_1616, B_1614))) | ~v1_funct_2(C_1615, A_1616, B_1614) | ~v1_funct_1(C_1615))), inference(cnfTransformation, [status(thm)], [f_220])).
% 34.75/25.18  tff(c_54929, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_54915])).
% 34.75/25.18  tff(c_54952, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_84, c_80, c_54929])).
% 34.75/25.18  tff(c_54953, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_76, c_54952])).
% 34.75/25.18  tff(c_54660, plain, (![F_1604, B_1603, D_1607, E_1602, C_1605, A_1606]: (k1_partfun1(A_1606, B_1603, C_1605, D_1607, E_1602, F_1604)=k5_relat_1(E_1602, F_1604) | ~m1_subset_1(F_1604, k1_zfmisc_1(k2_zfmisc_1(C_1605, D_1607))) | ~v1_funct_1(F_1604) | ~m1_subset_1(E_1602, k1_zfmisc_1(k2_zfmisc_1(A_1606, B_1603))) | ~v1_funct_1(E_1602))), inference(cnfTransformation, [status(thm)], [f_143])).
% 34.75/25.18  tff(c_54674, plain, (![A_1606, B_1603, E_1602]: (k1_partfun1(A_1606, B_1603, '#skF_1', '#skF_2', E_1602, '#skF_3')=k5_relat_1(E_1602, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_1602, k1_zfmisc_1(k2_zfmisc_1(A_1606, B_1603))) | ~v1_funct_1(E_1602))), inference(resolution, [status(thm)], [c_92, c_54660])).
% 34.75/25.18  tff(c_55850, plain, (![A_1648, B_1649, E_1650]: (k1_partfun1(A_1648, B_1649, '#skF_1', '#skF_2', E_1650, '#skF_3')=k5_relat_1(E_1650, '#skF_3') | ~m1_subset_1(E_1650, k1_zfmisc_1(k2_zfmisc_1(A_1648, B_1649))) | ~v1_funct_1(E_1650))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_54674])).
% 34.75/25.18  tff(c_55871, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_54500, c_55850])).
% 34.75/25.18  tff(c_55906, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3943, c_54953, c_55871])).
% 34.75/25.18  tff(c_56307, plain, (m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_55906, c_40])).
% 34.75/25.18  tff(c_56319, plain, (m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_3943, c_54500, c_96, c_92, c_56307])).
% 34.75/25.18  tff(c_56394, plain, (r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))), inference(resolution, [status(thm)], [c_56319, c_32])).
% 34.75/25.18  tff(c_14906, plain, (~v1_relat_1(k2_funct_1('#skF_4')) | v4_relat_1(k2_funct_1('#skF_4'), '#skF_1')), inference(splitRight, [status(thm)], [c_14896])).
% 34.75/25.18  tff(c_14908, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_14906])).
% 34.75/25.18  tff(c_14911, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4, c_14908])).
% 34.75/25.18  tff(c_14915, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_127, c_90, c_14911])).
% 34.75/25.18  tff(c_14917, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_14906])).
% 34.75/25.18  tff(c_54744, plain, (![A_1611, C_1612, B_1613]: (k6_partfun1(A_1611)=k5_relat_1(C_1612, k2_funct_1(C_1612)) | k1_xboole_0=B_1613 | ~v2_funct_1(C_1612) | k2_relset_1(A_1611, B_1613, C_1612)!=B_1613 | ~m1_subset_1(C_1612, k1_zfmisc_1(k2_zfmisc_1(A_1611, B_1613))) | ~v1_funct_2(C_1612, A_1611, B_1613) | ~v1_funct_1(C_1612))), inference(cnfTransformation, [status(thm)], [f_220])).
% 34.75/25.18  tff(c_54760, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_86, c_54744])).
% 34.75/25.18  tff(c_54785, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_3715, c_14897, c_54760])).
% 34.75/25.18  tff(c_54786, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_78, c_54785])).
% 34.75/25.18  tff(c_54814, plain, (v2_funct_1(k2_funct_1('#skF_4')) | k1_relat_1(k2_funct_1('#skF_4'))!=k2_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_54786, c_10])).
% 34.75/25.18  tff(c_54827, plain, (v2_funct_1(k2_funct_1('#skF_4')) | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14917, c_14907, c_127, c_90, c_100, c_3599, c_54814])).
% 34.75/25.18  tff(c_54847, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_54827])).
% 34.75/25.18  tff(c_54850, plain, (k2_relat_1('#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_16, c_54847])).
% 34.75/25.18  tff(c_54853, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_127, c_90, c_14897, c_3599, c_54850])).
% 34.75/25.18  tff(c_54855, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_1'), inference(splitRight, [status(thm)], [c_54827])).
% 34.75/25.18  tff(c_54880, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', k2_relat_1(k2_funct_1('#skF_4'))))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_54855, c_68])).
% 34.75/25.18  tff(c_54907, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', k2_relat_1(k2_funct_1('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_14917, c_14907, c_54880])).
% 34.75/25.18  tff(c_55223, plain, (v5_relat_1(k2_funct_1('#skF_4'), k2_relat_1(k2_funct_1('#skF_4')))), inference(resolution, [status(thm)], [c_54907, c_26])).
% 34.75/25.18  tff(c_55233, plain, (v2_funct_2(k2_funct_1('#skF_4'), k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_55223, c_36])).
% 34.75/25.18  tff(c_55243, plain, (v2_funct_2(k2_funct_1('#skF_4'), k2_relat_1(k2_funct_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_14917, c_55233])).
% 34.75/25.18  tff(c_55255, plain, (v2_funct_2(k2_funct_1('#skF_4'), k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_14, c_55243])).
% 34.75/25.18  tff(c_55257, plain, (v2_funct_2(k2_funct_1('#skF_4'), k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_90, c_14897, c_55255])).
% 34.75/25.18  tff(c_55236, plain, (v5_relat_1(k2_funct_1('#skF_4'), k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_14, c_55223])).
% 34.75/25.18  tff(c_55245, plain, (v5_relat_1(k2_funct_1('#skF_4'), k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_90, c_14897, c_55236])).
% 34.75/25.18  tff(c_55249, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4') | ~v2_funct_2(k2_funct_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_55245, c_38])).
% 34.75/25.18  tff(c_55252, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4') | ~v2_funct_2(k2_funct_1('#skF_4'), k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14917, c_55249])).
% 34.75/25.18  tff(c_55528, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_55257, c_55252])).
% 34.75/25.18  tff(c_54603, plain, (![C_1599, B_1600, A_1601]: (m1_subset_1(k2_funct_1(C_1599), k1_zfmisc_1(k2_zfmisc_1(B_1600, A_1601))) | k2_relset_1(A_1601, B_1600, C_1599)!=B_1600 | ~v2_funct_1(C_1599) | ~m1_subset_1(C_1599, k1_zfmisc_1(k2_zfmisc_1(A_1601, B_1600))) | ~v1_funct_2(C_1599, A_1601, B_1600) | ~v1_funct_1(C_1599))), inference(cnfTransformation, [status(thm)], [f_204])).
% 34.75/25.18  tff(c_60334, plain, (![B_1743, A_1744, C_1745]: (k2_relset_1(B_1743, A_1744, k2_funct_1(C_1745))=k2_relat_1(k2_funct_1(C_1745)) | k2_relset_1(A_1744, B_1743, C_1745)!=B_1743 | ~v2_funct_1(C_1745) | ~m1_subset_1(C_1745, k1_zfmisc_1(k2_zfmisc_1(A_1744, B_1743))) | ~v1_funct_2(C_1745, A_1744, B_1743) | ~v1_funct_1(C_1745))), inference(resolution, [status(thm)], [c_54603, c_30])).
% 34.75/25.18  tff(c_60394, plain, (k2_relset_1('#skF_1', '#skF_2', k2_funct_1('#skF_4'))=k2_relat_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_86, c_60334])).
% 34.75/25.18  tff(c_60444, plain, (k2_relset_1('#skF_1', '#skF_2', k2_funct_1('#skF_4'))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_14897, c_3715, c_55528, c_60394])).
% 34.75/25.18  tff(c_62429, plain, (![A_1792, A_1788, B_1789, B_1791, C_1790, E_1787]: (k1_partfun1(A_1792, B_1789, B_1791, A_1788, E_1787, k2_funct_1(C_1790))=k5_relat_1(E_1787, k2_funct_1(C_1790)) | ~v1_funct_1(k2_funct_1(C_1790)) | ~m1_subset_1(E_1787, k1_zfmisc_1(k2_zfmisc_1(A_1792, B_1789))) | ~v1_funct_1(E_1787) | k2_relset_1(A_1788, B_1791, C_1790)!=B_1791 | ~v2_funct_1(C_1790) | ~m1_subset_1(C_1790, k1_zfmisc_1(k2_zfmisc_1(A_1788, B_1791))) | ~v1_funct_2(C_1790, A_1788, B_1791) | ~v1_funct_1(C_1790))), inference(resolution, [status(thm)], [c_58, c_54660])).
% 34.75/25.18  tff(c_62469, plain, (![B_1791, A_1788, C_1790]: (k1_partfun1('#skF_2', '#skF_1', B_1791, A_1788, '#skF_4', k2_funct_1(C_1790))=k5_relat_1('#skF_4', k2_funct_1(C_1790)) | ~v1_funct_1(k2_funct_1(C_1790)) | ~v1_funct_1('#skF_4') | k2_relset_1(A_1788, B_1791, C_1790)!=B_1791 | ~v2_funct_1(C_1790) | ~m1_subset_1(C_1790, k1_zfmisc_1(k2_zfmisc_1(A_1788, B_1791))) | ~v1_funct_2(C_1790, A_1788, B_1791) | ~v1_funct_1(C_1790))), inference(resolution, [status(thm)], [c_86, c_62429])).
% 34.75/25.18  tff(c_77811, plain, (![B_1984, A_1985, C_1986]: (k1_partfun1('#skF_2', '#skF_1', B_1984, A_1985, '#skF_4', k2_funct_1(C_1986))=k5_relat_1('#skF_4', k2_funct_1(C_1986)) | ~v1_funct_1(k2_funct_1(C_1986)) | k2_relset_1(A_1985, B_1984, C_1986)!=B_1984 | ~v2_funct_1(C_1986) | ~m1_subset_1(C_1986, k1_zfmisc_1(k2_zfmisc_1(A_1985, B_1984))) | ~v1_funct_2(C_1986, A_1985, B_1984) | ~v1_funct_1(C_1986))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_62469])).
% 34.75/25.18  tff(c_77937, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', k2_funct_1('#skF_4'))=k5_relat_1('#skF_4', k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_86, c_77811])).
% 34.75/25.18  tff(c_78051, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_14897, c_3715, c_14907, c_54786, c_77937])).
% 34.75/25.18  tff(c_78084, plain, (k2_relset_1('#skF_1', '#skF_2', k2_funct_1('#skF_4'))='#skF_2' | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_1', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_78051, c_48])).
% 34.75/25.18  tff(c_78118, plain, (k1_relat_1('#skF_4')='#skF_2' | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_14907, c_30623, c_90, c_88, c_86, c_56394, c_60444, c_78084])).
% 34.75/25.18  tff(c_78119, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_30588, c_78118])).
% 34.75/25.18  tff(c_78128, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_78119])).
% 34.75/25.18  tff(c_78132, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_14897, c_3715, c_78128])).
% 34.75/25.18  tff(c_78133, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_30584])).
% 34.75/25.18  tff(c_78192, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_78133])).
% 34.75/25.18  tff(c_30125, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_15891])).
% 34.75/25.18  tff(c_78529, plain, (![C_2005, F_2004, D_2007, B_2003, E_2002, A_2006]: (k1_partfun1(A_2006, B_2003, C_2005, D_2007, E_2002, F_2004)=k5_relat_1(E_2002, F_2004) | ~m1_subset_1(F_2004, k1_zfmisc_1(k2_zfmisc_1(C_2005, D_2007))) | ~v1_funct_1(F_2004) | ~m1_subset_1(E_2002, k1_zfmisc_1(k2_zfmisc_1(A_2006, B_2003))) | ~v1_funct_1(E_2002))), inference(cnfTransformation, [status(thm)], [f_143])).
% 34.75/25.18  tff(c_78543, plain, (![A_2006, B_2003, E_2002]: (k1_partfun1(A_2006, B_2003, '#skF_2', '#skF_1', E_2002, '#skF_4')=k5_relat_1(E_2002, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_2002, k1_zfmisc_1(k2_zfmisc_1(A_2006, B_2003))) | ~v1_funct_1(E_2002))), inference(resolution, [status(thm)], [c_86, c_78529])).
% 34.75/25.18  tff(c_79739, plain, (![A_2048, B_2049, E_2050]: (k1_partfun1(A_2048, B_2049, '#skF_2', '#skF_1', E_2050, '#skF_4')=k5_relat_1(E_2050, '#skF_4') | ~m1_subset_1(E_2050, k1_zfmisc_1(k2_zfmisc_1(A_2048, B_2049))) | ~v1_funct_1(E_2050))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_78543])).
% 34.75/25.18  tff(c_79781, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_79739])).
% 34.75/25.18  tff(c_79820, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_30125, c_79781])).
% 34.75/25.18  tff(c_79822, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78192, c_79820])).
% 34.75/25.18  tff(c_79823, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_78133])).
% 34.75/25.18  tff(c_79872, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_79823, c_16])).
% 34.75/25.18  tff(c_79906, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_127, c_90, c_14897, c_3599, c_79872])).
% 34.75/25.18  tff(c_78134, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_30584])).
% 34.75/25.18  tff(c_20, plain, (![A_7]: (k5_relat_1(A_7, k2_funct_1(A_7))=k6_relat_1(k1_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_74])).
% 34.75/25.18  tff(c_98, plain, (![A_7]: (k5_relat_1(A_7, k2_funct_1(A_7))=k6_partfun1(k1_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_20])).
% 34.75/25.18  tff(c_85654, plain, (![A_2201]: (k2_funct_1(k2_funct_1(A_2201))=A_2201 | k6_partfun1(k2_relat_1(k2_funct_1(A_2201)))!=k6_partfun1(k1_relat_1(A_2201)) | k1_relat_1(k2_funct_1(A_2201))!=k2_relat_1(A_2201) | ~v2_funct_1(k2_funct_1(A_2201)) | ~v1_funct_1(A_2201) | ~v1_relat_1(A_2201) | ~v1_funct_1(k2_funct_1(A_2201)) | ~v1_relat_1(k2_funct_1(A_2201)) | ~v2_funct_1(A_2201) | ~v1_funct_1(A_2201) | ~v1_relat_1(A_2201))), inference(superposition, [status(thm), theory('equality')], [c_98, c_30526])).
% 34.75/25.18  tff(c_85663, plain, (k2_funct_1(k2_funct_1('#skF_4'))='#skF_4' | k6_partfun1(k2_relat_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_4')) | k1_relat_1(k2_funct_1('#skF_4'))!=k2_relat_1('#skF_4') | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_79823, c_85654])).
% 34.75/25.18  tff(c_85672, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_127, c_90, c_14897, c_126, c_79823, c_96, c_79823, c_127, c_90, c_80, c_79823, c_3599, c_79906, c_79823, c_3665, c_78134, c_79823, c_85663])).
% 34.75/25.18  tff(c_85674, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_85672])).
% 34.75/25.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 34.75/25.18  
% 34.75/25.18  Inference rules
% 34.75/25.18  ----------------------
% 34.75/25.18  #Ref     : 0
% 34.75/25.18  #Sup     : 17145
% 34.75/25.18  #Fact    : 0
% 34.75/25.18  #Define  : 0
% 34.75/25.18  #Split   : 284
% 34.75/25.18  #Chain   : 0
% 34.75/25.18  #Close   : 0
% 34.75/25.18  
% 34.75/25.18  Ordering : KBO
% 34.75/25.18  
% 34.75/25.18  Simplification rules
% 34.75/25.18  ----------------------
% 34.75/25.18  #Subsume      : 1628
% 34.75/25.18  #Demod        : 43581
% 34.75/25.18  #Tautology    : 5356
% 34.75/25.18  #SimpNegUnit  : 984
% 34.75/25.18  #BackRed      : 849
% 34.75/25.18  
% 34.75/25.18  #Partial instantiations: 0
% 34.75/25.18  #Strategies tried      : 1
% 34.75/25.18  
% 34.75/25.18  Timing (in seconds)
% 34.75/25.18  ----------------------
% 34.75/25.18  Preprocessing        : 0.40
% 34.75/25.18  Parsing              : 0.21
% 34.75/25.18  CNF conversion       : 0.03
% 34.75/25.18  Main loop            : 23.94
% 34.75/25.18  Inferencing          : 4.64
% 34.75/25.18  Reduction            : 14.26
% 34.75/25.18  Demodulation         : 12.39
% 34.75/25.18  BG Simplification    : 0.27
% 34.75/25.18  Subsumption          : 3.84
% 34.75/25.18  Abstraction          : 0.53
% 34.75/25.18  MUC search           : 0.00
% 34.75/25.18  Cooper               : 0.00
% 34.75/25.18  Total                : 24.45
% 34.75/25.18  Index Insertion      : 0.00
% 34.75/25.18  Index Deletion       : 0.00
% 34.75/25.18  Index Matching       : 0.00
% 34.75/25.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
