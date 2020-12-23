%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:24 EST 2020

% Result     : Theorem 6.50s
% Output     : CNFRefutation 6.79s
% Verified   : 
% Statistics : Number of formulae       :  172 (1150 expanded)
%              Number of leaves         :   44 ( 405 expanded)
%              Depth                    :   11
%              Number of atoms          :  327 (3493 expanded)
%              Number of equality atoms :   89 ( 665 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_158,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
             => ( v2_funct_1(C)
                & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_99,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_55,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_93,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_138,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_116,axiom,(
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

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_58,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_128,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_72,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_70,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_50,plain,(
    ! [A_33] : k6_relat_1(A_33) = k6_partfun1(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_26,plain,(
    ! [A_13] : v2_funct_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_73,plain,(
    ! [A_13] : v2_funct_1(k6_partfun1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_26])).

tff(c_42,plain,(
    ! [B_27,D_29,A_26,E_30,F_31,C_28] :
      ( m1_subset_1(k1_partfun1(A_26,B_27,C_28,D_29,E_30,F_31),k1_zfmisc_1(k2_zfmisc_1(A_26,D_29)))
      | ~ m1_subset_1(F_31,k1_zfmisc_1(k2_zfmisc_1(C_28,D_29)))
      | ~ v1_funct_1(F_31)
      | ~ m1_subset_1(E_30,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ v1_funct_1(E_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_48,plain,(
    ! [A_32] : m1_subset_1(k6_partfun1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_60,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_462,plain,(
    ! [D_95,C_96,A_97,B_98] :
      ( D_95 = C_96
      | ~ r2_relset_1(A_97,B_98,C_96,D_95)
      | ~ m1_subset_1(D_95,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98)))
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_468,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_60,c_462])).

tff(c_479,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_468])).

tff(c_503,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_479])).

tff(c_840,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_503])).

tff(c_847,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_66,c_62,c_840])).

tff(c_848,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_479])).

tff(c_1250,plain,(
    ! [D_215,E_212,C_214,B_213,A_211] :
      ( k1_xboole_0 = C_214
      | v2_funct_1(D_215)
      | ~ v2_funct_1(k1_partfun1(A_211,B_213,B_213,C_214,D_215,E_212))
      | ~ m1_subset_1(E_212,k1_zfmisc_1(k2_zfmisc_1(B_213,C_214)))
      | ~ v1_funct_2(E_212,B_213,C_214)
      | ~ v1_funct_1(E_212)
      | ~ m1_subset_1(D_215,k1_zfmisc_1(k2_zfmisc_1(A_211,B_213)))
      | ~ v1_funct_2(D_215,A_211,B_213)
      | ~ v1_funct_1(D_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1252,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_848,c_1250])).

tff(c_1254,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_64,c_62,c_73,c_1252])).

tff(c_1255,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_1254])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1285,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1255,c_8])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1283,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1255,c_1255,c_12])).

tff(c_140,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(A_57,B_58)
      | ~ m1_subset_1(A_57,k1_zfmisc_1(B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_151,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_140])).

tff(c_234,plain,(
    ! [B_65,A_66] :
      ( B_65 = A_66
      | ~ r1_tarski(B_65,A_66)
      | ~ r1_tarski(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_246,plain,
    ( k2_zfmisc_1('#skF_2','#skF_1') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_151,c_234])).

tff(c_257,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_246])).

tff(c_1404,plain,(
    ~ r1_tarski('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1283,c_257])).

tff(c_1409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1285,c_1404])).

tff(c_1410,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_1442,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1410,c_62])).

tff(c_1844,plain,(
    ! [D_282,C_283,A_284,B_285] :
      ( D_282 = C_283
      | ~ r2_relset_1(A_284,B_285,C_283,D_282)
      | ~ m1_subset_1(D_282,k1_zfmisc_1(k2_zfmisc_1(A_284,B_285)))
      | ~ m1_subset_1(C_283,k1_zfmisc_1(k2_zfmisc_1(A_284,B_285))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1856,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_60,c_1844])).

tff(c_1878,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1856])).

tff(c_1900,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1878])).

tff(c_2165,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_1900])).

tff(c_2172,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_66,c_1442,c_1410,c_2165])).

tff(c_2173,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1878])).

tff(c_2570,plain,(
    ! [B_393,E_392,A_391,C_394,D_395] :
      ( k1_xboole_0 = C_394
      | v2_funct_1(D_395)
      | ~ v2_funct_1(k1_partfun1(A_391,B_393,B_393,C_394,D_395,E_392))
      | ~ m1_subset_1(E_392,k1_zfmisc_1(k2_zfmisc_1(B_393,C_394)))
      | ~ v1_funct_2(E_392,B_393,C_394)
      | ~ v1_funct_1(E_392)
      | ~ m1_subset_1(D_395,k1_zfmisc_1(k2_zfmisc_1(A_391,B_393)))
      | ~ v1_funct_2(D_395,A_391,B_393)
      | ~ v1_funct_1(D_395) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_2572,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2173,c_2570])).

tff(c_2574,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_64,c_1442,c_1410,c_73,c_2572])).

tff(c_2575,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_2574])).

tff(c_2613,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2575,c_8])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2610,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2575,c_2575,c_14])).

tff(c_152,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_140])).

tff(c_247,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_152,c_234])).

tff(c_1440,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_247])).

tff(c_2750,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2610,c_1440])).

tff(c_2755,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2613,c_2750])).

tff(c_2756,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_247])).

tff(c_2783,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2756,c_68])).

tff(c_2806,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1410,c_62])).

tff(c_3306,plain,(
    ! [F_481,C_482,E_483,B_479,D_478,A_480] :
      ( m1_subset_1(k1_partfun1(A_480,B_479,C_482,D_478,E_483,F_481),k1_zfmisc_1(k2_zfmisc_1(A_480,D_478)))
      | ~ m1_subset_1(F_481,k1_zfmisc_1(k2_zfmisc_1(C_482,D_478)))
      | ~ v1_funct_1(F_481)
      | ~ m1_subset_1(E_483,k1_zfmisc_1(k2_zfmisc_1(A_480,B_479)))
      | ~ v1_funct_1(E_483) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3113,plain,(
    ! [D_447,C_448,A_449,B_450] :
      ( D_447 = C_448
      | ~ r2_relset_1(A_449,B_450,C_448,D_447)
      | ~ m1_subset_1(D_447,k1_zfmisc_1(k2_zfmisc_1(A_449,B_450)))
      | ~ m1_subset_1(C_448,k1_zfmisc_1(k2_zfmisc_1(A_449,B_450))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3119,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_60,c_3113])).

tff(c_3130,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3119])).

tff(c_3177,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_3130])).

tff(c_3309,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3306,c_3177])).

tff(c_3344,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2783,c_2756,c_66,c_2806,c_1410,c_3309])).

tff(c_3345,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_3130])).

tff(c_3770,plain,(
    ! [C_547,A_544,D_548,E_545,B_546] :
      ( k1_xboole_0 = C_547
      | v2_funct_1(D_548)
      | ~ v2_funct_1(k1_partfun1(A_544,B_546,B_546,C_547,D_548,E_545))
      | ~ m1_subset_1(E_545,k1_zfmisc_1(k2_zfmisc_1(B_546,C_547)))
      | ~ v1_funct_2(E_545,B_546,C_547)
      | ~ v1_funct_1(E_545)
      | ~ m1_subset_1(D_548,k1_zfmisc_1(k2_zfmisc_1(A_544,B_546)))
      | ~ v1_funct_2(D_548,A_544,B_546)
      | ~ v1_funct_1(D_548) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_3772,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3345,c_3770])).

tff(c_3774,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_2783,c_2756,c_66,c_64,c_2806,c_1410,c_73,c_3772])).

tff(c_3775,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_3774])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2817,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1410,c_10])).

tff(c_2862,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2817])).

tff(c_3801,plain,(
    '#skF_1' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3775,c_2862])).

tff(c_4003,plain,(
    ! [A_567] : k2_zfmisc_1(A_567,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3775,c_3775,c_12])).

tff(c_4048,plain,(
    '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_4003,c_1410])).

tff(c_4077,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3801,c_4048])).

tff(c_4079,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2817])).

tff(c_24,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_113,plain,(
    ! [A_54] : k6_relat_1(A_54) = k6_partfun1(A_54) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_125,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_113])).

tff(c_134,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_73])).

tff(c_4086,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4079,c_134])).

tff(c_2794,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2756,c_10])).

tff(c_4125,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_1' = '#skF_4'
    | '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4079,c_4079,c_4079,c_2794])).

tff(c_4126,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_4125])).

tff(c_4090,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4079,c_4079,c_12])).

tff(c_4089,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_4',B_5) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4079,c_4079,c_14])).

tff(c_4078,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2817])).

tff(c_4158,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4079,c_4079,c_4078])).

tff(c_4159,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_4158])).

tff(c_4186,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4159,c_2756])).

tff(c_4263,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4089,c_4186])).

tff(c_4264,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4126,c_4263])).

tff(c_4265,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4158])).

tff(c_4268,plain,(
    k2_zfmisc_1('#skF_1','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4265,c_2756])).

tff(c_4368,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4090,c_4268])).

tff(c_4369,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4126,c_4368])).

tff(c_4371,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4125])).

tff(c_4378,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4371,c_128])).

tff(c_4385,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4086,c_4378])).

tff(c_4386,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_22,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4453,plain,(
    ! [B_586,A_587] :
      ( v1_relat_1(B_586)
      | ~ m1_subset_1(B_586,k1_zfmisc_1(A_587))
      | ~ v1_relat_1(A_587) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4468,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_4453])).

tff(c_4481,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_4468])).

tff(c_4582,plain,(
    ! [C_599,B_600,A_601] :
      ( v5_relat_1(C_599,B_600)
      | ~ m1_subset_1(C_599,k1_zfmisc_1(k2_zfmisc_1(A_601,B_600))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4605,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_4582])).

tff(c_4639,plain,(
    ! [A_610,B_611,D_612] :
      ( r2_relset_1(A_610,B_611,D_612,D_612)
      | ~ m1_subset_1(D_612,k1_zfmisc_1(k2_zfmisc_1(A_610,B_611))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4653,plain,(
    ! [A_32] : r2_relset_1(A_32,A_32,k6_partfun1(A_32),k6_partfun1(A_32)) ),
    inference(resolution,[status(thm)],[c_48,c_4639])).

tff(c_4704,plain,(
    ! [A_621,B_622,C_623] :
      ( k2_relset_1(A_621,B_622,C_623) = k2_relat_1(C_623)
      | ~ m1_subset_1(C_623,k1_zfmisc_1(k2_zfmisc_1(A_621,B_622))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4727,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_4704])).

tff(c_4745,plain,(
    ! [D_625,C_626,A_627,B_628] :
      ( D_625 = C_626
      | ~ r2_relset_1(A_627,B_628,C_626,D_625)
      | ~ m1_subset_1(D_625,k1_zfmisc_1(k2_zfmisc_1(A_627,B_628)))
      | ~ m1_subset_1(C_626,k1_zfmisc_1(k2_zfmisc_1(A_627,B_628))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4753,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_60,c_4745])).

tff(c_4768,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4753])).

tff(c_4809,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_4768])).

tff(c_5155,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_4809])).

tff(c_5162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_66,c_62,c_5155])).

tff(c_5163,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_4768])).

tff(c_5668,plain,(
    ! [A_768,B_769,C_770,D_771] :
      ( k2_relset_1(A_768,B_769,C_770) = B_769
      | ~ r2_relset_1(B_769,B_769,k1_partfun1(B_769,A_768,A_768,B_769,D_771,C_770),k6_partfun1(B_769))
      | ~ m1_subset_1(D_771,k1_zfmisc_1(k2_zfmisc_1(B_769,A_768)))
      | ~ v1_funct_2(D_771,B_769,A_768)
      | ~ v1_funct_1(D_771)
      | ~ m1_subset_1(C_770,k1_zfmisc_1(k2_zfmisc_1(A_768,B_769)))
      | ~ v1_funct_2(C_770,A_768,B_769)
      | ~ v1_funct_1(C_770) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_5671,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5163,c_5668])).

tff(c_5676,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_72,c_70,c_68,c_4653,c_4727,c_5671])).

tff(c_38,plain,(
    ! [B_25] :
      ( v2_funct_2(B_25,k2_relat_1(B_25))
      | ~ v5_relat_1(B_25,k2_relat_1(B_25))
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_5685,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5676,c_38])).

tff(c_5692,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4481,c_4605,c_5676,c_5685])).

tff(c_5694,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4386,c_5692])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:41:29 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.50/2.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.50/2.27  
% 6.50/2.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.50/2.28  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.50/2.28  
% 6.50/2.28  %Foreground sorts:
% 6.50/2.28  
% 6.50/2.28  
% 6.50/2.28  %Background operators:
% 6.50/2.28  
% 6.50/2.28  
% 6.50/2.28  %Foreground operators:
% 6.50/2.28  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.50/2.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.50/2.28  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.50/2.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.50/2.28  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.50/2.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.50/2.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.50/2.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.50/2.28  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.50/2.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.50/2.28  tff('#skF_2', type, '#skF_2': $i).
% 6.50/2.28  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.50/2.28  tff('#skF_3', type, '#skF_3': $i).
% 6.50/2.28  tff('#skF_1', type, '#skF_1': $i).
% 6.50/2.28  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.50/2.28  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.50/2.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.50/2.28  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.50/2.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.50/2.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.50/2.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.50/2.28  tff('#skF_4', type, '#skF_4': $i).
% 6.50/2.28  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.50/2.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.50/2.28  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.50/2.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.50/2.28  
% 6.79/2.30  tff(f_158, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 6.79/2.30  tff(f_99, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.79/2.30  tff(f_55, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 6.79/2.30  tff(f_93, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.79/2.31  tff(f_97, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.79/2.31  tff(f_73, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.79/2.31  tff(f_138, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 6.79/2.31  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.79/2.31  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.79/2.31  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.79/2.31  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.79/2.31  tff(f_53, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 6.79/2.31  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.79/2.31  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.79/2.31  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.79/2.31  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.79/2.31  tff(f_116, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 6.79/2.31  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 6.79/2.31  tff(c_58, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.79/2.31  tff(c_128, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_58])).
% 6.79/2.31  tff(c_72, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.79/2.31  tff(c_70, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.79/2.31  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.79/2.31  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.79/2.31  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.79/2.31  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.79/2.31  tff(c_50, plain, (![A_33]: (k6_relat_1(A_33)=k6_partfun1(A_33))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.79/2.31  tff(c_26, plain, (![A_13]: (v2_funct_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.79/2.31  tff(c_73, plain, (![A_13]: (v2_funct_1(k6_partfun1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_26])).
% 6.79/2.31  tff(c_42, plain, (![B_27, D_29, A_26, E_30, F_31, C_28]: (m1_subset_1(k1_partfun1(A_26, B_27, C_28, D_29, E_30, F_31), k1_zfmisc_1(k2_zfmisc_1(A_26, D_29))) | ~m1_subset_1(F_31, k1_zfmisc_1(k2_zfmisc_1(C_28, D_29))) | ~v1_funct_1(F_31) | ~m1_subset_1(E_30, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~v1_funct_1(E_30))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.79/2.31  tff(c_48, plain, (![A_32]: (m1_subset_1(k6_partfun1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.79/2.31  tff(c_60, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.79/2.31  tff(c_462, plain, (![D_95, C_96, A_97, B_98]: (D_95=C_96 | ~r2_relset_1(A_97, B_98, C_96, D_95) | ~m1_subset_1(D_95, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.79/2.31  tff(c_468, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_60, c_462])).
% 6.79/2.31  tff(c_479, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_468])).
% 6.79/2.31  tff(c_503, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_479])).
% 6.79/2.31  tff(c_840, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_503])).
% 6.79/2.31  tff(c_847, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_66, c_62, c_840])).
% 6.79/2.31  tff(c_848, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_479])).
% 6.79/2.31  tff(c_1250, plain, (![D_215, E_212, C_214, B_213, A_211]: (k1_xboole_0=C_214 | v2_funct_1(D_215) | ~v2_funct_1(k1_partfun1(A_211, B_213, B_213, C_214, D_215, E_212)) | ~m1_subset_1(E_212, k1_zfmisc_1(k2_zfmisc_1(B_213, C_214))) | ~v1_funct_2(E_212, B_213, C_214) | ~v1_funct_1(E_212) | ~m1_subset_1(D_215, k1_zfmisc_1(k2_zfmisc_1(A_211, B_213))) | ~v1_funct_2(D_215, A_211, B_213) | ~v1_funct_1(D_215))), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.79/2.31  tff(c_1252, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_848, c_1250])).
% 6.79/2.31  tff(c_1254, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_64, c_62, c_73, c_1252])).
% 6.79/2.31  tff(c_1255, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_128, c_1254])).
% 6.79/2.31  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.79/2.31  tff(c_1285, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1255, c_8])).
% 6.79/2.31  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.79/2.31  tff(c_1283, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1255, c_1255, c_12])).
% 6.79/2.31  tff(c_140, plain, (![A_57, B_58]: (r1_tarski(A_57, B_58) | ~m1_subset_1(A_57, k1_zfmisc_1(B_58)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.79/2.31  tff(c_151, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_62, c_140])).
% 6.79/2.31  tff(c_234, plain, (![B_65, A_66]: (B_65=A_66 | ~r1_tarski(B_65, A_66) | ~r1_tarski(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.79/2.31  tff(c_246, plain, (k2_zfmisc_1('#skF_2', '#skF_1')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), '#skF_4')), inference(resolution, [status(thm)], [c_151, c_234])).
% 6.79/2.31  tff(c_257, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), '#skF_4')), inference(splitLeft, [status(thm)], [c_246])).
% 6.79/2.31  tff(c_1404, plain, (~r1_tarski('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1283, c_257])).
% 6.79/2.31  tff(c_1409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1285, c_1404])).
% 6.79/2.31  tff(c_1410, plain, (k2_zfmisc_1('#skF_2', '#skF_1')='#skF_4'), inference(splitRight, [status(thm)], [c_246])).
% 6.79/2.31  tff(c_1442, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1410, c_62])).
% 6.79/2.31  tff(c_1844, plain, (![D_282, C_283, A_284, B_285]: (D_282=C_283 | ~r2_relset_1(A_284, B_285, C_283, D_282) | ~m1_subset_1(D_282, k1_zfmisc_1(k2_zfmisc_1(A_284, B_285))) | ~m1_subset_1(C_283, k1_zfmisc_1(k2_zfmisc_1(A_284, B_285))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.79/2.31  tff(c_1856, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_60, c_1844])).
% 6.79/2.31  tff(c_1878, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1856])).
% 6.79/2.31  tff(c_1900, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1878])).
% 6.79/2.31  tff(c_2165, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_1900])).
% 6.79/2.31  tff(c_2172, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_66, c_1442, c_1410, c_2165])).
% 6.79/2.31  tff(c_2173, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1878])).
% 6.79/2.31  tff(c_2570, plain, (![B_393, E_392, A_391, C_394, D_395]: (k1_xboole_0=C_394 | v2_funct_1(D_395) | ~v2_funct_1(k1_partfun1(A_391, B_393, B_393, C_394, D_395, E_392)) | ~m1_subset_1(E_392, k1_zfmisc_1(k2_zfmisc_1(B_393, C_394))) | ~v1_funct_2(E_392, B_393, C_394) | ~v1_funct_1(E_392) | ~m1_subset_1(D_395, k1_zfmisc_1(k2_zfmisc_1(A_391, B_393))) | ~v1_funct_2(D_395, A_391, B_393) | ~v1_funct_1(D_395))), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.79/2.31  tff(c_2572, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2173, c_2570])).
% 6.79/2.31  tff(c_2574, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_64, c_1442, c_1410, c_73, c_2572])).
% 6.79/2.31  tff(c_2575, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_128, c_2574])).
% 6.79/2.31  tff(c_2613, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2575, c_8])).
% 6.79/2.31  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.79/2.31  tff(c_2610, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2575, c_2575, c_14])).
% 6.79/2.31  tff(c_152, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_68, c_140])).
% 6.79/2.31  tff(c_247, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_152, c_234])).
% 6.79/2.31  tff(c_1440, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_247])).
% 6.79/2.31  tff(c_2750, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2610, c_1440])).
% 6.79/2.31  tff(c_2755, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2613, c_2750])).
% 6.79/2.31  tff(c_2756, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_247])).
% 6.79/2.31  tff(c_2783, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2756, c_68])).
% 6.79/2.31  tff(c_2806, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1410, c_62])).
% 6.79/2.31  tff(c_3306, plain, (![F_481, C_482, E_483, B_479, D_478, A_480]: (m1_subset_1(k1_partfun1(A_480, B_479, C_482, D_478, E_483, F_481), k1_zfmisc_1(k2_zfmisc_1(A_480, D_478))) | ~m1_subset_1(F_481, k1_zfmisc_1(k2_zfmisc_1(C_482, D_478))) | ~v1_funct_1(F_481) | ~m1_subset_1(E_483, k1_zfmisc_1(k2_zfmisc_1(A_480, B_479))) | ~v1_funct_1(E_483))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.79/2.31  tff(c_3113, plain, (![D_447, C_448, A_449, B_450]: (D_447=C_448 | ~r2_relset_1(A_449, B_450, C_448, D_447) | ~m1_subset_1(D_447, k1_zfmisc_1(k2_zfmisc_1(A_449, B_450))) | ~m1_subset_1(C_448, k1_zfmisc_1(k2_zfmisc_1(A_449, B_450))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.79/2.31  tff(c_3119, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_60, c_3113])).
% 6.79/2.31  tff(c_3130, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_3119])).
% 6.79/2.31  tff(c_3177, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_3130])).
% 6.79/2.31  tff(c_3309, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_3306, c_3177])).
% 6.79/2.31  tff(c_3344, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_2783, c_2756, c_66, c_2806, c_1410, c_3309])).
% 6.79/2.31  tff(c_3345, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_3130])).
% 6.79/2.31  tff(c_3770, plain, (![C_547, A_544, D_548, E_545, B_546]: (k1_xboole_0=C_547 | v2_funct_1(D_548) | ~v2_funct_1(k1_partfun1(A_544, B_546, B_546, C_547, D_548, E_545)) | ~m1_subset_1(E_545, k1_zfmisc_1(k2_zfmisc_1(B_546, C_547))) | ~v1_funct_2(E_545, B_546, C_547) | ~v1_funct_1(E_545) | ~m1_subset_1(D_548, k1_zfmisc_1(k2_zfmisc_1(A_544, B_546))) | ~v1_funct_2(D_548, A_544, B_546) | ~v1_funct_1(D_548))), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.79/2.31  tff(c_3772, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3345, c_3770])).
% 6.79/2.31  tff(c_3774, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_2783, c_2756, c_66, c_64, c_2806, c_1410, c_73, c_3772])).
% 6.79/2.31  tff(c_3775, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_128, c_3774])).
% 6.79/2.31  tff(c_10, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.79/2.31  tff(c_2817, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1410, c_10])).
% 6.79/2.31  tff(c_2862, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_2817])).
% 6.79/2.31  tff(c_3801, plain, ('#skF_1'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3775, c_2862])).
% 6.79/2.31  tff(c_4003, plain, (![A_567]: (k2_zfmisc_1(A_567, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3775, c_3775, c_12])).
% 6.79/2.31  tff(c_4048, plain, ('#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_4003, c_1410])).
% 6.79/2.31  tff(c_4077, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3801, c_4048])).
% 6.79/2.31  tff(c_4079, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_2817])).
% 6.79/2.31  tff(c_24, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.79/2.31  tff(c_113, plain, (![A_54]: (k6_relat_1(A_54)=k6_partfun1(A_54))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.79/2.31  tff(c_125, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_24, c_113])).
% 6.79/2.31  tff(c_134, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_125, c_73])).
% 6.79/2.31  tff(c_4086, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4079, c_134])).
% 6.79/2.31  tff(c_2794, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2756, c_10])).
% 6.79/2.31  tff(c_4125, plain, ('#skF_2'='#skF_4' | '#skF_1'='#skF_4' | '#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4079, c_4079, c_4079, c_2794])).
% 6.79/2.31  tff(c_4126, plain, ('#skF_3'!='#skF_4'), inference(splitLeft, [status(thm)], [c_4125])).
% 6.79/2.31  tff(c_4090, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4079, c_4079, c_12])).
% 6.79/2.31  tff(c_4089, plain, (![B_5]: (k2_zfmisc_1('#skF_4', B_5)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4079, c_4079, c_14])).
% 6.79/2.31  tff(c_4078, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_2817])).
% 6.79/2.31  tff(c_4158, plain, ('#skF_2'='#skF_4' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4079, c_4079, c_4078])).
% 6.79/2.31  tff(c_4159, plain, ('#skF_1'='#skF_4'), inference(splitLeft, [status(thm)], [c_4158])).
% 6.79/2.31  tff(c_4186, plain, (k2_zfmisc_1('#skF_4', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4159, c_2756])).
% 6.79/2.31  tff(c_4263, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4089, c_4186])).
% 6.79/2.31  tff(c_4264, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4126, c_4263])).
% 6.79/2.31  tff(c_4265, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_4158])).
% 6.79/2.31  tff(c_4268, plain, (k2_zfmisc_1('#skF_1', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4265, c_2756])).
% 6.79/2.31  tff(c_4368, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4090, c_4268])).
% 6.79/2.31  tff(c_4369, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4126, c_4368])).
% 6.79/2.31  tff(c_4371, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_4125])).
% 6.79/2.31  tff(c_4378, plain, (~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4371, c_128])).
% 6.79/2.31  tff(c_4385, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4086, c_4378])).
% 6.79/2.31  tff(c_4386, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_58])).
% 6.79/2.31  tff(c_22, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.79/2.31  tff(c_4453, plain, (![B_586, A_587]: (v1_relat_1(B_586) | ~m1_subset_1(B_586, k1_zfmisc_1(A_587)) | ~v1_relat_1(A_587))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.79/2.31  tff(c_4468, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_62, c_4453])).
% 6.79/2.31  tff(c_4481, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_4468])).
% 6.79/2.31  tff(c_4582, plain, (![C_599, B_600, A_601]: (v5_relat_1(C_599, B_600) | ~m1_subset_1(C_599, k1_zfmisc_1(k2_zfmisc_1(A_601, B_600))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.79/2.31  tff(c_4605, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_4582])).
% 6.79/2.31  tff(c_4639, plain, (![A_610, B_611, D_612]: (r2_relset_1(A_610, B_611, D_612, D_612) | ~m1_subset_1(D_612, k1_zfmisc_1(k2_zfmisc_1(A_610, B_611))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.79/2.31  tff(c_4653, plain, (![A_32]: (r2_relset_1(A_32, A_32, k6_partfun1(A_32), k6_partfun1(A_32)))), inference(resolution, [status(thm)], [c_48, c_4639])).
% 6.79/2.31  tff(c_4704, plain, (![A_621, B_622, C_623]: (k2_relset_1(A_621, B_622, C_623)=k2_relat_1(C_623) | ~m1_subset_1(C_623, k1_zfmisc_1(k2_zfmisc_1(A_621, B_622))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.79/2.31  tff(c_4727, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_4704])).
% 6.79/2.31  tff(c_4745, plain, (![D_625, C_626, A_627, B_628]: (D_625=C_626 | ~r2_relset_1(A_627, B_628, C_626, D_625) | ~m1_subset_1(D_625, k1_zfmisc_1(k2_zfmisc_1(A_627, B_628))) | ~m1_subset_1(C_626, k1_zfmisc_1(k2_zfmisc_1(A_627, B_628))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.79/2.31  tff(c_4753, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_60, c_4745])).
% 6.79/2.31  tff(c_4768, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4753])).
% 6.79/2.31  tff(c_4809, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_4768])).
% 6.79/2.31  tff(c_5155, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_4809])).
% 6.79/2.31  tff(c_5162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_66, c_62, c_5155])).
% 6.79/2.31  tff(c_5163, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_4768])).
% 6.79/2.31  tff(c_5668, plain, (![A_768, B_769, C_770, D_771]: (k2_relset_1(A_768, B_769, C_770)=B_769 | ~r2_relset_1(B_769, B_769, k1_partfun1(B_769, A_768, A_768, B_769, D_771, C_770), k6_partfun1(B_769)) | ~m1_subset_1(D_771, k1_zfmisc_1(k2_zfmisc_1(B_769, A_768))) | ~v1_funct_2(D_771, B_769, A_768) | ~v1_funct_1(D_771) | ~m1_subset_1(C_770, k1_zfmisc_1(k2_zfmisc_1(A_768, B_769))) | ~v1_funct_2(C_770, A_768, B_769) | ~v1_funct_1(C_770))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.79/2.31  tff(c_5671, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5163, c_5668])).
% 6.79/2.31  tff(c_5676, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_72, c_70, c_68, c_4653, c_4727, c_5671])).
% 6.79/2.31  tff(c_38, plain, (![B_25]: (v2_funct_2(B_25, k2_relat_1(B_25)) | ~v5_relat_1(B_25, k2_relat_1(B_25)) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.79/2.31  tff(c_5685, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5676, c_38])).
% 6.79/2.31  tff(c_5692, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4481, c_4605, c_5676, c_5685])).
% 6.79/2.31  tff(c_5694, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4386, c_5692])).
% 6.79/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.79/2.31  
% 6.79/2.31  Inference rules
% 6.79/2.31  ----------------------
% 6.79/2.31  #Ref     : 0
% 6.79/2.31  #Sup     : 1244
% 6.79/2.31  #Fact    : 0
% 6.79/2.31  #Define  : 0
% 6.79/2.31  #Split   : 25
% 6.79/2.31  #Chain   : 0
% 6.79/2.31  #Close   : 0
% 6.79/2.31  
% 6.79/2.31  Ordering : KBO
% 6.79/2.31  
% 6.79/2.31  Simplification rules
% 6.79/2.31  ----------------------
% 6.79/2.31  #Subsume      : 91
% 6.79/2.31  #Demod        : 1065
% 6.79/2.31  #Tautology    : 586
% 6.79/2.31  #SimpNegUnit  : 8
% 6.79/2.31  #BackRed      : 163
% 6.79/2.31  
% 6.79/2.31  #Partial instantiations: 0
% 6.79/2.31  #Strategies tried      : 1
% 6.79/2.31  
% 6.79/2.31  Timing (in seconds)
% 6.79/2.31  ----------------------
% 6.79/2.31  Preprocessing        : 0.38
% 6.79/2.31  Parsing              : 0.21
% 6.79/2.31  CNF conversion       : 0.03
% 6.79/2.31  Main loop            : 1.18
% 6.79/2.31  Inferencing          : 0.41
% 6.79/2.31  Reduction            : 0.44
% 6.79/2.31  Demodulation         : 0.32
% 6.79/2.31  BG Simplification    : 0.04
% 6.79/2.31  Subsumption          : 0.19
% 6.79/2.31  Abstraction          : 0.05
% 6.79/2.31  MUC search           : 0.00
% 6.79/2.31  Cooper               : 0.00
% 6.79/2.31  Total                : 1.62
% 6.79/2.31  Index Insertion      : 0.00
% 6.79/2.31  Index Deletion       : 0.00
% 6.79/2.31  Index Matching       : 0.00
% 6.79/2.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
