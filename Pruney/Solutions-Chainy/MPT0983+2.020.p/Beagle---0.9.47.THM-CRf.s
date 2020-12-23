%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:03 EST 2020

% Result     : Theorem 3.89s
% Output     : CNFRefutation 4.08s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 232 expanded)
%              Number of leaves         :   42 ( 102 expanded)
%              Depth                    :    9
%              Number of atoms          :  211 ( 758 expanded)
%              Number of equality atoms :   25 (  48 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_165,negated_conjecture,(
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

tff(f_51,axiom,(
    ! [A] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_106,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_100,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_104,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_145,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_33,axiom,(
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

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_123,axiom,(
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

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_66,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_89,plain,(
    ! [A_53] :
      ( v2_funct_1(A_53)
      | ~ v1_funct_1(A_53)
      | ~ v1_relat_1(A_53)
      | ~ v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_52,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_87,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_92,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_89,c_87])).

tff(c_95,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_92])).

tff(c_96,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_62,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_144,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_xboole_0(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66)))
      | ~ v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_153,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_144])).

tff(c_158,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_153])).

tff(c_64,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_58,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_44,plain,(
    ! [A_32] : k6_relat_1(A_32) = k6_partfun1(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_18,plain,(
    ! [A_8] : v2_funct_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_67,plain,(
    ! [A_8] : v2_funct_1(k6_partfun1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_18])).

tff(c_305,plain,(
    ! [E_104,D_99,F_102,B_103,C_101,A_100] :
      ( m1_subset_1(k1_partfun1(A_100,B_103,C_101,D_99,E_104,F_102),k1_zfmisc_1(k2_zfmisc_1(A_100,D_99)))
      | ~ m1_subset_1(F_102,k1_zfmisc_1(k2_zfmisc_1(C_101,D_99)))
      | ~ v1_funct_1(F_102)
      | ~ m1_subset_1(E_104,k1_zfmisc_1(k2_zfmisc_1(A_100,B_103)))
      | ~ v1_funct_1(E_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_42,plain,(
    ! [A_31] : m1_subset_1(k6_partfun1(A_31),k1_zfmisc_1(k2_zfmisc_1(A_31,A_31))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_54,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_230,plain,(
    ! [D_81,C_82,A_83,B_84] :
      ( D_81 = C_82
      | ~ r2_relset_1(A_83,B_84,C_82,D_81)
      | ~ m1_subset_1(D_81,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84)))
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_238,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_54,c_230])).

tff(c_253,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_238])).

tff(c_254,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_253])).

tff(c_314,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_305,c_254])).

tff(c_339,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_60,c_56,c_314])).

tff(c_340,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_253])).

tff(c_547,plain,(
    ! [D_162,C_161,A_159,E_163,B_160] :
      ( k1_xboole_0 = C_161
      | v2_funct_1(D_162)
      | ~ v2_funct_1(k1_partfun1(A_159,B_160,B_160,C_161,D_162,E_163))
      | ~ m1_subset_1(E_163,k1_zfmisc_1(k2_zfmisc_1(B_160,C_161)))
      | ~ v1_funct_2(E_163,B_160,C_161)
      | ~ v1_funct_1(E_163)
      | ~ m1_subset_1(D_162,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160)))
      | ~ v1_funct_2(D_162,A_159,B_160)
      | ~ v1_funct_1(D_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_549,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_340,c_547])).

tff(c_554,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_58,c_56,c_67,c_549])).

tff(c_555,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_554])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_560,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_555,c_2])).

tff(c_562,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_158,c_560])).

tff(c_563,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_6,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_570,plain,(
    ! [B_164,A_165] :
      ( v1_relat_1(B_164)
      | ~ m1_subset_1(B_164,k1_zfmisc_1(A_165))
      | ~ v1_relat_1(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_579,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_62,c_570])).

tff(c_588,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_579])).

tff(c_590,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_563,c_588])).

tff(c_591,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_595,plain,(
    ! [B_168,A_169] :
      ( v1_relat_1(B_168)
      | ~ m1_subset_1(B_168,k1_zfmisc_1(A_169))
      | ~ v1_relat_1(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_601,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_56,c_595])).

tff(c_610,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_601])).

tff(c_628,plain,(
    ! [C_174,B_175,A_176] :
      ( v5_relat_1(C_174,B_175)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_176,B_175))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_639,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_628])).

tff(c_664,plain,(
    ! [A_184,B_185,D_186] :
      ( r2_relset_1(A_184,B_185,D_186,D_186)
      | ~ m1_subset_1(D_186,k1_zfmisc_1(k2_zfmisc_1(A_184,B_185))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_671,plain,(
    ! [A_31] : r2_relset_1(A_31,A_31,k6_partfun1(A_31),k6_partfun1(A_31)) ),
    inference(resolution,[status(thm)],[c_42,c_664])).

tff(c_696,plain,(
    ! [A_191,B_192,C_193] :
      ( k2_relset_1(A_191,B_192,C_193) = k2_relat_1(C_193)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(A_191,B_192))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_707,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_696])).

tff(c_782,plain,(
    ! [B_212,A_209,C_210,D_208,E_213,F_211] :
      ( m1_subset_1(k1_partfun1(A_209,B_212,C_210,D_208,E_213,F_211),k1_zfmisc_1(k2_zfmisc_1(A_209,D_208)))
      | ~ m1_subset_1(F_211,k1_zfmisc_1(k2_zfmisc_1(C_210,D_208)))
      | ~ v1_funct_1(F_211)
      | ~ m1_subset_1(E_213,k1_zfmisc_1(k2_zfmisc_1(A_209,B_212)))
      | ~ v1_funct_1(E_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_726,plain,(
    ! [D_195,C_196,A_197,B_198] :
      ( D_195 = C_196
      | ~ r2_relset_1(A_197,B_198,C_196,D_195)
      | ~ m1_subset_1(D_195,k1_zfmisc_1(k2_zfmisc_1(A_197,B_198)))
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(A_197,B_198))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_734,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_54,c_726])).

tff(c_749,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_734])).

tff(c_750,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_749])).

tff(c_790,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_782,c_750])).

tff(c_813,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_60,c_56,c_790])).

tff(c_814,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_749])).

tff(c_1118,plain,(
    ! [A_287,B_288,C_289,D_290] :
      ( k2_relset_1(A_287,B_288,C_289) = B_288
      | ~ r2_relset_1(B_288,B_288,k1_partfun1(B_288,A_287,A_287,B_288,D_290,C_289),k6_partfun1(B_288))
      | ~ m1_subset_1(D_290,k1_zfmisc_1(k2_zfmisc_1(B_288,A_287)))
      | ~ v1_funct_2(D_290,B_288,A_287)
      | ~ v1_funct_1(D_290)
      | ~ m1_subset_1(C_289,k1_zfmisc_1(k2_zfmisc_1(A_287,B_288)))
      | ~ v1_funct_2(C_289,A_287,B_288)
      | ~ v1_funct_1(C_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1121,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_814,c_1118])).

tff(c_1123,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_66,c_64,c_62,c_671,c_707,c_1121])).

tff(c_32,plain,(
    ! [B_24] :
      ( v2_funct_2(B_24,k2_relat_1(B_24))
      | ~ v5_relat_1(B_24,k2_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1128,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1123,c_32])).

tff(c_1132,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_610,c_639,c_1123,c_1128])).

tff(c_1134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_591,c_1132])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:10:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.89/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.89/1.65  
% 3.89/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.89/1.65  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.89/1.65  
% 3.89/1.65  %Foreground sorts:
% 3.89/1.65  
% 3.89/1.65  
% 3.89/1.65  %Background operators:
% 3.89/1.65  
% 3.89/1.65  
% 3.89/1.65  %Foreground operators:
% 3.89/1.65  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.89/1.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.89/1.65  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.89/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.89/1.65  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.89/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.89/1.65  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.89/1.65  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.89/1.65  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.89/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.89/1.65  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.89/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.89/1.65  tff('#skF_1', type, '#skF_1': $i).
% 3.89/1.65  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 3.89/1.65  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.89/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.89/1.65  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.89/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.89/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.89/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.89/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.89/1.65  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.89/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.89/1.65  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.89/1.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.89/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.89/1.65  
% 4.08/1.67  tff(f_165, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 4.08/1.67  tff(f_51, axiom, (![A]: (((v1_xboole_0(A) & v1_relat_1(A)) & v1_funct_1(A)) => ((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_1)).
% 4.08/1.67  tff(f_68, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 4.08/1.67  tff(f_106, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.08/1.67  tff(f_55, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.08/1.67  tff(f_100, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.08/1.67  tff(f_104, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.08/1.67  tff(f_80, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.08/1.67  tff(f_145, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 4.08/1.67  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.08/1.67  tff(f_35, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.08/1.67  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.08/1.67  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.08/1.67  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.08/1.67  tff(f_123, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 4.08/1.67  tff(f_88, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 4.08/1.67  tff(c_66, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 4.08/1.67  tff(c_89, plain, (![A_53]: (v2_funct_1(A_53) | ~v1_funct_1(A_53) | ~v1_relat_1(A_53) | ~v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.08/1.67  tff(c_52, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 4.08/1.67  tff(c_87, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_52])).
% 4.08/1.67  tff(c_92, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_89, c_87])).
% 4.08/1.67  tff(c_95, plain, (~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_92])).
% 4.08/1.67  tff(c_96, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_95])).
% 4.08/1.67  tff(c_62, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 4.08/1.67  tff(c_144, plain, (![C_64, A_65, B_66]: (v1_xboole_0(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))) | ~v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.08/1.67  tff(c_153, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_62, c_144])).
% 4.08/1.67  tff(c_158, plain, (~v1_xboole_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_96, c_153])).
% 4.08/1.67  tff(c_64, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 4.08/1.67  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_165])).
% 4.08/1.67  tff(c_58, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_165])).
% 4.08/1.67  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 4.08/1.67  tff(c_44, plain, (![A_32]: (k6_relat_1(A_32)=k6_partfun1(A_32))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.08/1.67  tff(c_18, plain, (![A_8]: (v2_funct_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.08/1.67  tff(c_67, plain, (![A_8]: (v2_funct_1(k6_partfun1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_18])).
% 4.08/1.67  tff(c_305, plain, (![E_104, D_99, F_102, B_103, C_101, A_100]: (m1_subset_1(k1_partfun1(A_100, B_103, C_101, D_99, E_104, F_102), k1_zfmisc_1(k2_zfmisc_1(A_100, D_99))) | ~m1_subset_1(F_102, k1_zfmisc_1(k2_zfmisc_1(C_101, D_99))) | ~v1_funct_1(F_102) | ~m1_subset_1(E_104, k1_zfmisc_1(k2_zfmisc_1(A_100, B_103))) | ~v1_funct_1(E_104))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.08/1.67  tff(c_42, plain, (![A_31]: (m1_subset_1(k6_partfun1(A_31), k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.08/1.67  tff(c_54, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 4.08/1.67  tff(c_230, plain, (![D_81, C_82, A_83, B_84]: (D_81=C_82 | ~r2_relset_1(A_83, B_84, C_82, D_81) | ~m1_subset_1(D_81, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.08/1.67  tff(c_238, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_54, c_230])).
% 4.08/1.67  tff(c_253, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_238])).
% 4.08/1.67  tff(c_254, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_253])).
% 4.08/1.67  tff(c_314, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_305, c_254])).
% 4.08/1.67  tff(c_339, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_60, c_56, c_314])).
% 4.08/1.67  tff(c_340, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_253])).
% 4.08/1.67  tff(c_547, plain, (![D_162, C_161, A_159, E_163, B_160]: (k1_xboole_0=C_161 | v2_funct_1(D_162) | ~v2_funct_1(k1_partfun1(A_159, B_160, B_160, C_161, D_162, E_163)) | ~m1_subset_1(E_163, k1_zfmisc_1(k2_zfmisc_1(B_160, C_161))) | ~v1_funct_2(E_163, B_160, C_161) | ~v1_funct_1(E_163) | ~m1_subset_1(D_162, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))) | ~v1_funct_2(D_162, A_159, B_160) | ~v1_funct_1(D_162))), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.08/1.67  tff(c_549, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_340, c_547])).
% 4.08/1.67  tff(c_554, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_58, c_56, c_67, c_549])).
% 4.08/1.67  tff(c_555, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_87, c_554])).
% 4.08/1.67  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.08/1.67  tff(c_560, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_555, c_2])).
% 4.08/1.67  tff(c_562, plain, $false, inference(negUnitSimplification, [status(thm)], [c_158, c_560])).
% 4.08/1.67  tff(c_563, plain, (~v1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_95])).
% 4.08/1.67  tff(c_6, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.08/1.67  tff(c_570, plain, (![B_164, A_165]: (v1_relat_1(B_164) | ~m1_subset_1(B_164, k1_zfmisc_1(A_165)) | ~v1_relat_1(A_165))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.08/1.67  tff(c_579, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_62, c_570])).
% 4.08/1.67  tff(c_588, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_579])).
% 4.08/1.67  tff(c_590, plain, $false, inference(negUnitSimplification, [status(thm)], [c_563, c_588])).
% 4.08/1.67  tff(c_591, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_52])).
% 4.08/1.67  tff(c_595, plain, (![B_168, A_169]: (v1_relat_1(B_168) | ~m1_subset_1(B_168, k1_zfmisc_1(A_169)) | ~v1_relat_1(A_169))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.08/1.67  tff(c_601, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_56, c_595])).
% 4.08/1.67  tff(c_610, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_601])).
% 4.08/1.67  tff(c_628, plain, (![C_174, B_175, A_176]: (v5_relat_1(C_174, B_175) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_176, B_175))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.08/1.67  tff(c_639, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_56, c_628])).
% 4.08/1.67  tff(c_664, plain, (![A_184, B_185, D_186]: (r2_relset_1(A_184, B_185, D_186, D_186) | ~m1_subset_1(D_186, k1_zfmisc_1(k2_zfmisc_1(A_184, B_185))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.08/1.67  tff(c_671, plain, (![A_31]: (r2_relset_1(A_31, A_31, k6_partfun1(A_31), k6_partfun1(A_31)))), inference(resolution, [status(thm)], [c_42, c_664])).
% 4.08/1.67  tff(c_696, plain, (![A_191, B_192, C_193]: (k2_relset_1(A_191, B_192, C_193)=k2_relat_1(C_193) | ~m1_subset_1(C_193, k1_zfmisc_1(k2_zfmisc_1(A_191, B_192))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.08/1.67  tff(c_707, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_696])).
% 4.08/1.67  tff(c_782, plain, (![B_212, A_209, C_210, D_208, E_213, F_211]: (m1_subset_1(k1_partfun1(A_209, B_212, C_210, D_208, E_213, F_211), k1_zfmisc_1(k2_zfmisc_1(A_209, D_208))) | ~m1_subset_1(F_211, k1_zfmisc_1(k2_zfmisc_1(C_210, D_208))) | ~v1_funct_1(F_211) | ~m1_subset_1(E_213, k1_zfmisc_1(k2_zfmisc_1(A_209, B_212))) | ~v1_funct_1(E_213))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.08/1.67  tff(c_726, plain, (![D_195, C_196, A_197, B_198]: (D_195=C_196 | ~r2_relset_1(A_197, B_198, C_196, D_195) | ~m1_subset_1(D_195, k1_zfmisc_1(k2_zfmisc_1(A_197, B_198))) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(A_197, B_198))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.08/1.67  tff(c_734, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_54, c_726])).
% 4.08/1.67  tff(c_749, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_734])).
% 4.08/1.67  tff(c_750, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_749])).
% 4.08/1.67  tff(c_790, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_782, c_750])).
% 4.08/1.67  tff(c_813, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_60, c_56, c_790])).
% 4.08/1.67  tff(c_814, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_749])).
% 4.08/1.67  tff(c_1118, plain, (![A_287, B_288, C_289, D_290]: (k2_relset_1(A_287, B_288, C_289)=B_288 | ~r2_relset_1(B_288, B_288, k1_partfun1(B_288, A_287, A_287, B_288, D_290, C_289), k6_partfun1(B_288)) | ~m1_subset_1(D_290, k1_zfmisc_1(k2_zfmisc_1(B_288, A_287))) | ~v1_funct_2(D_290, B_288, A_287) | ~v1_funct_1(D_290) | ~m1_subset_1(C_289, k1_zfmisc_1(k2_zfmisc_1(A_287, B_288))) | ~v1_funct_2(C_289, A_287, B_288) | ~v1_funct_1(C_289))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.08/1.67  tff(c_1121, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_814, c_1118])).
% 4.08/1.67  tff(c_1123, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_66, c_64, c_62, c_671, c_707, c_1121])).
% 4.08/1.67  tff(c_32, plain, (![B_24]: (v2_funct_2(B_24, k2_relat_1(B_24)) | ~v5_relat_1(B_24, k2_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.08/1.67  tff(c_1128, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1123, c_32])).
% 4.08/1.67  tff(c_1132, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_610, c_639, c_1123, c_1128])).
% 4.08/1.67  tff(c_1134, plain, $false, inference(negUnitSimplification, [status(thm)], [c_591, c_1132])).
% 4.08/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.08/1.67  
% 4.08/1.67  Inference rules
% 4.08/1.67  ----------------------
% 4.08/1.67  #Ref     : 0
% 4.08/1.67  #Sup     : 215
% 4.08/1.67  #Fact    : 0
% 4.08/1.67  #Define  : 0
% 4.08/1.67  #Split   : 11
% 4.08/1.67  #Chain   : 0
% 4.08/1.67  #Close   : 0
% 4.08/1.67  
% 4.08/1.67  Ordering : KBO
% 4.08/1.67  
% 4.08/1.67  Simplification rules
% 4.08/1.67  ----------------------
% 4.08/1.67  #Subsume      : 1
% 4.08/1.67  #Demod        : 153
% 4.08/1.67  #Tautology    : 41
% 4.08/1.67  #SimpNegUnit  : 5
% 4.08/1.67  #BackRed      : 7
% 4.08/1.67  
% 4.08/1.67  #Partial instantiations: 0
% 4.08/1.67  #Strategies tried      : 1
% 4.08/1.67  
% 4.08/1.67  Timing (in seconds)
% 4.08/1.67  ----------------------
% 4.08/1.67  Preprocessing        : 0.37
% 4.08/1.67  Parsing              : 0.19
% 4.08/1.67  CNF conversion       : 0.03
% 4.08/1.67  Main loop            : 0.49
% 4.08/1.67  Inferencing          : 0.19
% 4.08/1.67  Reduction            : 0.15
% 4.08/1.67  Demodulation         : 0.11
% 4.08/1.67  BG Simplification    : 0.02
% 4.08/1.67  Subsumption          : 0.08
% 4.08/1.67  Abstraction          : 0.02
% 4.08/1.67  MUC search           : 0.00
% 4.08/1.67  Cooper               : 0.00
% 4.08/1.67  Total                : 0.89
% 4.08/1.67  Index Insertion      : 0.00
% 4.08/1.67  Index Deletion       : 0.00
% 4.08/1.68  Index Matching       : 0.00
% 4.08/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
