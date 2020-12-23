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
% DateTime   : Thu Dec  3 10:12:56 EST 2020

% Result     : Theorem 14.81s
% Output     : CNFRefutation 15.04s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 841 expanded)
%              Number of leaves         :   48 ( 334 expanded)
%              Depth                    :   19
%              Number of atoms          :  357 (3515 expanded)
%              Number of equality atoms :  103 (1137 expanded)
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

tff(f_208,negated_conjecture,(
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

tff(f_124,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_166,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_51,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_182,axiom,(
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

tff(f_100,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_90,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_110,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
          & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_154,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_150,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_138,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_164,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_130,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
           => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).

tff(c_70,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_82,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_143,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_155,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_143])).

tff(c_88,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_154,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_143])).

tff(c_92,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_76,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_64,plain,(
    ! [A_46] : k6_relat_1(A_46) = k6_partfun1(A_46) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_16,plain,(
    ! [A_12] : k2_relat_1(k6_relat_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_97,plain,(
    ! [A_12] : k2_relat_1(k6_partfun1(A_12)) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_16])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_90,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_80,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_1966,plain,(
    ! [A_203,C_204,B_205] :
      ( k6_partfun1(A_203) = k5_relat_1(C_204,k2_funct_1(C_204))
      | k1_xboole_0 = B_205
      | ~ v2_funct_1(C_204)
      | k2_relset_1(A_203,B_205,C_204) != B_205
      | ~ m1_subset_1(C_204,k1_zfmisc_1(k2_zfmisc_1(A_203,B_205)))
      | ~ v1_funct_2(C_204,A_203,B_205)
      | ~ v1_funct_1(C_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_1970,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_1966])).

tff(c_1976,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_80,c_76,c_1970])).

tff(c_1977,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1976])).

tff(c_32,plain,(
    ! [A_20] :
      ( k2_relat_1(k5_relat_1(A_20,k2_funct_1(A_20))) = k1_relat_1(A_20)
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1991,plain,
    ( k2_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1977,c_32])).

tff(c_2008,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_92,c_76,c_97,c_1991])).

tff(c_28,plain,(
    ! [A_19] :
      ( k2_relat_1(k2_funct_1(A_19)) = k1_relat_1(A_19)
      | ~ v2_funct_1(A_19)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_24,plain,(
    ! [A_15] :
      ( v1_relat_1(k2_funct_1(A_15))
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2127,plain,(
    ! [B_207,C_208,A_209] :
      ( k6_partfun1(B_207) = k5_relat_1(k2_funct_1(C_208),C_208)
      | k1_xboole_0 = B_207
      | ~ v2_funct_1(C_208)
      | k2_relset_1(A_209,B_207,C_208) != B_207
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(A_209,B_207)))
      | ~ v1_funct_2(C_208,A_209,B_207)
      | ~ v1_funct_1(C_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_2131,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_2127])).

tff(c_2137,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_80,c_76,c_2131])).

tff(c_2138,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2137])).

tff(c_36,plain,(
    ! [A_21] :
      ( k2_relat_1(k5_relat_1(k2_funct_1(A_21),A_21)) = k2_relat_1(A_21)
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2155,plain,
    ( k2_relat_1(k6_partfun1('#skF_2')) = k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2138,c_36])).

tff(c_2171,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_92,c_76,c_97,c_2155])).

tff(c_281,plain,(
    ! [A_89] :
      ( k1_relat_1(k2_funct_1(A_89)) = k2_relat_1(A_89)
      | ~ v2_funct_1(A_89)
      | ~ v1_funct_1(A_89)
      | ~ v1_relat_1(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_218,plain,(
    ! [B_76,A_77] :
      ( v4_relat_1(B_76,A_77)
      | ~ r1_tarski(k1_relat_1(B_76),A_77)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_232,plain,(
    ! [B_76] :
      ( v4_relat_1(B_76,k1_relat_1(B_76))
      | ~ v1_relat_1(B_76) ) ),
    inference(resolution,[status(thm)],[c_6,c_218])).

tff(c_287,plain,(
    ! [A_89] :
      ( v4_relat_1(k2_funct_1(A_89),k2_relat_1(A_89))
      | ~ v1_relat_1(k2_funct_1(A_89))
      | ~ v2_funct_1(A_89)
      | ~ v1_funct_1(A_89)
      | ~ v1_relat_1(A_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_232])).

tff(c_2186,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2171,c_287])).

tff(c_2203,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_92,c_76,c_2186])).

tff(c_2325,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2203])).

tff(c_2328,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_2325])).

tff(c_2332,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_92,c_2328])).

tff(c_2334,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2203])).

tff(c_18,plain,(
    ! [A_13] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_13)),A_13) = A_13
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_96,plain,(
    ! [A_13] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_13)),A_13) = A_13
      | ~ v1_relat_1(A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_18])).

tff(c_2502,plain,(
    ! [A_223] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_223)),k2_funct_1(A_223)) = k2_funct_1(A_223)
      | ~ v1_relat_1(k2_funct_1(A_223))
      | ~ v2_funct_1(A_223)
      | ~ v1_funct_1(A_223)
      | ~ v1_relat_1(A_223) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_96])).

tff(c_2523,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2171,c_2502])).

tff(c_2545,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_92,c_76,c_2334,c_2523])).

tff(c_2333,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_2203])).

tff(c_10,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k1_relat_1(B_4),A_3)
      | ~ v4_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1709,plain,(
    ! [A_177,A_178] :
      ( r1_tarski(k2_relat_1(A_177),A_178)
      | ~ v4_relat_1(k2_funct_1(A_177),A_178)
      | ~ v1_relat_1(k2_funct_1(A_177))
      | ~ v2_funct_1(A_177)
      | ~ v1_funct_1(A_177)
      | ~ v1_relat_1(A_177) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_10])).

tff(c_1725,plain,(
    ! [A_177] :
      ( r1_tarski(k2_relat_1(A_177),k1_relat_1(k2_funct_1(A_177)))
      | ~ v2_funct_1(A_177)
      | ~ v1_funct_1(A_177)
      | ~ v1_relat_1(A_177)
      | ~ v1_relat_1(k2_funct_1(A_177)) ) ),
    inference(resolution,[status(thm)],[c_232,c_1709])).

tff(c_2180,plain,
    ( r1_tarski('#skF_2',k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2171,c_1725])).

tff(c_2199,plain,
    ( r1_tarski('#skF_2',k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_92,c_76,c_2180])).

tff(c_2568,plain,(
    r1_tarski('#skF_2',k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2334,c_2199])).

tff(c_208,plain,(
    ! [B_72,A_73] :
      ( r1_tarski(k1_relat_1(B_72),A_73)
      | ~ v4_relat_1(B_72,A_73)
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_214,plain,(
    ! [B_72,A_73] :
      ( k1_relat_1(B_72) = A_73
      | ~ r1_tarski(A_73,k1_relat_1(B_72))
      | ~ v4_relat_1(B_72,A_73)
      | ~ v1_relat_1(B_72) ) ),
    inference(resolution,[status(thm)],[c_208,c_2])).

tff(c_2571,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2'
    | ~ v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2568,c_214])).

tff(c_2579,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2334,c_2333,c_2571])).

tff(c_60,plain,(
    ! [A_39] : m1_subset_1(k6_partfun1(A_39),k1_zfmisc_1(k2_zfmisc_1(A_39,A_39))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_153,plain,(
    ! [A_39] : v1_relat_1(k6_partfun1(A_39)) ),
    inference(resolution,[status(thm)],[c_60,c_143])).

tff(c_20,plain,(
    ! [A_14] :
      ( k5_relat_1(A_14,k6_relat_1(k2_relat_1(A_14))) = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_95,plain,(
    ! [A_14] :
      ( k5_relat_1(A_14,k6_partfun1(k2_relat_1(A_14))) = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_20])).

tff(c_459,plain,(
    ! [A_101,B_102,C_103] :
      ( k5_relat_1(k5_relat_1(A_101,B_102),C_103) = k5_relat_1(A_101,k5_relat_1(B_102,C_103))
      | ~ v1_relat_1(C_103)
      | ~ v1_relat_1(B_102)
      | ~ v1_relat_1(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_510,plain,(
    ! [A_13,C_103] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_13)),k5_relat_1(A_13,C_103)) = k5_relat_1(A_13,C_103)
      | ~ v1_relat_1(C_103)
      | ~ v1_relat_1(A_13)
      | ~ v1_relat_1(k6_partfun1(k1_relat_1(A_13)))
      | ~ v1_relat_1(A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_459])).

tff(c_642,plain,(
    ! [A_108,C_109] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_108)),k5_relat_1(A_108,C_109)) = k5_relat_1(A_108,C_109)
      | ~ v1_relat_1(C_109)
      | ~ v1_relat_1(A_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_510])).

tff(c_687,plain,(
    ! [A_14] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_14)),A_14) = k5_relat_1(A_14,k6_partfun1(k2_relat_1(A_14)))
      | ~ v1_relat_1(k6_partfun1(k2_relat_1(A_14)))
      | ~ v1_relat_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_642])).

tff(c_710,plain,(
    ! [A_14] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_14)),A_14) = k5_relat_1(A_14,k6_partfun1(k2_relat_1(A_14)))
      | ~ v1_relat_1(A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_687])).

tff(c_2602,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))) = k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2579,c_710])).

tff(c_2643,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2334,c_2545,c_2602])).

tff(c_2931,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k1_relat_1('#skF_3'))) = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2643])).

tff(c_2950,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_92,c_76,c_2008,c_2931])).

tff(c_86,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_1644,plain,(
    ! [F_174,A_171,C_173,D_175,B_176,E_172] :
      ( m1_subset_1(k1_partfun1(A_171,B_176,C_173,D_175,E_172,F_174),k1_zfmisc_1(k2_zfmisc_1(A_171,D_175)))
      | ~ m1_subset_1(F_174,k1_zfmisc_1(k2_zfmisc_1(C_173,D_175)))
      | ~ v1_funct_1(F_174)
      | ~ m1_subset_1(E_172,k1_zfmisc_1(k2_zfmisc_1(A_171,B_176)))
      | ~ v1_funct_1(E_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_78,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_875,plain,(
    ! [D_119,C_120,A_121,B_122] :
      ( D_119 = C_120
      | ~ r2_relset_1(A_121,B_122,C_120,D_119)
      | ~ m1_subset_1(D_119,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122)))
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_883,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_78,c_875])).

tff(c_898,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_883])).

tff(c_1019,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_898])).

tff(c_1667,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1644,c_1019])).

tff(c_1699,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_86,c_82,c_1667])).

tff(c_1700,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_898])).

tff(c_1784,plain,(
    ! [A_191,D_192,E_190,C_194,F_193,B_195] :
      ( k1_partfun1(A_191,B_195,C_194,D_192,E_190,F_193) = k5_relat_1(E_190,F_193)
      | ~ m1_subset_1(F_193,k1_zfmisc_1(k2_zfmisc_1(C_194,D_192)))
      | ~ v1_funct_1(F_193)
      | ~ m1_subset_1(E_190,k1_zfmisc_1(k2_zfmisc_1(A_191,B_195)))
      | ~ v1_funct_1(E_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_1790,plain,(
    ! [A_191,B_195,E_190] :
      ( k1_partfun1(A_191,B_195,'#skF_2','#skF_1',E_190,'#skF_4') = k5_relat_1(E_190,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_190,k1_zfmisc_1(k2_zfmisc_1(A_191,B_195)))
      | ~ v1_funct_1(E_190) ) ),
    inference(resolution,[status(thm)],[c_82,c_1784])).

tff(c_1815,plain,(
    ! [A_199,B_200,E_201] :
      ( k1_partfun1(A_199,B_200,'#skF_2','#skF_1',E_201,'#skF_4') = k5_relat_1(E_201,'#skF_4')
      | ~ m1_subset_1(E_201,k1_zfmisc_1(k2_zfmisc_1(A_199,B_200)))
      | ~ v1_funct_1(E_201) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1790])).

tff(c_1821,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_1815])).

tff(c_1828,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_1700,c_1821])).

tff(c_12,plain,(
    ! [A_5,B_9,C_11] :
      ( k5_relat_1(k5_relat_1(A_5,B_9),C_11) = k5_relat_1(A_5,k5_relat_1(B_9,C_11))
      | ~ v1_relat_1(C_11)
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2149,plain,(
    ! [C_11] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_11)) = k5_relat_1(k6_partfun1('#skF_2'),C_11)
      | ~ v1_relat_1(C_11)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2138,c_12])).

tff(c_2167,plain,(
    ! [C_11] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_11)) = k5_relat_1(k6_partfun1('#skF_2'),C_11)
      | ~ v1_relat_1(C_11)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_2149])).

tff(c_4864,plain,(
    ! [C_265] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_265)) = k5_relat_1(k6_partfun1('#skF_2'),C_265)
      | ~ v1_relat_1(C_265) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2334,c_2167])).

tff(c_4927,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1828,c_4864])).

tff(c_4967,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_2950,c_4927])).

tff(c_14,plain,(
    ! [A_12] : k1_relat_1(k6_relat_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_98,plain,(
    ! [A_12] : k1_relat_1(k6_partfun1(A_12)) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_14])).

tff(c_233,plain,(
    ! [C_78,A_79,B_80] :
      ( v4_relat_1(C_78,A_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_245,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_233])).

tff(c_26,plain,(
    ! [B_18,A_16] :
      ( r1_tarski(k2_relat_1(B_18),k1_relat_1(A_16))
      | k1_relat_1(k5_relat_1(B_18,A_16)) != k1_relat_1(B_18)
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2189,plain,(
    ! [A_16] :
      ( r1_tarski('#skF_2',k1_relat_1(A_16))
      | k1_relat_1(k5_relat_1('#skF_3',A_16)) != k1_relat_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2171,c_26])).

tff(c_3986,plain,(
    ! [A_250] :
      ( r1_tarski('#skF_2',k1_relat_1(A_250))
      | k1_relat_1(k5_relat_1('#skF_3',A_250)) != '#skF_1'
      | ~ v1_funct_1(A_250)
      | ~ v1_relat_1(A_250) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_92,c_2008,c_2189])).

tff(c_21824,plain,(
    ! [A_485] :
      ( k1_relat_1(A_485) = '#skF_2'
      | ~ v4_relat_1(A_485,'#skF_2')
      | k1_relat_1(k5_relat_1('#skF_3',A_485)) != '#skF_1'
      | ~ v1_funct_1(A_485)
      | ~ v1_relat_1(A_485) ) ),
    inference(resolution,[status(thm)],[c_3986,c_214])).

tff(c_21912,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v4_relat_1('#skF_4','#skF_2')
    | k1_relat_1(k6_partfun1('#skF_1')) != '#skF_1'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1828,c_21824])).

tff(c_21964,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_86,c_98,c_245,c_21912])).

tff(c_22044,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_21964,c_96])).

tff(c_22094,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_4967,c_22044])).

tff(c_22096,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_22094])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.32  % Computer   : n004.cluster.edu
% 0.14/0.32  % Model      : x86_64 x86_64
% 0.14/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.32  % Memory     : 8042.1875MB
% 0.14/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.32  % CPULimit   : 60
% 0.14/0.32  % DateTime   : Tue Dec  1 14:51:23 EST 2020
% 0.14/0.32  % CPUTime    : 
% 0.14/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.81/7.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.81/7.18  
% 14.81/7.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.81/7.19  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 14.81/7.19  
% 14.81/7.19  %Foreground sorts:
% 14.81/7.19  
% 14.81/7.19  
% 14.81/7.19  %Background operators:
% 14.81/7.19  
% 14.81/7.19  
% 14.81/7.19  %Foreground operators:
% 14.81/7.19  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 14.81/7.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 14.81/7.19  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 14.81/7.19  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 14.81/7.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.81/7.19  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 14.81/7.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.81/7.19  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 14.81/7.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.81/7.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 14.81/7.19  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 14.81/7.19  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 14.81/7.19  tff('#skF_2', type, '#skF_2': $i).
% 14.81/7.19  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 14.81/7.19  tff('#skF_3', type, '#skF_3': $i).
% 14.81/7.19  tff('#skF_1', type, '#skF_1': $i).
% 14.81/7.19  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 14.81/7.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.81/7.19  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 14.81/7.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.81/7.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.81/7.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.81/7.19  tff('#skF_4', type, '#skF_4': $i).
% 14.81/7.19  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 14.81/7.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.81/7.19  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 14.81/7.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.81/7.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.81/7.19  
% 15.04/7.21  tff(f_208, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 15.04/7.21  tff(f_124, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 15.04/7.21  tff(f_166, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 15.04/7.21  tff(f_51, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 15.04/7.21  tff(f_182, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 15.04/7.21  tff(f_100, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 15.04/7.21  tff(f_90, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 15.04/7.21  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 15.04/7.21  tff(f_110, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_funct_1)).
% 15.04/7.21  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.04/7.21  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 15.04/7.21  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 15.04/7.21  tff(f_154, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 15.04/7.21  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 15.04/7.21  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 15.04/7.21  tff(f_150, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 15.04/7.21  tff(f_138, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 15.04/7.21  tff(f_164, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 15.04/7.21  tff(f_130, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 15.04/7.21  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_funct_1)).
% 15.04/7.21  tff(c_70, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_208])).
% 15.04/7.21  tff(c_82, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_208])).
% 15.04/7.21  tff(c_143, plain, (![C_61, A_62, B_63]: (v1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 15.04/7.21  tff(c_155, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_82, c_143])).
% 15.04/7.21  tff(c_88, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_208])).
% 15.04/7.21  tff(c_154, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_143])).
% 15.04/7.21  tff(c_92, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_208])).
% 15.04/7.21  tff(c_76, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_208])).
% 15.04/7.21  tff(c_64, plain, (![A_46]: (k6_relat_1(A_46)=k6_partfun1(A_46))), inference(cnfTransformation, [status(thm)], [f_166])).
% 15.04/7.21  tff(c_16, plain, (![A_12]: (k2_relat_1(k6_relat_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_51])).
% 15.04/7.21  tff(c_97, plain, (![A_12]: (k2_relat_1(k6_partfun1(A_12))=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_16])).
% 15.04/7.21  tff(c_72, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_208])).
% 15.04/7.21  tff(c_90, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 15.04/7.21  tff(c_80, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_208])).
% 15.04/7.21  tff(c_1966, plain, (![A_203, C_204, B_205]: (k6_partfun1(A_203)=k5_relat_1(C_204, k2_funct_1(C_204)) | k1_xboole_0=B_205 | ~v2_funct_1(C_204) | k2_relset_1(A_203, B_205, C_204)!=B_205 | ~m1_subset_1(C_204, k1_zfmisc_1(k2_zfmisc_1(A_203, B_205))) | ~v1_funct_2(C_204, A_203, B_205) | ~v1_funct_1(C_204))), inference(cnfTransformation, [status(thm)], [f_182])).
% 15.04/7.21  tff(c_1970, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_1966])).
% 15.04/7.21  tff(c_1976, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_80, c_76, c_1970])).
% 15.04/7.21  tff(c_1977, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_72, c_1976])).
% 15.04/7.21  tff(c_32, plain, (![A_20]: (k2_relat_1(k5_relat_1(A_20, k2_funct_1(A_20)))=k1_relat_1(A_20) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_100])).
% 15.04/7.21  tff(c_1991, plain, (k2_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1977, c_32])).
% 15.04/7.21  tff(c_2008, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_154, c_92, c_76, c_97, c_1991])).
% 15.04/7.21  tff(c_28, plain, (![A_19]: (k2_relat_1(k2_funct_1(A_19))=k1_relat_1(A_19) | ~v2_funct_1(A_19) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_90])).
% 15.04/7.21  tff(c_24, plain, (![A_15]: (v1_relat_1(k2_funct_1(A_15)) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.04/7.21  tff(c_2127, plain, (![B_207, C_208, A_209]: (k6_partfun1(B_207)=k5_relat_1(k2_funct_1(C_208), C_208) | k1_xboole_0=B_207 | ~v2_funct_1(C_208) | k2_relset_1(A_209, B_207, C_208)!=B_207 | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(A_209, B_207))) | ~v1_funct_2(C_208, A_209, B_207) | ~v1_funct_1(C_208))), inference(cnfTransformation, [status(thm)], [f_182])).
% 15.04/7.21  tff(c_2131, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_2127])).
% 15.04/7.21  tff(c_2137, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_80, c_76, c_2131])).
% 15.04/7.21  tff(c_2138, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_72, c_2137])).
% 15.04/7.21  tff(c_36, plain, (![A_21]: (k2_relat_1(k5_relat_1(k2_funct_1(A_21), A_21))=k2_relat_1(A_21) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_110])).
% 15.04/7.21  tff(c_2155, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2138, c_36])).
% 15.04/7.21  tff(c_2171, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_154, c_92, c_76, c_97, c_2155])).
% 15.04/7.21  tff(c_281, plain, (![A_89]: (k1_relat_1(k2_funct_1(A_89))=k2_relat_1(A_89) | ~v2_funct_1(A_89) | ~v1_funct_1(A_89) | ~v1_relat_1(A_89))), inference(cnfTransformation, [status(thm)], [f_90])).
% 15.04/7.21  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.04/7.21  tff(c_218, plain, (![B_76, A_77]: (v4_relat_1(B_76, A_77) | ~r1_tarski(k1_relat_1(B_76), A_77) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.04/7.21  tff(c_232, plain, (![B_76]: (v4_relat_1(B_76, k1_relat_1(B_76)) | ~v1_relat_1(B_76))), inference(resolution, [status(thm)], [c_6, c_218])).
% 15.04/7.21  tff(c_287, plain, (![A_89]: (v4_relat_1(k2_funct_1(A_89), k2_relat_1(A_89)) | ~v1_relat_1(k2_funct_1(A_89)) | ~v2_funct_1(A_89) | ~v1_funct_1(A_89) | ~v1_relat_1(A_89))), inference(superposition, [status(thm), theory('equality')], [c_281, c_232])).
% 15.04/7.21  tff(c_2186, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2171, c_287])).
% 15.04/7.21  tff(c_2203, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_92, c_76, c_2186])).
% 15.04/7.21  tff(c_2325, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2203])).
% 15.04/7.21  tff(c_2328, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_2325])).
% 15.04/7.21  tff(c_2332, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_154, c_92, c_2328])).
% 15.04/7.21  tff(c_2334, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2203])).
% 15.04/7.21  tff(c_18, plain, (![A_13]: (k5_relat_1(k6_relat_1(k1_relat_1(A_13)), A_13)=A_13 | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 15.04/7.21  tff(c_96, plain, (![A_13]: (k5_relat_1(k6_partfun1(k1_relat_1(A_13)), A_13)=A_13 | ~v1_relat_1(A_13))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_18])).
% 15.04/7.21  tff(c_2502, plain, (![A_223]: (k5_relat_1(k6_partfun1(k2_relat_1(A_223)), k2_funct_1(A_223))=k2_funct_1(A_223) | ~v1_relat_1(k2_funct_1(A_223)) | ~v2_funct_1(A_223) | ~v1_funct_1(A_223) | ~v1_relat_1(A_223))), inference(superposition, [status(thm), theory('equality')], [c_281, c_96])).
% 15.04/7.21  tff(c_2523, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2171, c_2502])).
% 15.04/7.21  tff(c_2545, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_92, c_76, c_2334, c_2523])).
% 15.04/7.21  tff(c_2333, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_2203])).
% 15.04/7.21  tff(c_10, plain, (![B_4, A_3]: (r1_tarski(k1_relat_1(B_4), A_3) | ~v4_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.04/7.21  tff(c_1709, plain, (![A_177, A_178]: (r1_tarski(k2_relat_1(A_177), A_178) | ~v4_relat_1(k2_funct_1(A_177), A_178) | ~v1_relat_1(k2_funct_1(A_177)) | ~v2_funct_1(A_177) | ~v1_funct_1(A_177) | ~v1_relat_1(A_177))), inference(superposition, [status(thm), theory('equality')], [c_281, c_10])).
% 15.04/7.21  tff(c_1725, plain, (![A_177]: (r1_tarski(k2_relat_1(A_177), k1_relat_1(k2_funct_1(A_177))) | ~v2_funct_1(A_177) | ~v1_funct_1(A_177) | ~v1_relat_1(A_177) | ~v1_relat_1(k2_funct_1(A_177)))), inference(resolution, [status(thm)], [c_232, c_1709])).
% 15.04/7.21  tff(c_2180, plain, (r1_tarski('#skF_2', k1_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2171, c_1725])).
% 15.04/7.21  tff(c_2199, plain, (r1_tarski('#skF_2', k1_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_92, c_76, c_2180])).
% 15.04/7.21  tff(c_2568, plain, (r1_tarski('#skF_2', k1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2334, c_2199])).
% 15.04/7.21  tff(c_208, plain, (![B_72, A_73]: (r1_tarski(k1_relat_1(B_72), A_73) | ~v4_relat_1(B_72, A_73) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.04/7.21  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.04/7.21  tff(c_214, plain, (![B_72, A_73]: (k1_relat_1(B_72)=A_73 | ~r1_tarski(A_73, k1_relat_1(B_72)) | ~v4_relat_1(B_72, A_73) | ~v1_relat_1(B_72))), inference(resolution, [status(thm)], [c_208, c_2])).
% 15.04/7.21  tff(c_2571, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2' | ~v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2568, c_214])).
% 15.04/7.21  tff(c_2579, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2334, c_2333, c_2571])).
% 15.04/7.21  tff(c_60, plain, (![A_39]: (m1_subset_1(k6_partfun1(A_39), k1_zfmisc_1(k2_zfmisc_1(A_39, A_39))))), inference(cnfTransformation, [status(thm)], [f_154])).
% 15.04/7.21  tff(c_153, plain, (![A_39]: (v1_relat_1(k6_partfun1(A_39)))), inference(resolution, [status(thm)], [c_60, c_143])).
% 15.04/7.21  tff(c_20, plain, (![A_14]: (k5_relat_1(A_14, k6_relat_1(k2_relat_1(A_14)))=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 15.04/7.21  tff(c_95, plain, (![A_14]: (k5_relat_1(A_14, k6_partfun1(k2_relat_1(A_14)))=A_14 | ~v1_relat_1(A_14))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_20])).
% 15.04/7.21  tff(c_459, plain, (![A_101, B_102, C_103]: (k5_relat_1(k5_relat_1(A_101, B_102), C_103)=k5_relat_1(A_101, k5_relat_1(B_102, C_103)) | ~v1_relat_1(C_103) | ~v1_relat_1(B_102) | ~v1_relat_1(A_101))), inference(cnfTransformation, [status(thm)], [f_47])).
% 15.04/7.21  tff(c_510, plain, (![A_13, C_103]: (k5_relat_1(k6_partfun1(k1_relat_1(A_13)), k5_relat_1(A_13, C_103))=k5_relat_1(A_13, C_103) | ~v1_relat_1(C_103) | ~v1_relat_1(A_13) | ~v1_relat_1(k6_partfun1(k1_relat_1(A_13))) | ~v1_relat_1(A_13))), inference(superposition, [status(thm), theory('equality')], [c_96, c_459])).
% 15.04/7.21  tff(c_642, plain, (![A_108, C_109]: (k5_relat_1(k6_partfun1(k1_relat_1(A_108)), k5_relat_1(A_108, C_109))=k5_relat_1(A_108, C_109) | ~v1_relat_1(C_109) | ~v1_relat_1(A_108))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_510])).
% 15.04/7.21  tff(c_687, plain, (![A_14]: (k5_relat_1(k6_partfun1(k1_relat_1(A_14)), A_14)=k5_relat_1(A_14, k6_partfun1(k2_relat_1(A_14))) | ~v1_relat_1(k6_partfun1(k2_relat_1(A_14))) | ~v1_relat_1(A_14) | ~v1_relat_1(A_14))), inference(superposition, [status(thm), theory('equality')], [c_95, c_642])).
% 15.04/7.21  tff(c_710, plain, (![A_14]: (k5_relat_1(k6_partfun1(k1_relat_1(A_14)), A_14)=k5_relat_1(A_14, k6_partfun1(k2_relat_1(A_14))) | ~v1_relat_1(A_14))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_687])).
% 15.04/7.21  tff(c_2602, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))))=k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2579, c_710])).
% 15.04/7.21  tff(c_2643, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2334, c_2545, c_2602])).
% 15.04/7.21  tff(c_2931, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k1_relat_1('#skF_3')))=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_2643])).
% 15.04/7.21  tff(c_2950, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_92, c_76, c_2008, c_2931])).
% 15.04/7.21  tff(c_86, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_208])).
% 15.04/7.21  tff(c_1644, plain, (![F_174, A_171, C_173, D_175, B_176, E_172]: (m1_subset_1(k1_partfun1(A_171, B_176, C_173, D_175, E_172, F_174), k1_zfmisc_1(k2_zfmisc_1(A_171, D_175))) | ~m1_subset_1(F_174, k1_zfmisc_1(k2_zfmisc_1(C_173, D_175))) | ~v1_funct_1(F_174) | ~m1_subset_1(E_172, k1_zfmisc_1(k2_zfmisc_1(A_171, B_176))) | ~v1_funct_1(E_172))), inference(cnfTransformation, [status(thm)], [f_150])).
% 15.04/7.21  tff(c_78, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_208])).
% 15.04/7.21  tff(c_875, plain, (![D_119, C_120, A_121, B_122]: (D_119=C_120 | ~r2_relset_1(A_121, B_122, C_120, D_119) | ~m1_subset_1(D_119, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 15.04/7.21  tff(c_883, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_78, c_875])).
% 15.04/7.21  tff(c_898, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_883])).
% 15.04/7.21  tff(c_1019, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_898])).
% 15.04/7.21  tff(c_1667, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1644, c_1019])).
% 15.04/7.21  tff(c_1699, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_86, c_82, c_1667])).
% 15.04/7.21  tff(c_1700, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_898])).
% 15.04/7.21  tff(c_1784, plain, (![A_191, D_192, E_190, C_194, F_193, B_195]: (k1_partfun1(A_191, B_195, C_194, D_192, E_190, F_193)=k5_relat_1(E_190, F_193) | ~m1_subset_1(F_193, k1_zfmisc_1(k2_zfmisc_1(C_194, D_192))) | ~v1_funct_1(F_193) | ~m1_subset_1(E_190, k1_zfmisc_1(k2_zfmisc_1(A_191, B_195))) | ~v1_funct_1(E_190))), inference(cnfTransformation, [status(thm)], [f_164])).
% 15.04/7.21  tff(c_1790, plain, (![A_191, B_195, E_190]: (k1_partfun1(A_191, B_195, '#skF_2', '#skF_1', E_190, '#skF_4')=k5_relat_1(E_190, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_190, k1_zfmisc_1(k2_zfmisc_1(A_191, B_195))) | ~v1_funct_1(E_190))), inference(resolution, [status(thm)], [c_82, c_1784])).
% 15.04/7.21  tff(c_1815, plain, (![A_199, B_200, E_201]: (k1_partfun1(A_199, B_200, '#skF_2', '#skF_1', E_201, '#skF_4')=k5_relat_1(E_201, '#skF_4') | ~m1_subset_1(E_201, k1_zfmisc_1(k2_zfmisc_1(A_199, B_200))) | ~v1_funct_1(E_201))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1790])).
% 15.04/7.21  tff(c_1821, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_1815])).
% 15.04/7.21  tff(c_1828, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_1700, c_1821])).
% 15.04/7.21  tff(c_12, plain, (![A_5, B_9, C_11]: (k5_relat_1(k5_relat_1(A_5, B_9), C_11)=k5_relat_1(A_5, k5_relat_1(B_9, C_11)) | ~v1_relat_1(C_11) | ~v1_relat_1(B_9) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_47])).
% 15.04/7.21  tff(c_2149, plain, (![C_11]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_11))=k5_relat_1(k6_partfun1('#skF_2'), C_11) | ~v1_relat_1(C_11) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2138, c_12])).
% 15.04/7.21  tff(c_2167, plain, (![C_11]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_11))=k5_relat_1(k6_partfun1('#skF_2'), C_11) | ~v1_relat_1(C_11) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_2149])).
% 15.04/7.21  tff(c_4864, plain, (![C_265]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_265))=k5_relat_1(k6_partfun1('#skF_2'), C_265) | ~v1_relat_1(C_265))), inference(demodulation, [status(thm), theory('equality')], [c_2334, c_2167])).
% 15.04/7.21  tff(c_4927, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1828, c_4864])).
% 15.04/7.21  tff(c_4967, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_2950, c_4927])).
% 15.04/7.21  tff(c_14, plain, (![A_12]: (k1_relat_1(k6_relat_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_51])).
% 15.04/7.21  tff(c_98, plain, (![A_12]: (k1_relat_1(k6_partfun1(A_12))=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_14])).
% 15.04/7.21  tff(c_233, plain, (![C_78, A_79, B_80]: (v4_relat_1(C_78, A_79) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 15.04/7.21  tff(c_245, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_82, c_233])).
% 15.04/7.21  tff(c_26, plain, (![B_18, A_16]: (r1_tarski(k2_relat_1(B_18), k1_relat_1(A_16)) | k1_relat_1(k5_relat_1(B_18, A_16))!=k1_relat_1(B_18) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_80])).
% 15.04/7.21  tff(c_2189, plain, (![A_16]: (r1_tarski('#skF_2', k1_relat_1(A_16)) | k1_relat_1(k5_relat_1('#skF_3', A_16))!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(superposition, [status(thm), theory('equality')], [c_2171, c_26])).
% 15.04/7.21  tff(c_3986, plain, (![A_250]: (r1_tarski('#skF_2', k1_relat_1(A_250)) | k1_relat_1(k5_relat_1('#skF_3', A_250))!='#skF_1' | ~v1_funct_1(A_250) | ~v1_relat_1(A_250))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_92, c_2008, c_2189])).
% 15.04/7.21  tff(c_21824, plain, (![A_485]: (k1_relat_1(A_485)='#skF_2' | ~v4_relat_1(A_485, '#skF_2') | k1_relat_1(k5_relat_1('#skF_3', A_485))!='#skF_1' | ~v1_funct_1(A_485) | ~v1_relat_1(A_485))), inference(resolution, [status(thm)], [c_3986, c_214])).
% 15.04/7.21  tff(c_21912, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v4_relat_1('#skF_4', '#skF_2') | k1_relat_1(k6_partfun1('#skF_1'))!='#skF_1' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1828, c_21824])).
% 15.04/7.21  tff(c_21964, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_155, c_86, c_98, c_245, c_21912])).
% 15.04/7.21  tff(c_22044, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_21964, c_96])).
% 15.04/7.21  tff(c_22094, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_155, c_4967, c_22044])).
% 15.04/7.21  tff(c_22096, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_22094])).
% 15.04/7.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.04/7.21  
% 15.04/7.21  Inference rules
% 15.04/7.21  ----------------------
% 15.04/7.21  #Ref     : 0
% 15.04/7.21  #Sup     : 4558
% 15.04/7.21  #Fact    : 0
% 15.04/7.21  #Define  : 0
% 15.04/7.21  #Split   : 29
% 15.04/7.21  #Chain   : 0
% 15.04/7.21  #Close   : 0
% 15.04/7.21  
% 15.04/7.21  Ordering : KBO
% 15.04/7.21  
% 15.04/7.21  Simplification rules
% 15.04/7.21  ----------------------
% 15.04/7.21  #Subsume      : 535
% 15.04/7.21  #Demod        : 11002
% 15.04/7.21  #Tautology    : 1310
% 15.04/7.21  #SimpNegUnit  : 115
% 15.04/7.21  #BackRed      : 122
% 15.04/7.21  
% 15.04/7.21  #Partial instantiations: 0
% 15.04/7.21  #Strategies tried      : 1
% 15.04/7.21  
% 15.04/7.21  Timing (in seconds)
% 15.04/7.21  ----------------------
% 15.04/7.21  Preprocessing        : 0.38
% 15.04/7.21  Parsing              : 0.20
% 15.04/7.21  CNF conversion       : 0.03
% 15.04/7.21  Main loop            : 6.07
% 15.04/7.21  Inferencing          : 1.30
% 15.04/7.22  Reduction            : 3.34
% 15.04/7.22  Demodulation         : 2.89
% 15.04/7.22  BG Simplification    : 0.13
% 15.04/7.22  Subsumption          : 1.04
% 15.04/7.22  Abstraction          : 0.20
% 15.04/7.22  MUC search           : 0.00
% 15.04/7.22  Cooper               : 0.00
% 15.04/7.22  Total                : 6.50
% 15.04/7.22  Index Insertion      : 0.00
% 15.04/7.22  Index Deletion       : 0.00
% 15.04/7.22  Index Matching       : 0.00
% 15.04/7.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
