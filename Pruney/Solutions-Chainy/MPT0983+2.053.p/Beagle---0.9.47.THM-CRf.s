%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:08 EST 2020

% Result     : Theorem 7.25s
% Output     : CNFRefutation 7.50s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 205 expanded)
%              Number of leaves         :   46 (  93 expanded)
%              Depth                    :    9
%              Number of atoms          :  198 ( 636 expanded)
%              Number of equality atoms :   39 (  53 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_163,negated_conjecture,(
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

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_104,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_72,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_102,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_92,axiom,(
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

tff(f_143,axiom,(
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

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_35,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_121,axiom,(
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

tff(c_48,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_99,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_172,plain,(
    ! [C_73,A_74,B_75] :
      ( v1_xboole_0(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75)))
      | ~ v1_xboole_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_189,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_172])).

tff(c_192,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_189])).

tff(c_62,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_60,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_54,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_40,plain,(
    ! [A_42] : k6_relat_1(A_42) = k6_partfun1(A_42) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_10,plain,(
    ! [A_3] : v2_funct_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_63,plain,(
    ! [A_3] : v2_funct_1(k6_partfun1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_10])).

tff(c_1920,plain,(
    ! [D_183,E_181,F_180,B_182,A_184,C_179] :
      ( k4_relset_1(A_184,B_182,C_179,D_183,E_181,F_180) = k5_relat_1(E_181,F_180)
      | ~ m1_subset_1(F_180,k1_zfmisc_1(k2_zfmisc_1(C_179,D_183)))
      | ~ m1_subset_1(E_181,k1_zfmisc_1(k2_zfmisc_1(A_184,B_182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2175,plain,(
    ! [A_200,B_201,E_202] :
      ( k4_relset_1(A_200,B_201,'#skF_2','#skF_1',E_202,'#skF_4') = k5_relat_1(E_202,'#skF_4')
      | ~ m1_subset_1(E_202,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201))) ) ),
    inference(resolution,[status(thm)],[c_52,c_1920])).

tff(c_2202,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_2175])).

tff(c_20,plain,(
    ! [E_18,C_16,D_17,F_19,A_14,B_15] :
      ( m1_subset_1(k4_relset_1(A_14,B_15,C_16,D_17,E_18,F_19),k1_zfmisc_1(k2_zfmisc_1(A_14,D_17)))
      | ~ m1_subset_1(F_19,k1_zfmisc_1(k2_zfmisc_1(C_16,D_17)))
      | ~ m1_subset_1(E_18,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2341,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2202,c_20])).

tff(c_2345,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_2341])).

tff(c_2250,plain,(
    ! [D_205,F_203,B_206,C_207,A_204,E_208] :
      ( k1_partfun1(A_204,B_206,C_207,D_205,E_208,F_203) = k5_relat_1(E_208,F_203)
      | ~ m1_subset_1(F_203,k1_zfmisc_1(k2_zfmisc_1(C_207,D_205)))
      | ~ v1_funct_1(F_203)
      | ~ m1_subset_1(E_208,k1_zfmisc_1(k2_zfmisc_1(A_204,B_206)))
      | ~ v1_funct_1(E_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2266,plain,(
    ! [A_204,B_206,E_208] :
      ( k1_partfun1(A_204,B_206,'#skF_2','#skF_1',E_208,'#skF_4') = k5_relat_1(E_208,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_208,k1_zfmisc_1(k2_zfmisc_1(A_204,B_206)))
      | ~ v1_funct_1(E_208) ) ),
    inference(resolution,[status(thm)],[c_52,c_2250])).

tff(c_2915,plain,(
    ! [A_231,B_232,E_233] :
      ( k1_partfun1(A_231,B_232,'#skF_2','#skF_1',E_233,'#skF_4') = k5_relat_1(E_233,'#skF_4')
      | ~ m1_subset_1(E_233,k1_zfmisc_1(k2_zfmisc_1(A_231,B_232)))
      | ~ v1_funct_1(E_233) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2266])).

tff(c_2951,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2915])).

tff(c_2972,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2951])).

tff(c_36,plain,(
    ! [A_35] : m1_subset_1(k6_partfun1(A_35),k1_zfmisc_1(k2_zfmisc_1(A_35,A_35))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_50,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_1557,plain,(
    ! [D_164,C_165,A_166,B_167] :
      ( D_164 = C_165
      | ~ r2_relset_1(A_166,B_167,C_165,D_164)
      | ~ m1_subset_1(D_164,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167)))
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1567,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_50,c_1557])).

tff(c_1586,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1567])).

tff(c_1611,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1586])).

tff(c_3470,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2972,c_1611])).

tff(c_3474,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2345,c_3470])).

tff(c_3475,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1586])).

tff(c_4352,plain,(
    ! [D_289,A_291,B_290,C_292,E_288] :
      ( k1_xboole_0 = C_292
      | v2_funct_1(D_289)
      | ~ v2_funct_1(k1_partfun1(A_291,B_290,B_290,C_292,D_289,E_288))
      | ~ m1_subset_1(E_288,k1_zfmisc_1(k2_zfmisc_1(B_290,C_292)))
      | ~ v1_funct_2(E_288,B_290,C_292)
      | ~ v1_funct_1(E_288)
      | ~ m1_subset_1(D_289,k1_zfmisc_1(k2_zfmisc_1(A_291,B_290)))
      | ~ v1_funct_2(D_289,A_291,B_290)
      | ~ v1_funct_1(D_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_4354,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3475,c_4352])).

tff(c_4356,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_54,c_52,c_63,c_4354])).

tff(c_4357,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_4356])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_4389,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4357,c_2])).

tff(c_4391,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_192,c_4389])).

tff(c_4392,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_189])).

tff(c_100,plain,(
    ! [B_59,A_60] :
      ( ~ v1_xboole_0(B_59)
      | B_59 = A_60
      | ~ v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_103,plain,(
    ! [A_60] :
      ( k1_xboole_0 = A_60
      | ~ v1_xboole_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_2,c_100])).

tff(c_4399,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4392,c_103])).

tff(c_72,plain,(
    ! [A_58] : k6_relat_1(A_58) = k6_partfun1(A_58) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_6,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_78,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_6])).

tff(c_94,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_63])).

tff(c_4413,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4399,c_94])).

tff(c_4419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_4413])).

tff(c_4420,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_4436,plain,(
    ! [C_297,A_298,B_299] :
      ( v1_relat_1(C_297)
      | ~ m1_subset_1(C_297,k1_zfmisc_1(k2_zfmisc_1(A_298,B_299))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4454,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_4436])).

tff(c_4472,plain,(
    ! [C_303,B_304,A_305] :
      ( v5_relat_1(C_303,B_304)
      | ~ m1_subset_1(C_303,k1_zfmisc_1(k2_zfmisc_1(A_305,B_304))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4488,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_4472])).

tff(c_4628,plain,(
    ! [A_320,B_321,C_322] :
      ( k2_relset_1(A_320,B_321,C_322) = k2_relat_1(C_322)
      | ~ m1_subset_1(C_322,k1_zfmisc_1(k2_zfmisc_1(A_320,B_321))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4644,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_4628])).

tff(c_5631,plain,(
    ! [A_378,B_379,C_380,D_381] :
      ( k2_relset_1(A_378,B_379,C_380) = B_379
      | ~ r2_relset_1(B_379,B_379,k1_partfun1(B_379,A_378,A_378,B_379,D_381,C_380),k6_partfun1(B_379))
      | ~ m1_subset_1(D_381,k1_zfmisc_1(k2_zfmisc_1(B_379,A_378)))
      | ~ v1_funct_2(D_381,B_379,A_378)
      | ~ v1_funct_1(D_381)
      | ~ m1_subset_1(C_380,k1_zfmisc_1(k2_zfmisc_1(A_378,B_379)))
      | ~ v1_funct_2(C_380,A_378,B_379)
      | ~ v1_funct_1(C_380) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_5643,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_5631])).

tff(c_5649,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_62,c_60,c_58,c_4644,c_5643])).

tff(c_30,plain,(
    ! [B_34] :
      ( v2_funct_2(B_34,k2_relat_1(B_34))
      | ~ v5_relat_1(B_34,k2_relat_1(B_34))
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_5654,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5649,c_30])).

tff(c_5658,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4454,c_4488,c_5649,c_5654])).

tff(c_5660,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4420,c_5658])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:40:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.25/2.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.50/2.60  
% 7.50/2.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.50/2.60  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.50/2.60  
% 7.50/2.60  %Foreground sorts:
% 7.50/2.60  
% 7.50/2.60  
% 7.50/2.60  %Background operators:
% 7.50/2.60  
% 7.50/2.60  
% 7.50/2.60  %Foreground operators:
% 7.50/2.60  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.50/2.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.50/2.60  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.50/2.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.50/2.60  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.50/2.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.50/2.60  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.50/2.60  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.50/2.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.50/2.60  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.50/2.60  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.50/2.60  tff('#skF_2', type, '#skF_2': $i).
% 7.50/2.60  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.50/2.60  tff('#skF_3', type, '#skF_3': $i).
% 7.50/2.60  tff('#skF_1', type, '#skF_1': $i).
% 7.50/2.60  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 7.50/2.60  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.50/2.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.50/2.60  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.50/2.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.50/2.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.50/2.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.50/2.60  tff('#skF_4', type, '#skF_4': $i).
% 7.50/2.60  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.50/2.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.50/2.60  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.50/2.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.50/2.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.50/2.60  
% 7.50/2.62  tff(f_163, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 7.50/2.62  tff(f_56, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 7.50/2.62  tff(f_104, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.50/2.62  tff(f_39, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 7.50/2.62  tff(f_72, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 7.50/2.62  tff(f_62, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 7.50/2.62  tff(f_102, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.50/2.62  tff(f_92, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.50/2.62  tff(f_80, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.50/2.62  tff(f_143, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 7.50/2.62  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.50/2.62  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 7.50/2.62  tff(f_35, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 7.50/2.62  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.50/2.62  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.50/2.62  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.50/2.62  tff(f_121, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 7.50/2.62  tff(f_88, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 7.50/2.62  tff(c_48, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.50/2.62  tff(c_99, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_48])).
% 7.50/2.62  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.50/2.62  tff(c_172, plain, (![C_73, A_74, B_75]: (v1_xboole_0(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))) | ~v1_xboole_0(A_74))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.50/2.62  tff(c_189, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_58, c_172])).
% 7.50/2.62  tff(c_192, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_189])).
% 7.50/2.62  tff(c_62, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.50/2.62  tff(c_60, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.50/2.62  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.50/2.62  tff(c_54, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.50/2.62  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.50/2.62  tff(c_40, plain, (![A_42]: (k6_relat_1(A_42)=k6_partfun1(A_42))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.50/2.62  tff(c_10, plain, (![A_3]: (v2_funct_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.50/2.62  tff(c_63, plain, (![A_3]: (v2_funct_1(k6_partfun1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_10])).
% 7.50/2.62  tff(c_1920, plain, (![D_183, E_181, F_180, B_182, A_184, C_179]: (k4_relset_1(A_184, B_182, C_179, D_183, E_181, F_180)=k5_relat_1(E_181, F_180) | ~m1_subset_1(F_180, k1_zfmisc_1(k2_zfmisc_1(C_179, D_183))) | ~m1_subset_1(E_181, k1_zfmisc_1(k2_zfmisc_1(A_184, B_182))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.50/2.62  tff(c_2175, plain, (![A_200, B_201, E_202]: (k4_relset_1(A_200, B_201, '#skF_2', '#skF_1', E_202, '#skF_4')=k5_relat_1(E_202, '#skF_4') | ~m1_subset_1(E_202, k1_zfmisc_1(k2_zfmisc_1(A_200, B_201))))), inference(resolution, [status(thm)], [c_52, c_1920])).
% 7.50/2.62  tff(c_2202, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_2175])).
% 7.50/2.62  tff(c_20, plain, (![E_18, C_16, D_17, F_19, A_14, B_15]: (m1_subset_1(k4_relset_1(A_14, B_15, C_16, D_17, E_18, F_19), k1_zfmisc_1(k2_zfmisc_1(A_14, D_17))) | ~m1_subset_1(F_19, k1_zfmisc_1(k2_zfmisc_1(C_16, D_17))) | ~m1_subset_1(E_18, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.50/2.62  tff(c_2341, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_2202, c_20])).
% 7.50/2.62  tff(c_2345, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_52, c_2341])).
% 7.50/2.62  tff(c_2250, plain, (![D_205, F_203, B_206, C_207, A_204, E_208]: (k1_partfun1(A_204, B_206, C_207, D_205, E_208, F_203)=k5_relat_1(E_208, F_203) | ~m1_subset_1(F_203, k1_zfmisc_1(k2_zfmisc_1(C_207, D_205))) | ~v1_funct_1(F_203) | ~m1_subset_1(E_208, k1_zfmisc_1(k2_zfmisc_1(A_204, B_206))) | ~v1_funct_1(E_208))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.50/2.62  tff(c_2266, plain, (![A_204, B_206, E_208]: (k1_partfun1(A_204, B_206, '#skF_2', '#skF_1', E_208, '#skF_4')=k5_relat_1(E_208, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_208, k1_zfmisc_1(k2_zfmisc_1(A_204, B_206))) | ~v1_funct_1(E_208))), inference(resolution, [status(thm)], [c_52, c_2250])).
% 7.50/2.62  tff(c_2915, plain, (![A_231, B_232, E_233]: (k1_partfun1(A_231, B_232, '#skF_2', '#skF_1', E_233, '#skF_4')=k5_relat_1(E_233, '#skF_4') | ~m1_subset_1(E_233, k1_zfmisc_1(k2_zfmisc_1(A_231, B_232))) | ~v1_funct_1(E_233))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2266])).
% 7.50/2.62  tff(c_2951, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2915])).
% 7.50/2.62  tff(c_2972, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2951])).
% 7.50/2.62  tff(c_36, plain, (![A_35]: (m1_subset_1(k6_partfun1(A_35), k1_zfmisc_1(k2_zfmisc_1(A_35, A_35))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.50/2.62  tff(c_50, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.50/2.62  tff(c_1557, plain, (![D_164, C_165, A_166, B_167]: (D_164=C_165 | ~r2_relset_1(A_166, B_167, C_165, D_164) | ~m1_subset_1(D_164, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.50/2.62  tff(c_1567, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_50, c_1557])).
% 7.50/2.62  tff(c_1586, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1567])).
% 7.50/2.62  tff(c_1611, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1586])).
% 7.50/2.62  tff(c_3470, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2972, c_1611])).
% 7.50/2.62  tff(c_3474, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2345, c_3470])).
% 7.50/2.62  tff(c_3475, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1586])).
% 7.50/2.62  tff(c_4352, plain, (![D_289, A_291, B_290, C_292, E_288]: (k1_xboole_0=C_292 | v2_funct_1(D_289) | ~v2_funct_1(k1_partfun1(A_291, B_290, B_290, C_292, D_289, E_288)) | ~m1_subset_1(E_288, k1_zfmisc_1(k2_zfmisc_1(B_290, C_292))) | ~v1_funct_2(E_288, B_290, C_292) | ~v1_funct_1(E_288) | ~m1_subset_1(D_289, k1_zfmisc_1(k2_zfmisc_1(A_291, B_290))) | ~v1_funct_2(D_289, A_291, B_290) | ~v1_funct_1(D_289))), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.50/2.62  tff(c_4354, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3475, c_4352])).
% 7.50/2.62  tff(c_4356, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_54, c_52, c_63, c_4354])).
% 7.50/2.62  tff(c_4357, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_99, c_4356])).
% 7.50/2.62  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 7.50/2.62  tff(c_4389, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4357, c_2])).
% 7.50/2.62  tff(c_4391, plain, $false, inference(negUnitSimplification, [status(thm)], [c_192, c_4389])).
% 7.50/2.62  tff(c_4392, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_189])).
% 7.50/2.62  tff(c_100, plain, (![B_59, A_60]: (~v1_xboole_0(B_59) | B_59=A_60 | ~v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.50/2.62  tff(c_103, plain, (![A_60]: (k1_xboole_0=A_60 | ~v1_xboole_0(A_60))), inference(resolution, [status(thm)], [c_2, c_100])).
% 7.50/2.62  tff(c_4399, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_4392, c_103])).
% 7.50/2.62  tff(c_72, plain, (![A_58]: (k6_relat_1(A_58)=k6_partfun1(A_58))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.50/2.62  tff(c_6, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.50/2.62  tff(c_78, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_72, c_6])).
% 7.50/2.62  tff(c_94, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_78, c_63])).
% 7.50/2.62  tff(c_4413, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4399, c_94])).
% 7.50/2.62  tff(c_4419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_4413])).
% 7.50/2.62  tff(c_4420, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 7.50/2.62  tff(c_4436, plain, (![C_297, A_298, B_299]: (v1_relat_1(C_297) | ~m1_subset_1(C_297, k1_zfmisc_1(k2_zfmisc_1(A_298, B_299))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.50/2.62  tff(c_4454, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_4436])).
% 7.50/2.62  tff(c_4472, plain, (![C_303, B_304, A_305]: (v5_relat_1(C_303, B_304) | ~m1_subset_1(C_303, k1_zfmisc_1(k2_zfmisc_1(A_305, B_304))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.50/2.62  tff(c_4488, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_52, c_4472])).
% 7.50/2.62  tff(c_4628, plain, (![A_320, B_321, C_322]: (k2_relset_1(A_320, B_321, C_322)=k2_relat_1(C_322) | ~m1_subset_1(C_322, k1_zfmisc_1(k2_zfmisc_1(A_320, B_321))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.50/2.62  tff(c_4644, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_4628])).
% 7.50/2.62  tff(c_5631, plain, (![A_378, B_379, C_380, D_381]: (k2_relset_1(A_378, B_379, C_380)=B_379 | ~r2_relset_1(B_379, B_379, k1_partfun1(B_379, A_378, A_378, B_379, D_381, C_380), k6_partfun1(B_379)) | ~m1_subset_1(D_381, k1_zfmisc_1(k2_zfmisc_1(B_379, A_378))) | ~v1_funct_2(D_381, B_379, A_378) | ~v1_funct_1(D_381) | ~m1_subset_1(C_380, k1_zfmisc_1(k2_zfmisc_1(A_378, B_379))) | ~v1_funct_2(C_380, A_378, B_379) | ~v1_funct_1(C_380))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.50/2.62  tff(c_5643, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_5631])).
% 7.50/2.62  tff(c_5649, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_62, c_60, c_58, c_4644, c_5643])).
% 7.50/2.62  tff(c_30, plain, (![B_34]: (v2_funct_2(B_34, k2_relat_1(B_34)) | ~v5_relat_1(B_34, k2_relat_1(B_34)) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.50/2.62  tff(c_5654, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5649, c_30])).
% 7.50/2.62  tff(c_5658, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4454, c_4488, c_5649, c_5654])).
% 7.50/2.62  tff(c_5660, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4420, c_5658])).
% 7.50/2.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.50/2.62  
% 7.50/2.62  Inference rules
% 7.50/2.62  ----------------------
% 7.50/2.62  #Ref     : 0
% 7.50/2.62  #Sup     : 1468
% 7.50/2.62  #Fact    : 0
% 7.50/2.62  #Define  : 0
% 7.50/2.62  #Split   : 20
% 7.50/2.62  #Chain   : 0
% 7.50/2.62  #Close   : 0
% 7.50/2.62  
% 7.50/2.62  Ordering : KBO
% 7.50/2.62  
% 7.50/2.62  Simplification rules
% 7.50/2.62  ----------------------
% 7.50/2.62  #Subsume      : 173
% 7.50/2.62  #Demod        : 738
% 7.50/2.62  #Tautology    : 374
% 7.50/2.62  #SimpNegUnit  : 5
% 7.50/2.62  #BackRed      : 67
% 7.50/2.62  
% 7.50/2.62  #Partial instantiations: 0
% 7.50/2.62  #Strategies tried      : 1
% 7.50/2.62  
% 7.50/2.62  Timing (in seconds)
% 7.50/2.62  ----------------------
% 7.50/2.62  Preprocessing        : 0.39
% 7.50/2.62  Parsing              : 0.21
% 7.50/2.62  CNF conversion       : 0.03
% 7.50/2.62  Main loop            : 1.40
% 7.50/2.62  Inferencing          : 0.44
% 7.50/2.62  Reduction            : 0.49
% 7.50/2.62  Demodulation         : 0.36
% 7.50/2.62  BG Simplification    : 0.05
% 7.50/2.62  Subsumption          : 0.29
% 7.50/2.62  Abstraction          : 0.07
% 7.50/2.62  MUC search           : 0.00
% 7.50/2.62  Cooper               : 0.00
% 7.50/2.62  Total                : 1.82
% 7.50/2.62  Index Insertion      : 0.00
% 7.50/2.63  Index Deletion       : 0.00
% 7.50/2.63  Index Matching       : 0.00
% 7.50/2.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
