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
% DateTime   : Thu Dec  3 10:12:04 EST 2020

% Result     : Theorem 8.76s
% Output     : CNFRefutation 9.20s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 244 expanded)
%              Number of leaves         :   45 ( 105 expanded)
%              Depth                    :   10
%              Number of atoms          :  207 ( 727 expanded)
%              Number of equality atoms :   42 (  65 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_174,negated_conjecture,(
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

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_115,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_52,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_85,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_113,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_95,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_154,axiom,(
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

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_132,axiom,(
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

tff(f_103,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_48,plain,
    ( ~ v2_funct_2('#skF_5','#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_76,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_166,plain,(
    ! [C_83,A_84,B_85] :
      ( v1_xboole_0(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85)))
      | ~ v1_xboole_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_183,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_166])).

tff(c_185,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_60,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_54,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_40,plain,(
    ! [A_47] : k6_relat_1(A_47) = k6_partfun1(A_47) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_12,plain,(
    ! [A_8] : v2_funct_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_64,plain,(
    ! [A_8] : v2_funct_1(k6_partfun1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_12])).

tff(c_1265,plain,(
    ! [C_182,A_181,B_183,D_184,E_180,F_179] :
      ( k4_relset_1(A_181,B_183,C_182,D_184,E_180,F_179) = k5_relat_1(E_180,F_179)
      | ~ m1_subset_1(F_179,k1_zfmisc_1(k2_zfmisc_1(C_182,D_184)))
      | ~ m1_subset_1(E_180,k1_zfmisc_1(k2_zfmisc_1(A_181,B_183))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1338,plain,(
    ! [A_190,B_191,E_192] :
      ( k4_relset_1(A_190,B_191,'#skF_3','#skF_2',E_192,'#skF_5') = k5_relat_1(E_192,'#skF_5')
      | ~ m1_subset_1(E_192,k1_zfmisc_1(k2_zfmisc_1(A_190,B_191))) ) ),
    inference(resolution,[status(thm)],[c_52,c_1265])).

tff(c_1363,plain,(
    k4_relset_1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_1338])).

tff(c_1427,plain,(
    ! [E_197,C_196,D_201,B_198,A_199,F_200] :
      ( m1_subset_1(k4_relset_1(A_199,B_198,C_196,D_201,E_197,F_200),k1_zfmisc_1(k2_zfmisc_1(A_199,D_201)))
      | ~ m1_subset_1(F_200,k1_zfmisc_1(k2_zfmisc_1(C_196,D_201)))
      | ~ m1_subset_1(E_197,k1_zfmisc_1(k2_zfmisc_1(A_199,B_198))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1455,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1363,c_1427])).

tff(c_1469,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_1455])).

tff(c_1590,plain,(
    ! [E_205,B_210,A_206,D_208,C_207,F_209] :
      ( k1_partfun1(A_206,B_210,C_207,D_208,E_205,F_209) = k5_relat_1(E_205,F_209)
      | ~ m1_subset_1(F_209,k1_zfmisc_1(k2_zfmisc_1(C_207,D_208)))
      | ~ v1_funct_1(F_209)
      | ~ m1_subset_1(E_205,k1_zfmisc_1(k2_zfmisc_1(A_206,B_210)))
      | ~ v1_funct_1(E_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1607,plain,(
    ! [A_206,B_210,E_205] :
      ( k1_partfun1(A_206,B_210,'#skF_3','#skF_2',E_205,'#skF_5') = k5_relat_1(E_205,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_205,k1_zfmisc_1(k2_zfmisc_1(A_206,B_210)))
      | ~ v1_funct_1(E_205) ) ),
    inference(resolution,[status(thm)],[c_52,c_1590])).

tff(c_2550,plain,(
    ! [A_251,B_252,E_253] :
      ( k1_partfun1(A_251,B_252,'#skF_3','#skF_2',E_253,'#skF_5') = k5_relat_1(E_253,'#skF_5')
      | ~ m1_subset_1(E_253,k1_zfmisc_1(k2_zfmisc_1(A_251,B_252)))
      | ~ v1_funct_1(E_253) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1607])).

tff(c_2587,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_2550])).

tff(c_2602,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2587])).

tff(c_32,plain,(
    ! [A_38] : m1_subset_1(k6_relat_1(A_38),k1_zfmisc_1(k2_zfmisc_1(A_38,A_38))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_63,plain,(
    ! [A_38] : m1_subset_1(k6_partfun1(A_38),k1_zfmisc_1(k2_zfmisc_1(A_38,A_38))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32])).

tff(c_50,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_1194,plain,(
    ! [D_167,C_168,A_169,B_170] :
      ( D_167 = C_168
      | ~ r2_relset_1(A_169,B_170,C_168,D_167)
      | ~ m1_subset_1(D_167,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170)))
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1204,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_50,c_1194])).

tff(c_1223,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_1204])).

tff(c_5027,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1223])).

tff(c_9821,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2602,c_5027])).

tff(c_9825,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1469,c_9821])).

tff(c_9826,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1223])).

tff(c_46,plain,(
    ! [A_53,D_56,E_58,C_55,B_54] :
      ( k1_xboole_0 = C_55
      | v2_funct_1(D_56)
      | ~ v2_funct_1(k1_partfun1(A_53,B_54,B_54,C_55,D_56,E_58))
      | ~ m1_subset_1(E_58,k1_zfmisc_1(k2_zfmisc_1(B_54,C_55)))
      | ~ v1_funct_2(E_58,B_54,C_55)
      | ~ v1_funct_1(E_58)
      | ~ m1_subset_1(D_56,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54)))
      | ~ v1_funct_2(D_56,A_53,B_54)
      | ~ v1_funct_1(D_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_9940,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_9826,c_46])).

tff(c_9946,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_54,c_52,c_64,c_9940])).

tff(c_9947,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_9946])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_10007,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9947,c_2])).

tff(c_10009,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_185,c_10007])).

tff(c_10010,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_10083,plain,(
    ! [A_497] :
      ( v1_xboole_0(k6_partfun1(A_497))
      | ~ v1_xboole_0(A_497) ) ),
    inference(resolution,[status(thm)],[c_63,c_166])).

tff(c_77,plain,(
    ! [B_63,A_64] :
      ( ~ v1_xboole_0(B_63)
      | B_63 = A_64
      | ~ v1_xboole_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_80,plain,(
    ! [A_64] :
      ( k1_xboole_0 = A_64
      | ~ v1_xboole_0(A_64) ) ),
    inference(resolution,[status(thm)],[c_2,c_77])).

tff(c_10017,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10010,c_80])).

tff(c_10011,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_10024,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_10011,c_80])).

tff(c_10033,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10017,c_10024])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10025,plain,(
    ! [A_1] :
      ( A_1 = '#skF_2'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_10011,c_4])).

tff(c_10049,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10033,c_10025])).

tff(c_10091,plain,(
    ! [A_498] :
      ( k6_partfun1(A_498) = '#skF_4'
      | ~ v1_xboole_0(A_498) ) ),
    inference(resolution,[status(thm)],[c_10083,c_10049])).

tff(c_10099,plain,(
    k6_partfun1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10010,c_10091])).

tff(c_10116,plain,(
    v2_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10099,c_64])).

tff(c_10124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_10116])).

tff(c_10125,plain,(
    ~ v2_funct_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_10139,plain,(
    ! [C_504,A_505,B_506] :
      ( v1_relat_1(C_504)
      | ~ m1_subset_1(C_504,k1_zfmisc_1(k2_zfmisc_1(A_505,B_506))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10156,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_10139])).

tff(c_10196,plain,(
    ! [C_514,B_515,A_516] :
      ( v5_relat_1(C_514,B_515)
      | ~ m1_subset_1(C_514,k1_zfmisc_1(k2_zfmisc_1(A_516,B_515))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_10213,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_10196])).

tff(c_10387,plain,(
    ! [A_533,B_534,C_535] :
      ( k2_relset_1(A_533,B_534,C_535) = k2_relat_1(C_535)
      | ~ m1_subset_1(C_535,k1_zfmisc_1(k2_zfmisc_1(A_533,B_534))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_10408,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_10387])).

tff(c_11016,plain,(
    ! [A_588,B_589,C_590,D_591] :
      ( k2_relset_1(A_588,B_589,C_590) = B_589
      | ~ r2_relset_1(B_589,B_589,k1_partfun1(B_589,A_588,A_588,B_589,D_591,C_590),k6_partfun1(B_589))
      | ~ m1_subset_1(D_591,k1_zfmisc_1(k2_zfmisc_1(B_589,A_588)))
      | ~ v1_funct_2(D_591,B_589,A_588)
      | ~ v1_funct_1(D_591)
      | ~ m1_subset_1(C_590,k1_zfmisc_1(k2_zfmisc_1(A_588,B_589)))
      | ~ v1_funct_2(C_590,A_588,B_589)
      | ~ v1_funct_1(C_590) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_11025,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_11016])).

tff(c_11028,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_62,c_60,c_58,c_10408,c_11025])).

tff(c_34,plain,(
    ! [B_40] :
      ( v2_funct_2(B_40,k2_relat_1(B_40))
      | ~ v5_relat_1(B_40,k2_relat_1(B_40))
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_11033,plain,
    ( v2_funct_2('#skF_5',k2_relat_1('#skF_5'))
    | ~ v5_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_11028,c_34])).

tff(c_11037,plain,(
    v2_funct_2('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10156,c_10213,c_11028,c_11033])).

tff(c_11039,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10125,c_11037])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:06:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.76/3.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.06/3.19  
% 9.06/3.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.06/3.19  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 9.06/3.19  
% 9.06/3.19  %Foreground sorts:
% 9.06/3.19  
% 9.06/3.19  
% 9.06/3.19  %Background operators:
% 9.06/3.19  
% 9.06/3.19  
% 9.06/3.19  %Foreground operators:
% 9.06/3.19  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.06/3.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.06/3.19  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.06/3.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.06/3.19  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.06/3.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.06/3.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.06/3.19  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.06/3.19  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.06/3.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.06/3.19  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.06/3.19  tff('#skF_5', type, '#skF_5': $i).
% 9.06/3.19  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.06/3.19  tff('#skF_2', type, '#skF_2': $i).
% 9.06/3.19  tff('#skF_3', type, '#skF_3': $i).
% 9.06/3.19  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 9.06/3.19  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.06/3.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.06/3.19  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.06/3.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.06/3.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.06/3.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.06/3.19  tff('#skF_4', type, '#skF_4': $i).
% 9.06/3.19  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.06/3.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.06/3.19  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.06/3.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.06/3.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.06/3.19  
% 9.20/3.21  tff(f_174, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 9.20/3.21  tff(f_69, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 9.20/3.21  tff(f_115, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.20/3.21  tff(f_52, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 9.20/3.21  tff(f_85, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 9.20/3.21  tff(f_75, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 9.20/3.21  tff(f_113, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 9.20/3.21  tff(f_95, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 9.20/3.21  tff(f_93, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 9.20/3.21  tff(f_154, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 9.20/3.21  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.20/3.21  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 9.20/3.21  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.20/3.21  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.20/3.21  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.20/3.21  tff(f_132, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 9.20/3.21  tff(f_103, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 9.20/3.21  tff(c_48, plain, (~v2_funct_2('#skF_5', '#skF_2') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_174])).
% 9.20/3.21  tff(c_76, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_48])).
% 9.20/3.21  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_174])).
% 9.20/3.21  tff(c_166, plain, (![C_83, A_84, B_85]: (v1_xboole_0(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))) | ~v1_xboole_0(A_84))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.20/3.21  tff(c_183, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_166])).
% 9.20/3.21  tff(c_185, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_183])).
% 9.20/3.21  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_174])).
% 9.20/3.21  tff(c_60, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_174])).
% 9.20/3.21  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_174])).
% 9.20/3.21  tff(c_54, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_174])).
% 9.20/3.21  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_174])).
% 9.20/3.21  tff(c_40, plain, (![A_47]: (k6_relat_1(A_47)=k6_partfun1(A_47))), inference(cnfTransformation, [status(thm)], [f_115])).
% 9.20/3.21  tff(c_12, plain, (![A_8]: (v2_funct_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.20/3.21  tff(c_64, plain, (![A_8]: (v2_funct_1(k6_partfun1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_12])).
% 9.20/3.21  tff(c_1265, plain, (![C_182, A_181, B_183, D_184, E_180, F_179]: (k4_relset_1(A_181, B_183, C_182, D_184, E_180, F_179)=k5_relat_1(E_180, F_179) | ~m1_subset_1(F_179, k1_zfmisc_1(k2_zfmisc_1(C_182, D_184))) | ~m1_subset_1(E_180, k1_zfmisc_1(k2_zfmisc_1(A_181, B_183))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.20/3.21  tff(c_1338, plain, (![A_190, B_191, E_192]: (k4_relset_1(A_190, B_191, '#skF_3', '#skF_2', E_192, '#skF_5')=k5_relat_1(E_192, '#skF_5') | ~m1_subset_1(E_192, k1_zfmisc_1(k2_zfmisc_1(A_190, B_191))))), inference(resolution, [status(thm)], [c_52, c_1265])).
% 9.20/3.21  tff(c_1363, plain, (k4_relset_1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_58, c_1338])).
% 9.20/3.21  tff(c_1427, plain, (![E_197, C_196, D_201, B_198, A_199, F_200]: (m1_subset_1(k4_relset_1(A_199, B_198, C_196, D_201, E_197, F_200), k1_zfmisc_1(k2_zfmisc_1(A_199, D_201))) | ~m1_subset_1(F_200, k1_zfmisc_1(k2_zfmisc_1(C_196, D_201))) | ~m1_subset_1(E_197, k1_zfmisc_1(k2_zfmisc_1(A_199, B_198))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.20/3.21  tff(c_1455, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1363, c_1427])).
% 9.20/3.21  tff(c_1469, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_52, c_1455])).
% 9.20/3.21  tff(c_1590, plain, (![E_205, B_210, A_206, D_208, C_207, F_209]: (k1_partfun1(A_206, B_210, C_207, D_208, E_205, F_209)=k5_relat_1(E_205, F_209) | ~m1_subset_1(F_209, k1_zfmisc_1(k2_zfmisc_1(C_207, D_208))) | ~v1_funct_1(F_209) | ~m1_subset_1(E_205, k1_zfmisc_1(k2_zfmisc_1(A_206, B_210))) | ~v1_funct_1(E_205))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.20/3.21  tff(c_1607, plain, (![A_206, B_210, E_205]: (k1_partfun1(A_206, B_210, '#skF_3', '#skF_2', E_205, '#skF_5')=k5_relat_1(E_205, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_205, k1_zfmisc_1(k2_zfmisc_1(A_206, B_210))) | ~v1_funct_1(E_205))), inference(resolution, [status(thm)], [c_52, c_1590])).
% 9.20/3.21  tff(c_2550, plain, (![A_251, B_252, E_253]: (k1_partfun1(A_251, B_252, '#skF_3', '#skF_2', E_253, '#skF_5')=k5_relat_1(E_253, '#skF_5') | ~m1_subset_1(E_253, k1_zfmisc_1(k2_zfmisc_1(A_251, B_252))) | ~v1_funct_1(E_253))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1607])).
% 9.20/3.21  tff(c_2587, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_2550])).
% 9.20/3.21  tff(c_2602, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2587])).
% 9.20/3.21  tff(c_32, plain, (![A_38]: (m1_subset_1(k6_relat_1(A_38), k1_zfmisc_1(k2_zfmisc_1(A_38, A_38))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.20/3.21  tff(c_63, plain, (![A_38]: (m1_subset_1(k6_partfun1(A_38), k1_zfmisc_1(k2_zfmisc_1(A_38, A_38))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32])).
% 9.20/3.21  tff(c_50, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_174])).
% 9.20/3.21  tff(c_1194, plain, (![D_167, C_168, A_169, B_170]: (D_167=C_168 | ~r2_relset_1(A_169, B_170, C_168, D_167) | ~m1_subset_1(D_167, k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.20/3.21  tff(c_1204, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_50, c_1194])).
% 9.20/3.21  tff(c_1223, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_1204])).
% 9.20/3.21  tff(c_5027, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1223])).
% 9.20/3.21  tff(c_9821, plain, (~m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2602, c_5027])).
% 9.20/3.21  tff(c_9825, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1469, c_9821])).
% 9.20/3.21  tff(c_9826, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_1223])).
% 9.20/3.21  tff(c_46, plain, (![A_53, D_56, E_58, C_55, B_54]: (k1_xboole_0=C_55 | v2_funct_1(D_56) | ~v2_funct_1(k1_partfun1(A_53, B_54, B_54, C_55, D_56, E_58)) | ~m1_subset_1(E_58, k1_zfmisc_1(k2_zfmisc_1(B_54, C_55))) | ~v1_funct_2(E_58, B_54, C_55) | ~v1_funct_1(E_58) | ~m1_subset_1(D_56, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))) | ~v1_funct_2(D_56, A_53, B_54) | ~v1_funct_1(D_56))), inference(cnfTransformation, [status(thm)], [f_154])).
% 9.20/3.21  tff(c_9940, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_9826, c_46])).
% 9.20/3.21  tff(c_9946, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_54, c_52, c_64, c_9940])).
% 9.20/3.21  tff(c_9947, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_76, c_9946])).
% 9.20/3.21  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 9.20/3.21  tff(c_10007, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9947, c_2])).
% 9.20/3.21  tff(c_10009, plain, $false, inference(negUnitSimplification, [status(thm)], [c_185, c_10007])).
% 9.20/3.21  tff(c_10010, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_183])).
% 9.20/3.21  tff(c_10083, plain, (![A_497]: (v1_xboole_0(k6_partfun1(A_497)) | ~v1_xboole_0(A_497))), inference(resolution, [status(thm)], [c_63, c_166])).
% 9.20/3.21  tff(c_77, plain, (![B_63, A_64]: (~v1_xboole_0(B_63) | B_63=A_64 | ~v1_xboole_0(A_64))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.20/3.21  tff(c_80, plain, (![A_64]: (k1_xboole_0=A_64 | ~v1_xboole_0(A_64))), inference(resolution, [status(thm)], [c_2, c_77])).
% 9.20/3.21  tff(c_10017, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_10010, c_80])).
% 9.20/3.21  tff(c_10011, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_183])).
% 9.20/3.21  tff(c_10024, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_10011, c_80])).
% 9.20/3.21  tff(c_10033, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10017, c_10024])).
% 9.20/3.21  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.20/3.21  tff(c_10025, plain, (![A_1]: (A_1='#skF_2' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_10011, c_4])).
% 9.20/3.21  tff(c_10049, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_10033, c_10025])).
% 9.20/3.21  tff(c_10091, plain, (![A_498]: (k6_partfun1(A_498)='#skF_4' | ~v1_xboole_0(A_498))), inference(resolution, [status(thm)], [c_10083, c_10049])).
% 9.20/3.21  tff(c_10099, plain, (k6_partfun1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_10010, c_10091])).
% 9.20/3.21  tff(c_10116, plain, (v2_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10099, c_64])).
% 9.20/3.21  tff(c_10124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_10116])).
% 9.20/3.21  tff(c_10125, plain, (~v2_funct_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 9.20/3.21  tff(c_10139, plain, (![C_504, A_505, B_506]: (v1_relat_1(C_504) | ~m1_subset_1(C_504, k1_zfmisc_1(k2_zfmisc_1(A_505, B_506))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.20/3.21  tff(c_10156, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_10139])).
% 9.20/3.21  tff(c_10196, plain, (![C_514, B_515, A_516]: (v5_relat_1(C_514, B_515) | ~m1_subset_1(C_514, k1_zfmisc_1(k2_zfmisc_1(A_516, B_515))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.20/3.21  tff(c_10213, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_52, c_10196])).
% 9.20/3.21  tff(c_10387, plain, (![A_533, B_534, C_535]: (k2_relset_1(A_533, B_534, C_535)=k2_relat_1(C_535) | ~m1_subset_1(C_535, k1_zfmisc_1(k2_zfmisc_1(A_533, B_534))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.20/3.21  tff(c_10408, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_10387])).
% 9.20/3.21  tff(c_11016, plain, (![A_588, B_589, C_590, D_591]: (k2_relset_1(A_588, B_589, C_590)=B_589 | ~r2_relset_1(B_589, B_589, k1_partfun1(B_589, A_588, A_588, B_589, D_591, C_590), k6_partfun1(B_589)) | ~m1_subset_1(D_591, k1_zfmisc_1(k2_zfmisc_1(B_589, A_588))) | ~v1_funct_2(D_591, B_589, A_588) | ~v1_funct_1(D_591) | ~m1_subset_1(C_590, k1_zfmisc_1(k2_zfmisc_1(A_588, B_589))) | ~v1_funct_2(C_590, A_588, B_589) | ~v1_funct_1(C_590))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.20/3.21  tff(c_11025, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_11016])).
% 9.20/3.21  tff(c_11028, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_62, c_60, c_58, c_10408, c_11025])).
% 9.20/3.21  tff(c_34, plain, (![B_40]: (v2_funct_2(B_40, k2_relat_1(B_40)) | ~v5_relat_1(B_40, k2_relat_1(B_40)) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.20/3.21  tff(c_11033, plain, (v2_funct_2('#skF_5', k2_relat_1('#skF_5')) | ~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_11028, c_34])).
% 9.20/3.21  tff(c_11037, plain, (v2_funct_2('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10156, c_10213, c_11028, c_11033])).
% 9.20/3.21  tff(c_11039, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10125, c_11037])).
% 9.20/3.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.20/3.21  
% 9.20/3.21  Inference rules
% 9.20/3.21  ----------------------
% 9.20/3.21  #Ref     : 0
% 9.20/3.21  #Sup     : 2875
% 9.20/3.21  #Fact    : 0
% 9.20/3.21  #Define  : 0
% 9.20/3.21  #Split   : 27
% 9.20/3.21  #Chain   : 0
% 9.20/3.21  #Close   : 0
% 9.20/3.21  
% 9.20/3.21  Ordering : KBO
% 9.20/3.21  
% 9.20/3.21  Simplification rules
% 9.20/3.21  ----------------------
% 9.20/3.21  #Subsume      : 169
% 9.20/3.21  #Demod        : 1969
% 9.20/3.21  #Tautology    : 1016
% 9.20/3.21  #SimpNegUnit  : 5
% 9.20/3.21  #BackRed      : 96
% 9.20/3.21  
% 9.20/3.21  #Partial instantiations: 0
% 9.20/3.21  #Strategies tried      : 1
% 9.20/3.21  
% 9.20/3.21  Timing (in seconds)
% 9.20/3.21  ----------------------
% 9.20/3.21  Preprocessing        : 0.35
% 9.20/3.21  Parsing              : 0.19
% 9.20/3.21  CNF conversion       : 0.02
% 9.20/3.21  Main loop            : 2.08
% 9.20/3.21  Inferencing          : 0.55
% 9.20/3.21  Reduction            : 0.80
% 9.20/3.21  Demodulation         : 0.60
% 9.20/3.21  BG Simplification    : 0.07
% 9.20/3.21  Subsumption          : 0.49
% 9.20/3.21  Abstraction          : 0.09
% 9.20/3.21  MUC search           : 0.00
% 9.20/3.21  Cooper               : 0.00
% 9.20/3.21  Total                : 2.47
% 9.20/3.21  Index Insertion      : 0.00
% 9.20/3.21  Index Deletion       : 0.00
% 9.20/3.21  Index Matching       : 0.00
% 9.20/3.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
