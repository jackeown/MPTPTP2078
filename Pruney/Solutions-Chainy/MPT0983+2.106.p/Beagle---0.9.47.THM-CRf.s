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
% DateTime   : Thu Dec  3 10:12:16 EST 2020

% Result     : Theorem 7.46s
% Output     : CNFRefutation 7.46s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 214 expanded)
%              Number of leaves         :   47 (  96 expanded)
%              Depth                    :    9
%              Number of atoms          :  204 ( 646 expanded)
%              Number of equality atoms :   39 (  57 expanded)
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

tff(f_182,negated_conjecture,(
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

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_123,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_93,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_121,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_103,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_162,axiom,(
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

tff(f_60,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_59,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_140,axiom,(
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

tff(f_111,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_54,plain,
    ( ~ v2_funct_2('#skF_5','#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_103,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_230,plain,(
    ! [C_88,A_89,B_90] :
      ( v1_xboole_0(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90)))
      | ~ v1_xboole_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_252,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_230])).

tff(c_254,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_252])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_66,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_60,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_46,plain,(
    ! [A_49] : k6_relat_1(A_49) = k6_partfun1(A_49) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_20,plain,(
    ! [A_13] : v2_funct_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_70,plain,(
    ! [A_13] : v2_funct_1(k6_partfun1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_20])).

tff(c_1787,plain,(
    ! [C_196,D_201,E_200,F_198,B_197,A_199] :
      ( k4_relset_1(A_199,B_197,C_196,D_201,E_200,F_198) = k5_relat_1(E_200,F_198)
      | ~ m1_subset_1(F_198,k1_zfmisc_1(k2_zfmisc_1(C_196,D_201)))
      | ~ m1_subset_1(E_200,k1_zfmisc_1(k2_zfmisc_1(A_199,B_197))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2040,plain,(
    ! [A_206,B_207,E_208] :
      ( k4_relset_1(A_206,B_207,'#skF_3','#skF_2',E_208,'#skF_5') = k5_relat_1(E_208,'#skF_5')
      | ~ m1_subset_1(E_208,k1_zfmisc_1(k2_zfmisc_1(A_206,B_207))) ) ),
    inference(resolution,[status(thm)],[c_58,c_1787])).

tff(c_2064,plain,(
    k4_relset_1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_2040])).

tff(c_2155,plain,(
    ! [E_217,B_216,C_214,D_213,F_215,A_212] :
      ( m1_subset_1(k4_relset_1(A_212,B_216,C_214,D_213,E_217,F_215),k1_zfmisc_1(k2_zfmisc_1(A_212,D_213)))
      | ~ m1_subset_1(F_215,k1_zfmisc_1(k2_zfmisc_1(C_214,D_213)))
      | ~ m1_subset_1(E_217,k1_zfmisc_1(k2_zfmisc_1(A_212,B_216))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2189,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2064,c_2155])).

tff(c_2206,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_58,c_2189])).

tff(c_2329,plain,(
    ! [C_221,A_224,B_225,D_222,F_223,E_226] :
      ( k1_partfun1(A_224,B_225,C_221,D_222,E_226,F_223) = k5_relat_1(E_226,F_223)
      | ~ m1_subset_1(F_223,k1_zfmisc_1(k2_zfmisc_1(C_221,D_222)))
      | ~ v1_funct_1(F_223)
      | ~ m1_subset_1(E_226,k1_zfmisc_1(k2_zfmisc_1(A_224,B_225)))
      | ~ v1_funct_1(E_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2348,plain,(
    ! [A_224,B_225,E_226] :
      ( k1_partfun1(A_224,B_225,'#skF_3','#skF_2',E_226,'#skF_5') = k5_relat_1(E_226,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_226,k1_zfmisc_1(k2_zfmisc_1(A_224,B_225)))
      | ~ v1_funct_1(E_226) ) ),
    inference(resolution,[status(thm)],[c_58,c_2329])).

tff(c_4394,plain,(
    ! [A_294,B_295,E_296] :
      ( k1_partfun1(A_294,B_295,'#skF_3','#skF_2',E_296,'#skF_5') = k5_relat_1(E_296,'#skF_5')
      | ~ m1_subset_1(E_296,k1_zfmisc_1(k2_zfmisc_1(A_294,B_295)))
      | ~ v1_funct_1(E_296) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2348])).

tff(c_4434,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_4394])).

tff(c_4449,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_4434])).

tff(c_38,plain,(
    ! [A_40] : m1_subset_1(k6_relat_1(A_40),k1_zfmisc_1(k2_zfmisc_1(A_40,A_40))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_69,plain,(
    ! [A_40] : m1_subset_1(k6_partfun1(A_40),k1_zfmisc_1(k2_zfmisc_1(A_40,A_40))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_38])).

tff(c_56,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_1641,plain,(
    ! [D_180,C_181,A_182,B_183] :
      ( D_180 = C_181
      | ~ r2_relset_1(A_182,B_183,C_181,D_180)
      | ~ m1_subset_1(D_180,k1_zfmisc_1(k2_zfmisc_1(A_182,B_183)))
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_182,B_183))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1651,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_56,c_1641])).

tff(c_1670,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_1651])).

tff(c_1703,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1670])).

tff(c_5095,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4449,c_1703])).

tff(c_5099,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2206,c_5095])).

tff(c_5100,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1670])).

tff(c_5962,plain,(
    ! [A_353,D_352,C_355,B_351,E_354] :
      ( k1_xboole_0 = C_355
      | v2_funct_1(D_352)
      | ~ v2_funct_1(k1_partfun1(A_353,B_351,B_351,C_355,D_352,E_354))
      | ~ m1_subset_1(E_354,k1_zfmisc_1(k2_zfmisc_1(B_351,C_355)))
      | ~ v1_funct_2(E_354,B_351,C_355)
      | ~ v1_funct_1(E_354)
      | ~ m1_subset_1(D_352,k1_zfmisc_1(k2_zfmisc_1(A_353,B_351)))
      | ~ v1_funct_2(D_352,A_353,B_351)
      | ~ v1_funct_1(D_352) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_5964,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5100,c_5962])).

tff(c_5966,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_62,c_60,c_58,c_70,c_5964])).

tff(c_5967,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_5966])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_5994,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5967,c_2])).

tff(c_5996,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_254,c_5994])).

tff(c_5997,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_105,plain,(
    ! [B_68,A_69] :
      ( ~ v1_xboole_0(B_68)
      | B_68 = A_69
      | ~ v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_108,plain,(
    ! [A_69] :
      ( k1_xboole_0 = A_69
      | ~ v1_xboole_0(A_69) ) ),
    inference(resolution,[status(thm)],[c_2,c_105])).

tff(c_6004,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5997,c_108])).

tff(c_79,plain,(
    ! [A_66] : k6_relat_1(A_66) = k6_partfun1(A_66) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_16,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_85,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_16])).

tff(c_98,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_70])).

tff(c_6018,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6004,c_98])).

tff(c_6024,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_6018])).

tff(c_6025,plain,(
    ~ v2_funct_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_14,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6043,plain,(
    ! [B_362,A_363] :
      ( v1_relat_1(B_362)
      | ~ m1_subset_1(B_362,k1_zfmisc_1(A_363))
      | ~ v1_relat_1(A_363) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6058,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_6043])).

tff(c_6071,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_6058])).

tff(c_6120,plain,(
    ! [C_371,B_372,A_373] :
      ( v5_relat_1(C_371,B_372)
      | ~ m1_subset_1(C_371,k1_zfmisc_1(k2_zfmisc_1(A_373,B_372))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6141,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_6120])).

tff(c_6286,plain,(
    ! [A_388,B_389,C_390] :
      ( k2_relset_1(A_388,B_389,C_390) = k2_relat_1(C_390)
      | ~ m1_subset_1(C_390,k1_zfmisc_1(k2_zfmisc_1(A_388,B_389))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_6307,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_6286])).

tff(c_7063,plain,(
    ! [A_446,B_447,C_448,D_449] :
      ( k2_relset_1(A_446,B_447,C_448) = B_447
      | ~ r2_relset_1(B_447,B_447,k1_partfun1(B_447,A_446,A_446,B_447,D_449,C_448),k6_partfun1(B_447))
      | ~ m1_subset_1(D_449,k1_zfmisc_1(k2_zfmisc_1(B_447,A_446)))
      | ~ v1_funct_2(D_449,B_447,A_446)
      | ~ v1_funct_1(D_449)
      | ~ m1_subset_1(C_448,k1_zfmisc_1(k2_zfmisc_1(A_446,B_447)))
      | ~ v1_funct_2(C_448,A_446,B_447)
      | ~ v1_funct_1(C_448) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_7069,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_7063])).

tff(c_7075,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_68,c_66,c_64,c_6307,c_7069])).

tff(c_40,plain,(
    ! [B_42] :
      ( v2_funct_2(B_42,k2_relat_1(B_42))
      | ~ v5_relat_1(B_42,k2_relat_1(B_42))
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_7080,plain,
    ( v2_funct_2('#skF_5',k2_relat_1('#skF_5'))
    | ~ v5_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7075,c_40])).

tff(c_7084,plain,(
    v2_funct_2('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6071,c_6141,c_7075,c_7080])).

tff(c_7086,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6025,c_7084])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:02:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.46/2.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.46/2.54  
% 7.46/2.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.46/2.54  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 7.46/2.54  
% 7.46/2.54  %Foreground sorts:
% 7.46/2.54  
% 7.46/2.54  
% 7.46/2.54  %Background operators:
% 7.46/2.54  
% 7.46/2.54  
% 7.46/2.54  %Foreground operators:
% 7.46/2.54  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.46/2.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.46/2.54  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.46/2.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.46/2.54  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.46/2.54  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.46/2.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.46/2.54  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.46/2.54  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.46/2.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.46/2.54  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.46/2.54  tff('#skF_5', type, '#skF_5': $i).
% 7.46/2.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.46/2.54  tff('#skF_2', type, '#skF_2': $i).
% 7.46/2.54  tff('#skF_3', type, '#skF_3': $i).
% 7.46/2.54  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 7.46/2.54  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.46/2.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.46/2.54  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.46/2.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.46/2.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.46/2.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.46/2.54  tff('#skF_4', type, '#skF_4': $i).
% 7.46/2.54  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.46/2.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.46/2.54  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.46/2.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.46/2.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.46/2.54  
% 7.46/2.56  tff(f_182, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 7.46/2.56  tff(f_77, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 7.46/2.56  tff(f_123, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.46/2.56  tff(f_64, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 7.46/2.56  tff(f_93, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 7.46/2.56  tff(f_83, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 7.46/2.56  tff(f_121, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.46/2.56  tff(f_103, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 7.46/2.56  tff(f_101, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.46/2.56  tff(f_162, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 7.46/2.56  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.46/2.56  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 7.46/2.56  tff(f_60, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 7.46/2.56  tff(f_59, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.46/2.56  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.46/2.56  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.46/2.56  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.46/2.56  tff(f_140, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 7.46/2.56  tff(f_111, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 7.46/2.56  tff(c_54, plain, (~v2_funct_2('#skF_5', '#skF_2') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.46/2.56  tff(c_103, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_54])).
% 7.46/2.56  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.46/2.56  tff(c_230, plain, (![C_88, A_89, B_90]: (v1_xboole_0(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))) | ~v1_xboole_0(A_89))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.46/2.56  tff(c_252, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_230])).
% 7.46/2.56  tff(c_254, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_252])).
% 7.46/2.56  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.46/2.56  tff(c_66, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.46/2.56  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.46/2.56  tff(c_60, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.46/2.56  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.46/2.56  tff(c_46, plain, (![A_49]: (k6_relat_1(A_49)=k6_partfun1(A_49))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.46/2.56  tff(c_20, plain, (![A_13]: (v2_funct_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.46/2.56  tff(c_70, plain, (![A_13]: (v2_funct_1(k6_partfun1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_20])).
% 7.46/2.56  tff(c_1787, plain, (![C_196, D_201, E_200, F_198, B_197, A_199]: (k4_relset_1(A_199, B_197, C_196, D_201, E_200, F_198)=k5_relat_1(E_200, F_198) | ~m1_subset_1(F_198, k1_zfmisc_1(k2_zfmisc_1(C_196, D_201))) | ~m1_subset_1(E_200, k1_zfmisc_1(k2_zfmisc_1(A_199, B_197))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.46/2.56  tff(c_2040, plain, (![A_206, B_207, E_208]: (k4_relset_1(A_206, B_207, '#skF_3', '#skF_2', E_208, '#skF_5')=k5_relat_1(E_208, '#skF_5') | ~m1_subset_1(E_208, k1_zfmisc_1(k2_zfmisc_1(A_206, B_207))))), inference(resolution, [status(thm)], [c_58, c_1787])).
% 7.46/2.56  tff(c_2064, plain, (k4_relset_1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_64, c_2040])).
% 7.46/2.56  tff(c_2155, plain, (![E_217, B_216, C_214, D_213, F_215, A_212]: (m1_subset_1(k4_relset_1(A_212, B_216, C_214, D_213, E_217, F_215), k1_zfmisc_1(k2_zfmisc_1(A_212, D_213))) | ~m1_subset_1(F_215, k1_zfmisc_1(k2_zfmisc_1(C_214, D_213))) | ~m1_subset_1(E_217, k1_zfmisc_1(k2_zfmisc_1(A_212, B_216))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.46/2.56  tff(c_2189, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2064, c_2155])).
% 7.46/2.56  tff(c_2206, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_58, c_2189])).
% 7.46/2.56  tff(c_2329, plain, (![C_221, A_224, B_225, D_222, F_223, E_226]: (k1_partfun1(A_224, B_225, C_221, D_222, E_226, F_223)=k5_relat_1(E_226, F_223) | ~m1_subset_1(F_223, k1_zfmisc_1(k2_zfmisc_1(C_221, D_222))) | ~v1_funct_1(F_223) | ~m1_subset_1(E_226, k1_zfmisc_1(k2_zfmisc_1(A_224, B_225))) | ~v1_funct_1(E_226))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.46/2.56  tff(c_2348, plain, (![A_224, B_225, E_226]: (k1_partfun1(A_224, B_225, '#skF_3', '#skF_2', E_226, '#skF_5')=k5_relat_1(E_226, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_226, k1_zfmisc_1(k2_zfmisc_1(A_224, B_225))) | ~v1_funct_1(E_226))), inference(resolution, [status(thm)], [c_58, c_2329])).
% 7.46/2.56  tff(c_4394, plain, (![A_294, B_295, E_296]: (k1_partfun1(A_294, B_295, '#skF_3', '#skF_2', E_296, '#skF_5')=k5_relat_1(E_296, '#skF_5') | ~m1_subset_1(E_296, k1_zfmisc_1(k2_zfmisc_1(A_294, B_295))) | ~v1_funct_1(E_296))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2348])).
% 7.46/2.56  tff(c_4434, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_4394])).
% 7.46/2.56  tff(c_4449, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_4434])).
% 7.46/2.56  tff(c_38, plain, (![A_40]: (m1_subset_1(k6_relat_1(A_40), k1_zfmisc_1(k2_zfmisc_1(A_40, A_40))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.46/2.56  tff(c_69, plain, (![A_40]: (m1_subset_1(k6_partfun1(A_40), k1_zfmisc_1(k2_zfmisc_1(A_40, A_40))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_38])).
% 7.46/2.56  tff(c_56, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.46/2.56  tff(c_1641, plain, (![D_180, C_181, A_182, B_183]: (D_180=C_181 | ~r2_relset_1(A_182, B_183, C_181, D_180) | ~m1_subset_1(D_180, k1_zfmisc_1(k2_zfmisc_1(A_182, B_183))) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_182, B_183))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.46/2.56  tff(c_1651, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_56, c_1641])).
% 7.46/2.56  tff(c_1670, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_1651])).
% 7.46/2.56  tff(c_1703, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1670])).
% 7.46/2.56  tff(c_5095, plain, (~m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4449, c_1703])).
% 7.46/2.56  tff(c_5099, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2206, c_5095])).
% 7.46/2.56  tff(c_5100, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_1670])).
% 7.46/2.56  tff(c_5962, plain, (![A_353, D_352, C_355, B_351, E_354]: (k1_xboole_0=C_355 | v2_funct_1(D_352) | ~v2_funct_1(k1_partfun1(A_353, B_351, B_351, C_355, D_352, E_354)) | ~m1_subset_1(E_354, k1_zfmisc_1(k2_zfmisc_1(B_351, C_355))) | ~v1_funct_2(E_354, B_351, C_355) | ~v1_funct_1(E_354) | ~m1_subset_1(D_352, k1_zfmisc_1(k2_zfmisc_1(A_353, B_351))) | ~v1_funct_2(D_352, A_353, B_351) | ~v1_funct_1(D_352))), inference(cnfTransformation, [status(thm)], [f_162])).
% 7.46/2.56  tff(c_5964, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5100, c_5962])).
% 7.46/2.56  tff(c_5966, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_62, c_60, c_58, c_70, c_5964])).
% 7.46/2.56  tff(c_5967, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_103, c_5966])).
% 7.46/2.56  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 7.46/2.56  tff(c_5994, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5967, c_2])).
% 7.46/2.56  tff(c_5996, plain, $false, inference(negUnitSimplification, [status(thm)], [c_254, c_5994])).
% 7.46/2.56  tff(c_5997, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_252])).
% 7.46/2.56  tff(c_105, plain, (![B_68, A_69]: (~v1_xboole_0(B_68) | B_68=A_69 | ~v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.46/2.56  tff(c_108, plain, (![A_69]: (k1_xboole_0=A_69 | ~v1_xboole_0(A_69))), inference(resolution, [status(thm)], [c_2, c_105])).
% 7.46/2.56  tff(c_6004, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_5997, c_108])).
% 7.46/2.56  tff(c_79, plain, (![A_66]: (k6_relat_1(A_66)=k6_partfun1(A_66))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.46/2.56  tff(c_16, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.46/2.56  tff(c_85, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_79, c_16])).
% 7.46/2.56  tff(c_98, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_85, c_70])).
% 7.46/2.56  tff(c_6018, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6004, c_98])).
% 7.46/2.56  tff(c_6024, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_6018])).
% 7.46/2.56  tff(c_6025, plain, (~v2_funct_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_54])).
% 7.46/2.56  tff(c_14, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.46/2.56  tff(c_6043, plain, (![B_362, A_363]: (v1_relat_1(B_362) | ~m1_subset_1(B_362, k1_zfmisc_1(A_363)) | ~v1_relat_1(A_363))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.46/2.56  tff(c_6058, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_6043])).
% 7.46/2.56  tff(c_6071, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_6058])).
% 7.46/2.56  tff(c_6120, plain, (![C_371, B_372, A_373]: (v5_relat_1(C_371, B_372) | ~m1_subset_1(C_371, k1_zfmisc_1(k2_zfmisc_1(A_373, B_372))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.46/2.56  tff(c_6141, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_6120])).
% 7.46/2.56  tff(c_6286, plain, (![A_388, B_389, C_390]: (k2_relset_1(A_388, B_389, C_390)=k2_relat_1(C_390) | ~m1_subset_1(C_390, k1_zfmisc_1(k2_zfmisc_1(A_388, B_389))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.46/2.56  tff(c_6307, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_6286])).
% 7.46/2.56  tff(c_7063, plain, (![A_446, B_447, C_448, D_449]: (k2_relset_1(A_446, B_447, C_448)=B_447 | ~r2_relset_1(B_447, B_447, k1_partfun1(B_447, A_446, A_446, B_447, D_449, C_448), k6_partfun1(B_447)) | ~m1_subset_1(D_449, k1_zfmisc_1(k2_zfmisc_1(B_447, A_446))) | ~v1_funct_2(D_449, B_447, A_446) | ~v1_funct_1(D_449) | ~m1_subset_1(C_448, k1_zfmisc_1(k2_zfmisc_1(A_446, B_447))) | ~v1_funct_2(C_448, A_446, B_447) | ~v1_funct_1(C_448))), inference(cnfTransformation, [status(thm)], [f_140])).
% 7.46/2.56  tff(c_7069, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_7063])).
% 7.46/2.56  tff(c_7075, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_68, c_66, c_64, c_6307, c_7069])).
% 7.46/2.56  tff(c_40, plain, (![B_42]: (v2_funct_2(B_42, k2_relat_1(B_42)) | ~v5_relat_1(B_42, k2_relat_1(B_42)) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.46/2.56  tff(c_7080, plain, (v2_funct_2('#skF_5', k2_relat_1('#skF_5')) | ~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7075, c_40])).
% 7.46/2.56  tff(c_7084, plain, (v2_funct_2('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6071, c_6141, c_7075, c_7080])).
% 7.46/2.56  tff(c_7086, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6025, c_7084])).
% 7.46/2.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.46/2.56  
% 7.46/2.56  Inference rules
% 7.46/2.56  ----------------------
% 7.46/2.56  #Ref     : 0
% 7.46/2.56  #Sup     : 1804
% 7.46/2.56  #Fact    : 0
% 7.46/2.56  #Define  : 0
% 7.46/2.56  #Split   : 29
% 7.46/2.56  #Chain   : 0
% 7.46/2.56  #Close   : 0
% 7.46/2.56  
% 7.46/2.56  Ordering : KBO
% 7.46/2.56  
% 7.46/2.56  Simplification rules
% 7.46/2.56  ----------------------
% 7.46/2.56  #Subsume      : 213
% 7.46/2.56  #Demod        : 1070
% 7.46/2.56  #Tautology    : 575
% 7.46/2.56  #SimpNegUnit  : 5
% 7.46/2.56  #BackRed      : 65
% 7.46/2.56  
% 7.46/2.56  #Partial instantiations: 0
% 7.46/2.56  #Strategies tried      : 1
% 7.46/2.56  
% 7.46/2.56  Timing (in seconds)
% 7.46/2.56  ----------------------
% 7.46/2.56  Preprocessing        : 0.39
% 7.46/2.56  Parsing              : 0.21
% 7.46/2.56  CNF conversion       : 0.03
% 7.46/2.56  Main loop            : 1.40
% 7.46/2.56  Inferencing          : 0.42
% 7.46/2.56  Reduction            : 0.51
% 7.46/2.56  Demodulation         : 0.37
% 7.46/2.56  BG Simplification    : 0.06
% 7.46/2.56  Subsumption          : 0.30
% 7.46/2.56  Abstraction          : 0.07
% 7.46/2.56  MUC search           : 0.00
% 7.46/2.56  Cooper               : 0.00
% 7.46/2.56  Total                : 1.83
% 7.46/2.56  Index Insertion      : 0.00
% 7.46/2.56  Index Deletion       : 0.00
% 7.46/2.56  Index Matching       : 0.00
% 7.46/2.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
