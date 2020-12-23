%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:13 EST 2020

% Result     : Theorem 7.59s
% Output     : CNFRefutation 7.59s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 253 expanded)
%              Number of leaves         :   45 ( 110 expanded)
%              Depth                    :    9
%              Number of atoms          :  199 ( 728 expanded)
%              Number of equality atoms :   32 (  72 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_157,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_98,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_96,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_76,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_137,axiom,(
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

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_48,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

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

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_115,axiom,(
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
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_50,plain,
    ( ~ v2_funct_2('#skF_5','#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_104,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( v1_xboole_0(k2_zfmisc_1(A_6,B_7))
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_219,plain,(
    ! [C_70,B_71,A_72] :
      ( ~ v1_xboole_0(C_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(C_70))
      | ~ r2_hidden(A_72,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_232,plain,(
    ! [A_72] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_72,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_219])).

tff(c_245,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_232])).

tff(c_249,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_245])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_56,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_42,plain,(
    ! [A_34] : k6_relat_1(A_34) = k6_partfun1(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_18,plain,(
    ! [A_11] : v2_funct_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_66,plain,(
    ! [A_11] : v2_funct_1(k6_partfun1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_18])).

tff(c_38,plain,(
    ! [C_30,E_32,D_31,B_29,F_33,A_28] :
      ( m1_subset_1(k1_partfun1(A_28,B_29,C_30,D_31,E_32,F_33),k1_zfmisc_1(k2_zfmisc_1(A_28,D_31)))
      | ~ m1_subset_1(F_33,k1_zfmisc_1(k2_zfmisc_1(C_30,D_31)))
      | ~ v1_funct_1(F_33)
      | ~ m1_subset_1(E_32,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ v1_funct_1(E_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_32,plain,(
    ! [A_25] : m1_subset_1(k6_relat_1(A_25),k1_zfmisc_1(k2_zfmisc_1(A_25,A_25))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_65,plain,(
    ! [A_25] : m1_subset_1(k6_partfun1(A_25),k1_zfmisc_1(k2_zfmisc_1(A_25,A_25))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_32])).

tff(c_52,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_2208,plain,(
    ! [D_195,C_196,A_197,B_198] :
      ( D_195 = C_196
      | ~ r2_relset_1(A_197,B_198,C_196,D_195)
      | ~ m1_subset_1(D_195,k1_zfmisc_1(k2_zfmisc_1(A_197,B_198)))
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(A_197,B_198))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2218,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_52,c_2208])).

tff(c_2237,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_2218])).

tff(c_2387,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2237])).

tff(c_3474,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_2387])).

tff(c_3478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_58,c_54,c_3474])).

tff(c_3479,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2237])).

tff(c_4720,plain,(
    ! [A_314,E_313,B_317,C_316,D_315] :
      ( k1_xboole_0 = C_316
      | v2_funct_1(D_315)
      | ~ v2_funct_1(k1_partfun1(A_314,B_317,B_317,C_316,D_315,E_313))
      | ~ m1_subset_1(E_313,k1_zfmisc_1(k2_zfmisc_1(B_317,C_316)))
      | ~ v1_funct_2(E_313,B_317,C_316)
      | ~ v1_funct_1(E_313)
      | ~ m1_subset_1(D_315,k1_zfmisc_1(k2_zfmisc_1(A_314,B_317)))
      | ~ v1_funct_2(D_315,A_314,B_317)
      | ~ v1_funct_1(D_315) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_4722,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3479,c_4720])).

tff(c_4724,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_58,c_56,c_54,c_66,c_4722])).

tff(c_4725,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_4724])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4766,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4725,c_6])).

tff(c_4768,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_4766])).

tff(c_4771,plain,(
    ! [A_318] : ~ r2_hidden(A_318,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_232])).

tff(c_4776,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_4771])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4783,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4776,c_8])).

tff(c_80,plain,(
    ! [A_50] : k6_relat_1(A_50) = k6_partfun1(A_50) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_14,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_86,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_14])).

tff(c_97,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_66])).

tff(c_4793,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4783,c_97])).

tff(c_4800,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_4793])).

tff(c_4801,plain,(
    ~ v2_funct_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_4844,plain,(
    ! [C_328,A_329,B_330] :
      ( v1_relat_1(C_328)
      | ~ m1_subset_1(C_328,k1_zfmisc_1(k2_zfmisc_1(A_329,B_330))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4859,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_4844])).

tff(c_4985,plain,(
    ! [C_348,B_349,A_350] :
      ( v5_relat_1(C_348,B_349)
      | ~ m1_subset_1(C_348,k1_zfmisc_1(k2_zfmisc_1(A_350,B_349))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_5003,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_4985])).

tff(c_5090,plain,(
    ! [A_357,B_358,D_359] :
      ( r2_relset_1(A_357,B_358,D_359,D_359)
      | ~ m1_subset_1(D_359,k1_zfmisc_1(k2_zfmisc_1(A_357,B_358))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_5101,plain,(
    ! [A_25] : r2_relset_1(A_25,A_25,k6_partfun1(A_25),k6_partfun1(A_25)) ),
    inference(resolution,[status(thm)],[c_65,c_5090])).

tff(c_5162,plain,(
    ! [A_364,B_365,C_366] :
      ( k2_relset_1(A_364,B_365,C_366) = k2_relat_1(C_366)
      | ~ m1_subset_1(C_366,k1_zfmisc_1(k2_zfmisc_1(A_364,B_365))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_5180,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_5162])).

tff(c_5264,plain,(
    ! [D_373,C_374,A_375,B_376] :
      ( D_373 = C_374
      | ~ r2_relset_1(A_375,B_376,C_374,D_373)
      | ~ m1_subset_1(D_373,k1_zfmisc_1(k2_zfmisc_1(A_375,B_376)))
      | ~ m1_subset_1(C_374,k1_zfmisc_1(k2_zfmisc_1(A_375,B_376))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_5274,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_52,c_5264])).

tff(c_5293,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_5274])).

tff(c_5408,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_5293])).

tff(c_6526,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_5408])).

tff(c_6530,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_58,c_54,c_6526])).

tff(c_6531,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_5293])).

tff(c_8448,plain,(
    ! [A_510,B_511,C_512,D_513] :
      ( k2_relset_1(A_510,B_511,C_512) = B_511
      | ~ r2_relset_1(B_511,B_511,k1_partfun1(B_511,A_510,A_510,B_511,D_513,C_512),k6_partfun1(B_511))
      | ~ m1_subset_1(D_513,k1_zfmisc_1(k2_zfmisc_1(B_511,A_510)))
      | ~ v1_funct_2(D_513,B_511,A_510)
      | ~ v1_funct_1(D_513)
      | ~ m1_subset_1(C_512,k1_zfmisc_1(k2_zfmisc_1(A_510,B_511)))
      | ~ v1_funct_2(C_512,A_510,B_511)
      | ~ v1_funct_1(C_512) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_8454,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6531,c_8448])).

tff(c_8474,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_64,c_62,c_60,c_5101,c_5180,c_8454])).

tff(c_34,plain,(
    ! [B_27] :
      ( v2_funct_2(B_27,k2_relat_1(B_27))
      | ~ v5_relat_1(B_27,k2_relat_1(B_27))
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_8480,plain,
    ( v2_funct_2('#skF_5',k2_relat_1('#skF_5'))
    | ~ v5_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_8474,c_34])).

tff(c_8484,plain,(
    v2_funct_2('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4859,c_5003,c_8474,c_8480])).

tff(c_8486,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4801,c_8484])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:02:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.59/2.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.59/2.75  
% 7.59/2.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.59/2.75  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 7.59/2.75  
% 7.59/2.75  %Foreground sorts:
% 7.59/2.75  
% 7.59/2.75  
% 7.59/2.75  %Background operators:
% 7.59/2.75  
% 7.59/2.75  
% 7.59/2.75  %Foreground operators:
% 7.59/2.75  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.59/2.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.59/2.75  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.59/2.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.59/2.75  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.59/2.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.59/2.75  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.59/2.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.59/2.75  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.59/2.75  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.59/2.75  tff('#skF_5', type, '#skF_5': $i).
% 7.59/2.75  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.59/2.75  tff('#skF_2', type, '#skF_2': $i).
% 7.59/2.75  tff('#skF_3', type, '#skF_3': $i).
% 7.59/2.75  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 7.59/2.75  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.59/2.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.59/2.75  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.59/2.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.59/2.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.59/2.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.59/2.75  tff('#skF_4', type, '#skF_4': $i).
% 7.59/2.75  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.59/2.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.59/2.75  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.59/2.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.59/2.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.59/2.75  
% 7.59/2.77  tff(f_157, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 7.59/2.77  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.59/2.77  tff(f_40, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 7.59/2.77  tff(f_47, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 7.59/2.77  tff(f_98, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.59/2.77  tff(f_52, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 7.59/2.77  tff(f_96, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.59/2.77  tff(f_76, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 7.59/2.77  tff(f_74, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.59/2.77  tff(f_137, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 7.59/2.77  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.59/2.77  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 7.59/2.77  tff(f_48, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 7.59/2.77  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.59/2.77  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.59/2.77  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.59/2.77  tff(f_115, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 7.59/2.77  tff(f_84, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 7.59/2.77  tff(c_50, plain, (~v2_funct_2('#skF_5', '#skF_2') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_157])).
% 7.59/2.77  tff(c_104, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_50])).
% 7.59/2.77  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.59/2.77  tff(c_10, plain, (![A_6, B_7]: (v1_xboole_0(k2_zfmisc_1(A_6, B_7)) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.59/2.77  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_157])).
% 7.59/2.77  tff(c_219, plain, (![C_70, B_71, A_72]: (~v1_xboole_0(C_70) | ~m1_subset_1(B_71, k1_zfmisc_1(C_70)) | ~r2_hidden(A_72, B_71))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.59/2.77  tff(c_232, plain, (![A_72]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_72, '#skF_4'))), inference(resolution, [status(thm)], [c_60, c_219])).
% 7.59/2.77  tff(c_245, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_232])).
% 7.59/2.77  tff(c_249, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_10, c_245])).
% 7.59/2.77  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_157])).
% 7.59/2.77  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 7.59/2.77  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_157])).
% 7.59/2.77  tff(c_56, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 7.59/2.77  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_157])).
% 7.59/2.77  tff(c_42, plain, (![A_34]: (k6_relat_1(A_34)=k6_partfun1(A_34))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.59/2.77  tff(c_18, plain, (![A_11]: (v2_funct_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.59/2.77  tff(c_66, plain, (![A_11]: (v2_funct_1(k6_partfun1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_18])).
% 7.59/2.77  tff(c_38, plain, (![C_30, E_32, D_31, B_29, F_33, A_28]: (m1_subset_1(k1_partfun1(A_28, B_29, C_30, D_31, E_32, F_33), k1_zfmisc_1(k2_zfmisc_1(A_28, D_31))) | ~m1_subset_1(F_33, k1_zfmisc_1(k2_zfmisc_1(C_30, D_31))) | ~v1_funct_1(F_33) | ~m1_subset_1(E_32, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~v1_funct_1(E_32))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.59/2.77  tff(c_32, plain, (![A_25]: (m1_subset_1(k6_relat_1(A_25), k1_zfmisc_1(k2_zfmisc_1(A_25, A_25))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.59/2.77  tff(c_65, plain, (![A_25]: (m1_subset_1(k6_partfun1(A_25), k1_zfmisc_1(k2_zfmisc_1(A_25, A_25))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_32])).
% 7.59/2.77  tff(c_52, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 7.59/2.77  tff(c_2208, plain, (![D_195, C_196, A_197, B_198]: (D_195=C_196 | ~r2_relset_1(A_197, B_198, C_196, D_195) | ~m1_subset_1(D_195, k1_zfmisc_1(k2_zfmisc_1(A_197, B_198))) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(A_197, B_198))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.59/2.77  tff(c_2218, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_52, c_2208])).
% 7.59/2.77  tff(c_2237, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_2218])).
% 7.59/2.77  tff(c_2387, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_2237])).
% 7.59/2.77  tff(c_3474, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_2387])).
% 7.59/2.77  tff(c_3478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_58, c_54, c_3474])).
% 7.59/2.77  tff(c_3479, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_2237])).
% 7.59/2.77  tff(c_4720, plain, (![A_314, E_313, B_317, C_316, D_315]: (k1_xboole_0=C_316 | v2_funct_1(D_315) | ~v2_funct_1(k1_partfun1(A_314, B_317, B_317, C_316, D_315, E_313)) | ~m1_subset_1(E_313, k1_zfmisc_1(k2_zfmisc_1(B_317, C_316))) | ~v1_funct_2(E_313, B_317, C_316) | ~v1_funct_1(E_313) | ~m1_subset_1(D_315, k1_zfmisc_1(k2_zfmisc_1(A_314, B_317))) | ~v1_funct_2(D_315, A_314, B_317) | ~v1_funct_1(D_315))), inference(cnfTransformation, [status(thm)], [f_137])).
% 7.59/2.77  tff(c_4722, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3479, c_4720])).
% 7.59/2.77  tff(c_4724, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_58, c_56, c_54, c_66, c_4722])).
% 7.59/2.77  tff(c_4725, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_104, c_4724])).
% 7.59/2.77  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.59/2.77  tff(c_4766, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4725, c_6])).
% 7.59/2.77  tff(c_4768, plain, $false, inference(negUnitSimplification, [status(thm)], [c_249, c_4766])).
% 7.59/2.77  tff(c_4771, plain, (![A_318]: (~r2_hidden(A_318, '#skF_4'))), inference(splitRight, [status(thm)], [c_232])).
% 7.59/2.77  tff(c_4776, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_4771])).
% 7.59/2.77  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.59/2.77  tff(c_4783, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_4776, c_8])).
% 7.59/2.77  tff(c_80, plain, (![A_50]: (k6_relat_1(A_50)=k6_partfun1(A_50))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.59/2.77  tff(c_14, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.59/2.77  tff(c_86, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_80, c_14])).
% 7.59/2.77  tff(c_97, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_86, c_66])).
% 7.59/2.77  tff(c_4793, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4783, c_97])).
% 7.59/2.77  tff(c_4800, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_4793])).
% 7.59/2.77  tff(c_4801, plain, (~v2_funct_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 7.59/2.77  tff(c_4844, plain, (![C_328, A_329, B_330]: (v1_relat_1(C_328) | ~m1_subset_1(C_328, k1_zfmisc_1(k2_zfmisc_1(A_329, B_330))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.59/2.77  tff(c_4859, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_4844])).
% 7.59/2.77  tff(c_4985, plain, (![C_348, B_349, A_350]: (v5_relat_1(C_348, B_349) | ~m1_subset_1(C_348, k1_zfmisc_1(k2_zfmisc_1(A_350, B_349))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.59/2.77  tff(c_5003, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_54, c_4985])).
% 7.59/2.77  tff(c_5090, plain, (![A_357, B_358, D_359]: (r2_relset_1(A_357, B_358, D_359, D_359) | ~m1_subset_1(D_359, k1_zfmisc_1(k2_zfmisc_1(A_357, B_358))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.59/2.77  tff(c_5101, plain, (![A_25]: (r2_relset_1(A_25, A_25, k6_partfun1(A_25), k6_partfun1(A_25)))), inference(resolution, [status(thm)], [c_65, c_5090])).
% 7.59/2.77  tff(c_5162, plain, (![A_364, B_365, C_366]: (k2_relset_1(A_364, B_365, C_366)=k2_relat_1(C_366) | ~m1_subset_1(C_366, k1_zfmisc_1(k2_zfmisc_1(A_364, B_365))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.59/2.77  tff(c_5180, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_5162])).
% 7.59/2.77  tff(c_5264, plain, (![D_373, C_374, A_375, B_376]: (D_373=C_374 | ~r2_relset_1(A_375, B_376, C_374, D_373) | ~m1_subset_1(D_373, k1_zfmisc_1(k2_zfmisc_1(A_375, B_376))) | ~m1_subset_1(C_374, k1_zfmisc_1(k2_zfmisc_1(A_375, B_376))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.59/2.77  tff(c_5274, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_52, c_5264])).
% 7.59/2.77  tff(c_5293, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_5274])).
% 7.59/2.77  tff(c_5408, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_5293])).
% 7.59/2.77  tff(c_6526, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_5408])).
% 7.59/2.77  tff(c_6530, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_58, c_54, c_6526])).
% 7.59/2.77  tff(c_6531, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_5293])).
% 7.59/2.77  tff(c_8448, plain, (![A_510, B_511, C_512, D_513]: (k2_relset_1(A_510, B_511, C_512)=B_511 | ~r2_relset_1(B_511, B_511, k1_partfun1(B_511, A_510, A_510, B_511, D_513, C_512), k6_partfun1(B_511)) | ~m1_subset_1(D_513, k1_zfmisc_1(k2_zfmisc_1(B_511, A_510))) | ~v1_funct_2(D_513, B_511, A_510) | ~v1_funct_1(D_513) | ~m1_subset_1(C_512, k1_zfmisc_1(k2_zfmisc_1(A_510, B_511))) | ~v1_funct_2(C_512, A_510, B_511) | ~v1_funct_1(C_512))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.59/2.77  tff(c_8454, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6531, c_8448])).
% 7.59/2.77  tff(c_8474, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_64, c_62, c_60, c_5101, c_5180, c_8454])).
% 7.59/2.77  tff(c_34, plain, (![B_27]: (v2_funct_2(B_27, k2_relat_1(B_27)) | ~v5_relat_1(B_27, k2_relat_1(B_27)) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.59/2.77  tff(c_8480, plain, (v2_funct_2('#skF_5', k2_relat_1('#skF_5')) | ~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_8474, c_34])).
% 7.59/2.77  tff(c_8484, plain, (v2_funct_2('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4859, c_5003, c_8474, c_8480])).
% 7.59/2.77  tff(c_8486, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4801, c_8484])).
% 7.59/2.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.59/2.77  
% 7.59/2.77  Inference rules
% 7.59/2.77  ----------------------
% 7.59/2.77  #Ref     : 0
% 7.59/2.77  #Sup     : 2083
% 7.59/2.77  #Fact    : 0
% 7.59/2.77  #Define  : 0
% 7.59/2.77  #Split   : 14
% 7.59/2.77  #Chain   : 0
% 7.59/2.77  #Close   : 0
% 7.59/2.77  
% 7.59/2.77  Ordering : KBO
% 7.59/2.77  
% 7.59/2.77  Simplification rules
% 7.59/2.77  ----------------------
% 7.59/2.77  #Subsume      : 230
% 7.59/2.77  #Demod        : 2251
% 7.59/2.77  #Tautology    : 1257
% 7.59/2.77  #SimpNegUnit  : 5
% 7.59/2.77  #BackRed      : 60
% 7.59/2.77  
% 7.59/2.77  #Partial instantiations: 0
% 7.59/2.77  #Strategies tried      : 1
% 7.59/2.77  
% 7.59/2.77  Timing (in seconds)
% 7.59/2.77  ----------------------
% 7.59/2.78  Preprocessing        : 0.42
% 7.59/2.78  Parsing              : 0.24
% 7.59/2.78  CNF conversion       : 0.03
% 7.59/2.78  Main loop            : 1.47
% 7.59/2.78  Inferencing          : 0.45
% 7.59/2.78  Reduction            : 0.56
% 7.59/2.78  Demodulation         : 0.41
% 7.59/2.78  BG Simplification    : 0.05
% 7.59/2.78  Subsumption          : 0.30
% 7.59/2.78  Abstraction          : 0.06
% 7.59/2.78  MUC search           : 0.00
% 7.59/2.78  Cooper               : 0.00
% 7.59/2.78  Total                : 1.94
% 7.59/2.78  Index Insertion      : 0.00
% 7.59/2.78  Index Deletion       : 0.00
% 7.59/2.78  Index Matching       : 0.00
% 7.59/2.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
