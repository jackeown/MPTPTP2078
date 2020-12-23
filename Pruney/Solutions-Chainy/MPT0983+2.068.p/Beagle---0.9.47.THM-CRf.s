%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:10 EST 2020

% Result     : Theorem 7.68s
% Output     : CNFRefutation 7.86s
% Verified   : 
% Statistics : Number of formulae       :  199 (1501 expanded)
%              Number of leaves         :   46 ( 521 expanded)
%              Depth                    :   18
%              Number of atoms          :  399 (3953 expanded)
%              Number of equality atoms :  113 (1182 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_119,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_178,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_117,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_107,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_87,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_59,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_158,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_136,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_47,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_54,plain,(
    ! [A_39] : k6_relat_1(A_39) = k6_partfun1(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_28,plain,(
    ! [A_10] : v2_funct_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_78,plain,(
    ! [A_10] : v2_funct_1(k6_partfun1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_28])).

tff(c_76,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_1834,plain,(
    ! [B_252,C_249,F_250,D_251,E_248,A_247] :
      ( k1_partfun1(A_247,B_252,C_249,D_251,E_248,F_250) = k5_relat_1(E_248,F_250)
      | ~ m1_subset_1(F_250,k1_zfmisc_1(k2_zfmisc_1(C_249,D_251)))
      | ~ v1_funct_1(F_250)
      | ~ m1_subset_1(E_248,k1_zfmisc_1(k2_zfmisc_1(A_247,B_252)))
      | ~ v1_funct_1(E_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1840,plain,(
    ! [A_247,B_252,E_248] :
      ( k1_partfun1(A_247,B_252,'#skF_2','#skF_1',E_248,'#skF_4') = k5_relat_1(E_248,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_248,k1_zfmisc_1(k2_zfmisc_1(A_247,B_252)))
      | ~ v1_funct_1(E_248) ) ),
    inference(resolution,[status(thm)],[c_66,c_1834])).

tff(c_2250,plain,(
    ! [A_285,B_286,E_287] :
      ( k1_partfun1(A_285,B_286,'#skF_2','#skF_1',E_287,'#skF_4') = k5_relat_1(E_287,'#skF_4')
      | ~ m1_subset_1(E_287,k1_zfmisc_1(k2_zfmisc_1(A_285,B_286)))
      | ~ v1_funct_1(E_287) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1840])).

tff(c_2271,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_2250])).

tff(c_2286,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2271])).

tff(c_48,plain,(
    ! [C_29,D_30,B_28,F_32,A_27,E_31] :
      ( m1_subset_1(k1_partfun1(A_27,B_28,C_29,D_30,E_31,F_32),k1_zfmisc_1(k2_zfmisc_1(A_27,D_30)))
      | ~ m1_subset_1(F_32,k1_zfmisc_1(k2_zfmisc_1(C_29,D_30)))
      | ~ v1_funct_1(F_32)
      | ~ m1_subset_1(E_31,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ v1_funct_1(E_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2423,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2286,c_48])).

tff(c_2432,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_70,c_66,c_2423])).

tff(c_42,plain,(
    ! [A_24] : m1_subset_1(k6_relat_1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_77,plain,(
    ! [A_24] : m1_subset_1(k6_partfun1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_42])).

tff(c_64,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_1572,plain,(
    ! [D_217,C_218,A_219,B_220] :
      ( D_217 = C_218
      | ~ r2_relset_1(A_219,B_220,C_218,D_217)
      | ~ m1_subset_1(D_217,k1_zfmisc_1(k2_zfmisc_1(A_219,B_220)))
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(A_219,B_220))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1584,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_64,c_1572])).

tff(c_1604,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_1584])).

tff(c_2541,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2432,c_2286,c_2286,c_1604])).

tff(c_62,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_121,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_24,plain,(
    ! [A_9] : k2_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_80,plain,(
    ! [A_9] : k2_relat_1(k6_partfun1(A_9)) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_24])).

tff(c_26,plain,(
    ! [A_10] : v1_relat_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_79,plain,(
    ! [A_10] : v1_relat_1(k6_partfun1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_26])).

tff(c_122,plain,(
    ! [A_58] :
      ( k2_relat_1(A_58) != k1_xboole_0
      | k1_xboole_0 = A_58
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_125,plain,(
    ! [A_10] :
      ( k2_relat_1(k6_partfun1(A_10)) != k1_xboole_0
      | k6_partfun1(A_10) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_79,c_122])).

tff(c_127,plain,(
    ! [A_10] :
      ( k1_xboole_0 != A_10
      | k6_partfun1(A_10) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_125])).

tff(c_214,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_xboole_0)
    | k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_64])).

tff(c_250,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_214])).

tff(c_74,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_68,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_60,plain,(
    ! [E_50,D_48,C_47,A_45,B_46] :
      ( k1_xboole_0 = C_47
      | v2_funct_1(D_48)
      | ~ v2_funct_1(k1_partfun1(A_45,B_46,B_46,C_47,D_48,E_50))
      | ~ m1_subset_1(E_50,k1_zfmisc_1(k2_zfmisc_1(B_46,C_47)))
      | ~ v1_funct_2(E_50,B_46,C_47)
      | ~ v1_funct_1(E_50)
      | ~ m1_subset_1(D_48,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46)))
      | ~ v1_funct_2(D_48,A_45,B_46)
      | ~ v1_funct_1(D_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_2420,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2286,c_60])).

tff(c_2429,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_68,c_66,c_2420])).

tff(c_2430,plain,(
    ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_250,c_2429])).

tff(c_2547,plain,(
    ~ v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2541,c_2430])).

tff(c_2557,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2547])).

tff(c_2559,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_198,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_210,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_198])).

tff(c_18,plain,(
    ! [A_8] :
      ( k2_relat_1(A_8) != k1_xboole_0
      | k1_xboole_0 = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_222,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_210,c_18])).

tff(c_232,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_222])).

tff(c_2561,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2559,c_232])).

tff(c_3207,plain,(
    ! [D_376,A_372,B_377,E_373,C_374,F_375] :
      ( k1_partfun1(A_372,B_377,C_374,D_376,E_373,F_375) = k5_relat_1(E_373,F_375)
      | ~ m1_subset_1(F_375,k1_zfmisc_1(k2_zfmisc_1(C_374,D_376)))
      | ~ v1_funct_1(F_375)
      | ~ m1_subset_1(E_373,k1_zfmisc_1(k2_zfmisc_1(A_372,B_377)))
      | ~ v1_funct_1(E_373) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_3213,plain,(
    ! [A_372,B_377,E_373] :
      ( k1_partfun1(A_372,B_377,'#skF_2','#skF_1',E_373,'#skF_4') = k5_relat_1(E_373,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_373,k1_zfmisc_1(k2_zfmisc_1(A_372,B_377)))
      | ~ v1_funct_1(E_373) ) ),
    inference(resolution,[status(thm)],[c_66,c_3207])).

tff(c_3500,plain,(
    ! [A_402,B_403,E_404] :
      ( k1_partfun1(A_402,B_403,'#skF_2','#skF_1',E_404,'#skF_4') = k5_relat_1(E_404,'#skF_4')
      | ~ m1_subset_1(E_404,k1_zfmisc_1(k2_zfmisc_1(A_402,B_403)))
      | ~ v1_funct_1(E_404) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_3213])).

tff(c_3515,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_3500])).

tff(c_3524,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_3515])).

tff(c_2607,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2559,c_2559,c_127])).

tff(c_2608,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2607,c_64])).

tff(c_3605,plain,(
    r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3524,c_2608])).

tff(c_2939,plain,(
    ! [A_338,B_339,C_340] :
      ( k2_relset_1(A_338,B_339,C_340) = k2_relat_1(C_340)
      | ~ m1_subset_1(C_340,k1_zfmisc_1(k2_zfmisc_1(A_338,B_339))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2956,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_2939])).

tff(c_3746,plain,(
    ! [A_417,B_418,C_419,D_420] :
      ( k2_relset_1(A_417,B_418,C_419) = B_418
      | ~ r2_relset_1(B_418,B_418,k1_partfun1(B_418,A_417,A_417,B_418,D_420,C_419),k6_partfun1(B_418))
      | ~ m1_subset_1(D_420,k1_zfmisc_1(k2_zfmisc_1(B_418,A_417)))
      | ~ v1_funct_2(D_420,B_418,A_417)
      | ~ v1_funct_1(D_420)
      | ~ m1_subset_1(C_419,k1_zfmisc_1(k2_zfmisc_1(A_417,B_418)))
      | ~ v1_funct_2(C_419,A_417,B_418)
      | ~ v1_funct_1(C_419) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_3749,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_4'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3524,c_3746])).

tff(c_3754,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_76,c_74,c_72,c_3605,c_2607,c_2956,c_3749])).

tff(c_3756,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2561,c_3754])).

tff(c_3757,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_16,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3765,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3757,c_3757,c_16])).

tff(c_20,plain,(
    ! [A_8] :
      ( k1_relat_1(A_8) != k1_xboole_0
      | k1_xboole_0 = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_221,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_210,c_20])).

tff(c_231,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_3759,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3757,c_231])).

tff(c_3785,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3765,c_3759])).

tff(c_3786,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_129,plain,(
    ! [A_59] :
      ( k1_xboole_0 != A_59
      | k6_partfun1(A_59) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_125])).

tff(c_142,plain,(
    ! [A_59] :
      ( v2_funct_1(k1_xboole_0)
      | k1_xboole_0 != A_59 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_78])).

tff(c_167,plain,(
    ! [A_59] : k1_xboole_0 != A_59 ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_16])).

tff(c_173,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_3789,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3786,c_173])).

tff(c_211,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_198])).

tff(c_229,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_211,c_20])).

tff(c_4967,plain,
    ( k1_relat_1('#skF_3') != '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3786,c_3786,c_229])).

tff(c_4968,plain,(
    k1_relat_1('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_4967])).

tff(c_3824,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_4')
    | '#skF_1' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3786,c_3786,c_214])).

tff(c_3825,plain,(
    '#skF_1' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3824])).

tff(c_14,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3794,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3786,c_3786,c_14])).

tff(c_4133,plain,(
    ! [A_459,B_460,C_461] :
      ( k2_relset_1(A_459,B_460,C_461) = k2_relat_1(C_461)
      | ~ m1_subset_1(C_461,k1_zfmisc_1(k2_zfmisc_1(A_459,B_460))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4142,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_4133])).

tff(c_4151,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3794,c_4142])).

tff(c_4938,plain,(
    ! [A_541,B_542,C_543,D_544] :
      ( k2_relset_1(A_541,B_542,C_543) = B_542
      | ~ r2_relset_1(B_542,B_542,k1_partfun1(B_542,A_541,A_541,B_542,D_544,C_543),k6_partfun1(B_542))
      | ~ m1_subset_1(D_544,k1_zfmisc_1(k2_zfmisc_1(B_542,A_541)))
      | ~ v1_funct_2(D_544,B_542,A_541)
      | ~ v1_funct_1(D_544)
      | ~ m1_subset_1(C_543,k1_zfmisc_1(k2_zfmisc_1(A_541,B_542)))
      | ~ v1_funct_2(C_543,A_541,B_542)
      | ~ v1_funct_1(C_543) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_4947,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_4938])).

tff(c_4952,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_76,c_74,c_72,c_4151,c_4947])).

tff(c_4954,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3825,c_4952])).

tff(c_4956,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3824])).

tff(c_4959,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4956,c_72])).

tff(c_5129,plain,(
    ! [C_564,A_565,B_566] :
      ( v4_relat_1(C_564,A_565)
      | ~ m1_subset_1(C_564,k1_zfmisc_1(k2_zfmisc_1(A_565,B_566))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_5139,plain,(
    v4_relat_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_4959,c_5129])).

tff(c_3793,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3786,c_3786,c_16])).

tff(c_4958,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4956,c_66])).

tff(c_5979,plain,(
    ! [C_652,A_656,F_651,E_654,B_655,D_653] :
      ( m1_subset_1(k1_partfun1(A_656,B_655,C_652,D_653,E_654,F_651),k1_zfmisc_1(k2_zfmisc_1(A_656,D_653)))
      | ~ m1_subset_1(F_651,k1_zfmisc_1(k2_zfmisc_1(C_652,D_653)))
      | ~ v1_funct_1(F_651)
      | ~ m1_subset_1(E_654,k1_zfmisc_1(k2_zfmisc_1(A_656,B_655)))
      | ~ v1_funct_1(E_654) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_187,plain,(
    ! [A_61] : m1_subset_1(k6_partfun1(A_61),k1_zfmisc_1(k2_zfmisc_1(A_61,A_61))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_42])).

tff(c_190,plain,(
    ! [A_10] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_10,A_10)))
      | k1_xboole_0 != A_10 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_187])).

tff(c_5170,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3786,c_3786,c_190])).

tff(c_3851,plain,(
    k6_partfun1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3786,c_3786,c_127])).

tff(c_4957,plain,(
    r2_relset_1('#skF_4','#skF_4',k1_partfun1('#skF_4','#skF_2','#skF_2','#skF_4','#skF_3','#skF_4'),k6_partfun1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4956,c_4956,c_4956,c_4956,c_4956,c_64])).

tff(c_5079,plain,(
    r2_relset_1('#skF_4','#skF_4',k1_partfun1('#skF_4','#skF_2','#skF_2','#skF_4','#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3851,c_4957])).

tff(c_5467,plain,(
    ! [D_599,C_600,A_601,B_602] :
      ( D_599 = C_600
      | ~ r2_relset_1(A_601,B_602,C_600,D_599)
      | ~ m1_subset_1(D_599,k1_zfmisc_1(k2_zfmisc_1(A_601,B_602)))
      | ~ m1_subset_1(C_600,k1_zfmisc_1(k2_zfmisc_1(A_601,B_602))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_5481,plain,
    ( k1_partfun1('#skF_4','#skF_2','#skF_2','#skF_4','#skF_3','#skF_4') = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
    | ~ m1_subset_1(k1_partfun1('#skF_4','#skF_2','#skF_2','#skF_4','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_5079,c_5467])).

tff(c_5504,plain,
    ( k1_partfun1('#skF_4','#skF_2','#skF_2','#skF_4','#skF_3','#skF_4') = '#skF_4'
    | ~ m1_subset_1(k1_partfun1('#skF_4','#skF_2','#skF_2','#skF_4','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5170,c_5481])).

tff(c_5568,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_4','#skF_2','#skF_2','#skF_4','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_5504])).

tff(c_5985,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5979,c_5568])).

tff(c_6011,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_4959,c_70,c_4958,c_5985])).

tff(c_6012,plain,(
    k1_partfun1('#skF_4','#skF_2','#skF_2','#skF_4','#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5504])).

tff(c_6381,plain,(
    ! [E_691,A_690,C_692,D_694,B_695,F_693] :
      ( k1_partfun1(A_690,B_695,C_692,D_694,E_691,F_693) = k5_relat_1(E_691,F_693)
      | ~ m1_subset_1(F_693,k1_zfmisc_1(k2_zfmisc_1(C_692,D_694)))
      | ~ v1_funct_1(F_693)
      | ~ m1_subset_1(E_691,k1_zfmisc_1(k2_zfmisc_1(A_690,B_695)))
      | ~ v1_funct_1(E_691) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_6387,plain,(
    ! [A_690,B_695,E_691] :
      ( k1_partfun1(A_690,B_695,'#skF_2','#skF_4',E_691,'#skF_4') = k5_relat_1(E_691,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_691,k1_zfmisc_1(k2_zfmisc_1(A_690,B_695)))
      | ~ v1_funct_1(E_691) ) ),
    inference(resolution,[status(thm)],[c_4958,c_6381])).

tff(c_6505,plain,(
    ! [A_715,B_716,E_717] :
      ( k1_partfun1(A_715,B_716,'#skF_2','#skF_4',E_717,'#skF_4') = k5_relat_1(E_717,'#skF_4')
      | ~ m1_subset_1(E_717,k1_zfmisc_1(k2_zfmisc_1(A_715,B_716)))
      | ~ v1_funct_1(E_717) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_6387])).

tff(c_6514,plain,
    ( k1_partfun1('#skF_4','#skF_2','#skF_2','#skF_4','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4959,c_6505])).

tff(c_6527,plain,(
    k5_relat_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_6012,c_6514])).

tff(c_12,plain,(
    ! [A_5,B_7] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_5,B_7)),k1_relat_1(A_5))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6537,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6527,c_12])).

tff(c_6543,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_210,c_3793,c_6537])).

tff(c_4973,plain,(
    ! [B_545,A_546] :
      ( r1_tarski(k1_relat_1(B_545),A_546)
      | ~ v4_relat_1(B_545,A_546)
      | ~ v1_relat_1(B_545) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4986,plain,(
    ! [B_545,A_546] :
      ( k1_relat_1(B_545) = A_546
      | ~ r1_tarski(A_546,k1_relat_1(B_545))
      | ~ v4_relat_1(B_545,A_546)
      | ~ v1_relat_1(B_545) ) ),
    inference(resolution,[status(thm)],[c_4973,c_2])).

tff(c_6567,plain,
    ( k1_relat_1('#skF_3') = '#skF_4'
    | ~ v4_relat_1('#skF_3','#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6543,c_4986])).

tff(c_6580,plain,(
    k1_relat_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_5139,c_6567])).

tff(c_6582,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4968,c_6580])).

tff(c_6583,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4967])).

tff(c_6587,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6583,c_121])).

tff(c_6592,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3789,c_6587])).

tff(c_6593,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_6686,plain,(
    ! [C_725,A_726,B_727] :
      ( v1_relat_1(C_725)
      | ~ m1_subset_1(C_725,k1_zfmisc_1(k2_zfmisc_1(A_726,B_727))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6699,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_6686])).

tff(c_6734,plain,(
    ! [C_730,B_731,A_732] :
      ( v5_relat_1(C_730,B_731)
      | ~ m1_subset_1(C_730,k1_zfmisc_1(k2_zfmisc_1(A_732,B_731))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6746,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_6734])).

tff(c_6974,plain,(
    ! [A_763,B_764,D_765] :
      ( r2_relset_1(A_763,B_764,D_765,D_765)
      | ~ m1_subset_1(D_765,k1_zfmisc_1(k2_zfmisc_1(A_763,B_764))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_6984,plain,(
    ! [A_24] : r2_relset_1(A_24,A_24,k6_partfun1(A_24),k6_partfun1(A_24)) ),
    inference(resolution,[status(thm)],[c_77,c_6974])).

tff(c_7001,plain,(
    ! [A_767,B_768,C_769] :
      ( k2_relset_1(A_767,B_768,C_769) = k2_relat_1(C_769)
      | ~ m1_subset_1(C_769,k1_zfmisc_1(k2_zfmisc_1(A_767,B_768))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_7019,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_7001])).

tff(c_7534,plain,(
    ! [E_829,A_831,B_830,F_826,C_827,D_828] :
      ( m1_subset_1(k1_partfun1(A_831,B_830,C_827,D_828,E_829,F_826),k1_zfmisc_1(k2_zfmisc_1(A_831,D_828)))
      | ~ m1_subset_1(F_826,k1_zfmisc_1(k2_zfmisc_1(C_827,D_828)))
      | ~ v1_funct_1(F_826)
      | ~ m1_subset_1(E_829,k1_zfmisc_1(k2_zfmisc_1(A_831,B_830)))
      | ~ v1_funct_1(E_829) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_7057,plain,(
    ! [D_773,C_774,A_775,B_776] :
      ( D_773 = C_774
      | ~ r2_relset_1(A_775,B_776,C_774,D_773)
      | ~ m1_subset_1(D_773,k1_zfmisc_1(k2_zfmisc_1(A_775,B_776)))
      | ~ m1_subset_1(C_774,k1_zfmisc_1(k2_zfmisc_1(A_775,B_776))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_7065,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_64,c_7057])).

tff(c_7080,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_7065])).

tff(c_7116,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_7080])).

tff(c_7537,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_7534,c_7116])).

tff(c_7565,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_70,c_66,c_7537])).

tff(c_7566,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_7080])).

tff(c_8335,plain,(
    ! [A_903,B_904,C_905,D_906] :
      ( k2_relset_1(A_903,B_904,C_905) = B_904
      | ~ r2_relset_1(B_904,B_904,k1_partfun1(B_904,A_903,A_903,B_904,D_906,C_905),k6_partfun1(B_904))
      | ~ m1_subset_1(D_906,k1_zfmisc_1(k2_zfmisc_1(B_904,A_903)))
      | ~ v1_funct_2(D_906,B_904,A_903)
      | ~ v1_funct_1(D_906)
      | ~ m1_subset_1(C_905,k1_zfmisc_1(k2_zfmisc_1(A_903,B_904)))
      | ~ v1_funct_2(C_905,A_903,B_904)
      | ~ v1_funct_1(C_905) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_8341,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7566,c_8335])).

tff(c_8348,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_76,c_74,c_72,c_6984,c_7019,c_8341])).

tff(c_44,plain,(
    ! [B_26] :
      ( v2_funct_2(B_26,k2_relat_1(B_26))
      | ~ v5_relat_1(B_26,k2_relat_1(B_26))
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_8354,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8348,c_44])).

tff(c_8358,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6699,c_6746,c_8348,c_8354])).

tff(c_8360,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6593,c_8358])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:08:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.68/2.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.68/2.70  
% 7.68/2.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.68/2.70  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.68/2.70  
% 7.68/2.70  %Foreground sorts:
% 7.68/2.70  
% 7.68/2.70  
% 7.68/2.70  %Background operators:
% 7.68/2.70  
% 7.68/2.70  
% 7.68/2.70  %Foreground operators:
% 7.68/2.70  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.68/2.70  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.68/2.70  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.68/2.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.68/2.70  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.68/2.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.68/2.70  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.68/2.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.68/2.70  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.68/2.70  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.68/2.70  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.68/2.70  tff('#skF_2', type, '#skF_2': $i).
% 7.68/2.70  tff('#skF_3', type, '#skF_3': $i).
% 7.68/2.70  tff('#skF_1', type, '#skF_1': $i).
% 7.68/2.70  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 7.68/2.70  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.68/2.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.68/2.70  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.68/2.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.68/2.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.68/2.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.68/2.70  tff('#skF_4', type, '#skF_4': $i).
% 7.68/2.70  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.68/2.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.68/2.70  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.68/2.70  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.68/2.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.68/2.70  
% 7.86/2.75  tff(f_119, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.86/2.75  tff(f_63, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 7.86/2.75  tff(f_178, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 7.86/2.75  tff(f_117, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.86/2.75  tff(f_107, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.86/2.75  tff(f_87, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 7.86/2.75  tff(f_85, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.86/2.75  tff(f_59, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 7.86/2.75  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 7.86/2.75  tff(f_158, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 7.86/2.75  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.86/2.75  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.86/2.75  tff(f_136, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 7.86/2.75  tff(f_47, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 7.86/2.75  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.86/2.75  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 7.86/2.75  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 7.86/2.75  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.86/2.75  tff(f_95, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 7.86/2.75  tff(c_54, plain, (![A_39]: (k6_relat_1(A_39)=k6_partfun1(A_39))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.86/2.75  tff(c_28, plain, (![A_10]: (v2_funct_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.86/2.75  tff(c_78, plain, (![A_10]: (v2_funct_1(k6_partfun1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_28])).
% 7.86/2.75  tff(c_76, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_178])).
% 7.86/2.75  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_178])).
% 7.86/2.75  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_178])).
% 7.86/2.75  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_178])).
% 7.86/2.75  tff(c_1834, plain, (![B_252, C_249, F_250, D_251, E_248, A_247]: (k1_partfun1(A_247, B_252, C_249, D_251, E_248, F_250)=k5_relat_1(E_248, F_250) | ~m1_subset_1(F_250, k1_zfmisc_1(k2_zfmisc_1(C_249, D_251))) | ~v1_funct_1(F_250) | ~m1_subset_1(E_248, k1_zfmisc_1(k2_zfmisc_1(A_247, B_252))) | ~v1_funct_1(E_248))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.86/2.75  tff(c_1840, plain, (![A_247, B_252, E_248]: (k1_partfun1(A_247, B_252, '#skF_2', '#skF_1', E_248, '#skF_4')=k5_relat_1(E_248, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_248, k1_zfmisc_1(k2_zfmisc_1(A_247, B_252))) | ~v1_funct_1(E_248))), inference(resolution, [status(thm)], [c_66, c_1834])).
% 7.86/2.75  tff(c_2250, plain, (![A_285, B_286, E_287]: (k1_partfun1(A_285, B_286, '#skF_2', '#skF_1', E_287, '#skF_4')=k5_relat_1(E_287, '#skF_4') | ~m1_subset_1(E_287, k1_zfmisc_1(k2_zfmisc_1(A_285, B_286))) | ~v1_funct_1(E_287))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1840])).
% 7.86/2.75  tff(c_2271, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_2250])).
% 7.86/2.75  tff(c_2286, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2271])).
% 7.86/2.75  tff(c_48, plain, (![C_29, D_30, B_28, F_32, A_27, E_31]: (m1_subset_1(k1_partfun1(A_27, B_28, C_29, D_30, E_31, F_32), k1_zfmisc_1(k2_zfmisc_1(A_27, D_30))) | ~m1_subset_1(F_32, k1_zfmisc_1(k2_zfmisc_1(C_29, D_30))) | ~v1_funct_1(F_32) | ~m1_subset_1(E_31, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~v1_funct_1(E_31))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.86/2.75  tff(c_2423, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2286, c_48])).
% 7.86/2.75  tff(c_2432, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_70, c_66, c_2423])).
% 7.86/2.75  tff(c_42, plain, (![A_24]: (m1_subset_1(k6_relat_1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.86/2.75  tff(c_77, plain, (![A_24]: (m1_subset_1(k6_partfun1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_42])).
% 7.86/2.75  tff(c_64, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_178])).
% 7.86/2.75  tff(c_1572, plain, (![D_217, C_218, A_219, B_220]: (D_217=C_218 | ~r2_relset_1(A_219, B_220, C_218, D_217) | ~m1_subset_1(D_217, k1_zfmisc_1(k2_zfmisc_1(A_219, B_220))) | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(A_219, B_220))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.86/2.75  tff(c_1584, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_64, c_1572])).
% 7.86/2.75  tff(c_1604, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_1584])).
% 7.86/2.75  tff(c_2541, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2432, c_2286, c_2286, c_1604])).
% 7.86/2.75  tff(c_62, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_178])).
% 7.86/2.75  tff(c_121, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_62])).
% 7.86/2.75  tff(c_24, plain, (![A_9]: (k2_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.86/2.75  tff(c_80, plain, (![A_9]: (k2_relat_1(k6_partfun1(A_9))=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_24])).
% 7.86/2.75  tff(c_26, plain, (![A_10]: (v1_relat_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.86/2.75  tff(c_79, plain, (![A_10]: (v1_relat_1(k6_partfun1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_26])).
% 7.86/2.75  tff(c_122, plain, (![A_58]: (k2_relat_1(A_58)!=k1_xboole_0 | k1_xboole_0=A_58 | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.86/2.75  tff(c_125, plain, (![A_10]: (k2_relat_1(k6_partfun1(A_10))!=k1_xboole_0 | k6_partfun1(A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_79, c_122])).
% 7.86/2.75  tff(c_127, plain, (![A_10]: (k1_xboole_0!=A_10 | k6_partfun1(A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_80, c_125])).
% 7.86/2.75  tff(c_214, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_xboole_0) | k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_127, c_64])).
% 7.86/2.75  tff(c_250, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_214])).
% 7.86/2.75  tff(c_74, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 7.86/2.75  tff(c_68, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_178])).
% 7.86/2.75  tff(c_60, plain, (![E_50, D_48, C_47, A_45, B_46]: (k1_xboole_0=C_47 | v2_funct_1(D_48) | ~v2_funct_1(k1_partfun1(A_45, B_46, B_46, C_47, D_48, E_50)) | ~m1_subset_1(E_50, k1_zfmisc_1(k2_zfmisc_1(B_46, C_47))) | ~v1_funct_2(E_50, B_46, C_47) | ~v1_funct_1(E_50) | ~m1_subset_1(D_48, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))) | ~v1_funct_2(D_48, A_45, B_46) | ~v1_funct_1(D_48))), inference(cnfTransformation, [status(thm)], [f_158])).
% 7.86/2.75  tff(c_2420, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2286, c_60])).
% 7.86/2.75  tff(c_2429, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_70, c_68, c_66, c_2420])).
% 7.86/2.75  tff(c_2430, plain, (~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_121, c_250, c_2429])).
% 7.86/2.75  tff(c_2547, plain, (~v2_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2541, c_2430])).
% 7.86/2.75  tff(c_2557, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_2547])).
% 7.86/2.75  tff(c_2559, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_214])).
% 7.86/2.75  tff(c_198, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.86/2.75  tff(c_210, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_198])).
% 7.86/2.75  tff(c_18, plain, (![A_8]: (k2_relat_1(A_8)!=k1_xboole_0 | k1_xboole_0=A_8 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.86/2.75  tff(c_222, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_210, c_18])).
% 7.86/2.75  tff(c_232, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_222])).
% 7.86/2.75  tff(c_2561, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2559, c_232])).
% 7.86/2.75  tff(c_3207, plain, (![D_376, A_372, B_377, E_373, C_374, F_375]: (k1_partfun1(A_372, B_377, C_374, D_376, E_373, F_375)=k5_relat_1(E_373, F_375) | ~m1_subset_1(F_375, k1_zfmisc_1(k2_zfmisc_1(C_374, D_376))) | ~v1_funct_1(F_375) | ~m1_subset_1(E_373, k1_zfmisc_1(k2_zfmisc_1(A_372, B_377))) | ~v1_funct_1(E_373))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.86/2.75  tff(c_3213, plain, (![A_372, B_377, E_373]: (k1_partfun1(A_372, B_377, '#skF_2', '#skF_1', E_373, '#skF_4')=k5_relat_1(E_373, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_373, k1_zfmisc_1(k2_zfmisc_1(A_372, B_377))) | ~v1_funct_1(E_373))), inference(resolution, [status(thm)], [c_66, c_3207])).
% 7.86/2.75  tff(c_3500, plain, (![A_402, B_403, E_404]: (k1_partfun1(A_402, B_403, '#skF_2', '#skF_1', E_404, '#skF_4')=k5_relat_1(E_404, '#skF_4') | ~m1_subset_1(E_404, k1_zfmisc_1(k2_zfmisc_1(A_402, B_403))) | ~v1_funct_1(E_404))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_3213])).
% 7.86/2.75  tff(c_3515, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_3500])).
% 7.86/2.75  tff(c_3524, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_3515])).
% 7.86/2.75  tff(c_2607, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2559, c_2559, c_127])).
% 7.86/2.75  tff(c_2608, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2607, c_64])).
% 7.86/2.75  tff(c_3605, plain, (r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3524, c_2608])).
% 7.86/2.75  tff(c_2939, plain, (![A_338, B_339, C_340]: (k2_relset_1(A_338, B_339, C_340)=k2_relat_1(C_340) | ~m1_subset_1(C_340, k1_zfmisc_1(k2_zfmisc_1(A_338, B_339))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.86/2.75  tff(c_2956, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_2939])).
% 7.86/2.75  tff(c_3746, plain, (![A_417, B_418, C_419, D_420]: (k2_relset_1(A_417, B_418, C_419)=B_418 | ~r2_relset_1(B_418, B_418, k1_partfun1(B_418, A_417, A_417, B_418, D_420, C_419), k6_partfun1(B_418)) | ~m1_subset_1(D_420, k1_zfmisc_1(k2_zfmisc_1(B_418, A_417))) | ~v1_funct_2(D_420, B_418, A_417) | ~v1_funct_1(D_420) | ~m1_subset_1(C_419, k1_zfmisc_1(k2_zfmisc_1(A_417, B_418))) | ~v1_funct_2(C_419, A_417, B_418) | ~v1_funct_1(C_419))), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.86/2.75  tff(c_3749, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_4'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3524, c_3746])).
% 7.86/2.75  tff(c_3754, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_76, c_74, c_72, c_3605, c_2607, c_2956, c_3749])).
% 7.86/2.75  tff(c_3756, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2561, c_3754])).
% 7.86/2.75  tff(c_3757, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_222])).
% 7.86/2.75  tff(c_16, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.86/2.75  tff(c_3765, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3757, c_3757, c_16])).
% 7.86/2.75  tff(c_20, plain, (![A_8]: (k1_relat_1(A_8)!=k1_xboole_0 | k1_xboole_0=A_8 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.86/2.75  tff(c_221, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_210, c_20])).
% 7.86/2.75  tff(c_231, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_221])).
% 7.86/2.75  tff(c_3759, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3757, c_231])).
% 7.86/2.75  tff(c_3785, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3765, c_3759])).
% 7.86/2.75  tff(c_3786, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_221])).
% 7.86/2.75  tff(c_129, plain, (![A_59]: (k1_xboole_0!=A_59 | k6_partfun1(A_59)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_80, c_125])).
% 7.86/2.75  tff(c_142, plain, (![A_59]: (v2_funct_1(k1_xboole_0) | k1_xboole_0!=A_59)), inference(superposition, [status(thm), theory('equality')], [c_129, c_78])).
% 7.86/2.75  tff(c_167, plain, (![A_59]: (k1_xboole_0!=A_59)), inference(splitLeft, [status(thm)], [c_142])).
% 7.86/2.75  tff(c_172, plain, $false, inference(negUnitSimplification, [status(thm)], [c_167, c_16])).
% 7.86/2.75  tff(c_173, plain, (v2_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_142])).
% 7.86/2.75  tff(c_3789, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3786, c_173])).
% 7.86/2.75  tff(c_211, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_198])).
% 7.86/2.75  tff(c_229, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_211, c_20])).
% 7.86/2.75  tff(c_4967, plain, (k1_relat_1('#skF_3')!='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3786, c_3786, c_229])).
% 7.86/2.75  tff(c_4968, plain, (k1_relat_1('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_4967])).
% 7.86/2.75  tff(c_3824, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_4') | '#skF_1'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3786, c_3786, c_214])).
% 7.86/2.75  tff(c_3825, plain, ('#skF_1'!='#skF_4'), inference(splitLeft, [status(thm)], [c_3824])).
% 7.86/2.75  tff(c_14, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.86/2.75  tff(c_3794, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3786, c_3786, c_14])).
% 7.86/2.75  tff(c_4133, plain, (![A_459, B_460, C_461]: (k2_relset_1(A_459, B_460, C_461)=k2_relat_1(C_461) | ~m1_subset_1(C_461, k1_zfmisc_1(k2_zfmisc_1(A_459, B_460))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.86/2.75  tff(c_4142, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_4133])).
% 7.86/2.75  tff(c_4151, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3794, c_4142])).
% 7.86/2.75  tff(c_4938, plain, (![A_541, B_542, C_543, D_544]: (k2_relset_1(A_541, B_542, C_543)=B_542 | ~r2_relset_1(B_542, B_542, k1_partfun1(B_542, A_541, A_541, B_542, D_544, C_543), k6_partfun1(B_542)) | ~m1_subset_1(D_544, k1_zfmisc_1(k2_zfmisc_1(B_542, A_541))) | ~v1_funct_2(D_544, B_542, A_541) | ~v1_funct_1(D_544) | ~m1_subset_1(C_543, k1_zfmisc_1(k2_zfmisc_1(A_541, B_542))) | ~v1_funct_2(C_543, A_541, B_542) | ~v1_funct_1(C_543))), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.86/2.75  tff(c_4947, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_4938])).
% 7.86/2.75  tff(c_4952, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_76, c_74, c_72, c_4151, c_4947])).
% 7.86/2.75  tff(c_4954, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3825, c_4952])).
% 7.86/2.75  tff(c_4956, plain, ('#skF_1'='#skF_4'), inference(splitRight, [status(thm)], [c_3824])).
% 7.86/2.75  tff(c_4959, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4956, c_72])).
% 7.86/2.75  tff(c_5129, plain, (![C_564, A_565, B_566]: (v4_relat_1(C_564, A_565) | ~m1_subset_1(C_564, k1_zfmisc_1(k2_zfmisc_1(A_565, B_566))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.86/2.75  tff(c_5139, plain, (v4_relat_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_4959, c_5129])).
% 7.86/2.75  tff(c_3793, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3786, c_3786, c_16])).
% 7.86/2.75  tff(c_4958, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_4956, c_66])).
% 7.86/2.75  tff(c_5979, plain, (![C_652, A_656, F_651, E_654, B_655, D_653]: (m1_subset_1(k1_partfun1(A_656, B_655, C_652, D_653, E_654, F_651), k1_zfmisc_1(k2_zfmisc_1(A_656, D_653))) | ~m1_subset_1(F_651, k1_zfmisc_1(k2_zfmisc_1(C_652, D_653))) | ~v1_funct_1(F_651) | ~m1_subset_1(E_654, k1_zfmisc_1(k2_zfmisc_1(A_656, B_655))) | ~v1_funct_1(E_654))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.86/2.75  tff(c_187, plain, (![A_61]: (m1_subset_1(k6_partfun1(A_61), k1_zfmisc_1(k2_zfmisc_1(A_61, A_61))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_42])).
% 7.86/2.75  tff(c_190, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_10, A_10))) | k1_xboole_0!=A_10)), inference(superposition, [status(thm), theory('equality')], [c_127, c_187])).
% 7.86/2.75  tff(c_5170, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_3786, c_3786, c_190])).
% 7.86/2.75  tff(c_3851, plain, (k6_partfun1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3786, c_3786, c_127])).
% 7.86/2.75  tff(c_4957, plain, (r2_relset_1('#skF_4', '#skF_4', k1_partfun1('#skF_4', '#skF_2', '#skF_2', '#skF_4', '#skF_3', '#skF_4'), k6_partfun1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4956, c_4956, c_4956, c_4956, c_4956, c_64])).
% 7.86/2.75  tff(c_5079, plain, (r2_relset_1('#skF_4', '#skF_4', k1_partfun1('#skF_4', '#skF_2', '#skF_2', '#skF_4', '#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3851, c_4957])).
% 7.86/2.75  tff(c_5467, plain, (![D_599, C_600, A_601, B_602]: (D_599=C_600 | ~r2_relset_1(A_601, B_602, C_600, D_599) | ~m1_subset_1(D_599, k1_zfmisc_1(k2_zfmisc_1(A_601, B_602))) | ~m1_subset_1(C_600, k1_zfmisc_1(k2_zfmisc_1(A_601, B_602))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.86/2.75  tff(c_5481, plain, (k1_partfun1('#skF_4', '#skF_2', '#skF_2', '#skF_4', '#skF_3', '#skF_4')='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~m1_subset_1(k1_partfun1('#skF_4', '#skF_2', '#skF_2', '#skF_4', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(resolution, [status(thm)], [c_5079, c_5467])).
% 7.86/2.75  tff(c_5504, plain, (k1_partfun1('#skF_4', '#skF_2', '#skF_2', '#skF_4', '#skF_3', '#skF_4')='#skF_4' | ~m1_subset_1(k1_partfun1('#skF_4', '#skF_2', '#skF_2', '#skF_4', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_5170, c_5481])).
% 7.86/2.75  tff(c_5568, plain, (~m1_subset_1(k1_partfun1('#skF_4', '#skF_2', '#skF_2', '#skF_4', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(splitLeft, [status(thm)], [c_5504])).
% 7.86/2.75  tff(c_5985, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_5979, c_5568])).
% 7.86/2.75  tff(c_6011, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_4959, c_70, c_4958, c_5985])).
% 7.86/2.75  tff(c_6012, plain, (k1_partfun1('#skF_4', '#skF_2', '#skF_2', '#skF_4', '#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_5504])).
% 7.86/2.75  tff(c_6381, plain, (![E_691, A_690, C_692, D_694, B_695, F_693]: (k1_partfun1(A_690, B_695, C_692, D_694, E_691, F_693)=k5_relat_1(E_691, F_693) | ~m1_subset_1(F_693, k1_zfmisc_1(k2_zfmisc_1(C_692, D_694))) | ~v1_funct_1(F_693) | ~m1_subset_1(E_691, k1_zfmisc_1(k2_zfmisc_1(A_690, B_695))) | ~v1_funct_1(E_691))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.86/2.75  tff(c_6387, plain, (![A_690, B_695, E_691]: (k1_partfun1(A_690, B_695, '#skF_2', '#skF_4', E_691, '#skF_4')=k5_relat_1(E_691, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_691, k1_zfmisc_1(k2_zfmisc_1(A_690, B_695))) | ~v1_funct_1(E_691))), inference(resolution, [status(thm)], [c_4958, c_6381])).
% 7.86/2.75  tff(c_6505, plain, (![A_715, B_716, E_717]: (k1_partfun1(A_715, B_716, '#skF_2', '#skF_4', E_717, '#skF_4')=k5_relat_1(E_717, '#skF_4') | ~m1_subset_1(E_717, k1_zfmisc_1(k2_zfmisc_1(A_715, B_716))) | ~v1_funct_1(E_717))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_6387])).
% 7.86/2.75  tff(c_6514, plain, (k1_partfun1('#skF_4', '#skF_2', '#skF_2', '#skF_4', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_4959, c_6505])).
% 7.86/2.75  tff(c_6527, plain, (k5_relat_1('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_6012, c_6514])).
% 7.86/2.75  tff(c_12, plain, (![A_5, B_7]: (r1_tarski(k1_relat_1(k5_relat_1(A_5, B_7)), k1_relat_1(A_5)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.86/2.75  tff(c_6537, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6527, c_12])).
% 7.86/2.75  tff(c_6543, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_211, c_210, c_3793, c_6537])).
% 7.86/2.75  tff(c_4973, plain, (![B_545, A_546]: (r1_tarski(k1_relat_1(B_545), A_546) | ~v4_relat_1(B_545, A_546) | ~v1_relat_1(B_545))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.86/2.75  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.86/2.75  tff(c_4986, plain, (![B_545, A_546]: (k1_relat_1(B_545)=A_546 | ~r1_tarski(A_546, k1_relat_1(B_545)) | ~v4_relat_1(B_545, A_546) | ~v1_relat_1(B_545))), inference(resolution, [status(thm)], [c_4973, c_2])).
% 7.86/2.75  tff(c_6567, plain, (k1_relat_1('#skF_3')='#skF_4' | ~v4_relat_1('#skF_3', '#skF_4') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6543, c_4986])).
% 7.86/2.75  tff(c_6580, plain, (k1_relat_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_211, c_5139, c_6567])).
% 7.86/2.75  tff(c_6582, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4968, c_6580])).
% 7.86/2.75  tff(c_6583, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_4967])).
% 7.86/2.75  tff(c_6587, plain, (~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6583, c_121])).
% 7.86/2.75  tff(c_6592, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3789, c_6587])).
% 7.86/2.75  tff(c_6593, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_62])).
% 7.86/2.75  tff(c_6686, plain, (![C_725, A_726, B_727]: (v1_relat_1(C_725) | ~m1_subset_1(C_725, k1_zfmisc_1(k2_zfmisc_1(A_726, B_727))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.86/2.75  tff(c_6699, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_6686])).
% 7.86/2.75  tff(c_6734, plain, (![C_730, B_731, A_732]: (v5_relat_1(C_730, B_731) | ~m1_subset_1(C_730, k1_zfmisc_1(k2_zfmisc_1(A_732, B_731))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.86/2.75  tff(c_6746, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_6734])).
% 7.86/2.75  tff(c_6974, plain, (![A_763, B_764, D_765]: (r2_relset_1(A_763, B_764, D_765, D_765) | ~m1_subset_1(D_765, k1_zfmisc_1(k2_zfmisc_1(A_763, B_764))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.86/2.75  tff(c_6984, plain, (![A_24]: (r2_relset_1(A_24, A_24, k6_partfun1(A_24), k6_partfun1(A_24)))), inference(resolution, [status(thm)], [c_77, c_6974])).
% 7.86/2.75  tff(c_7001, plain, (![A_767, B_768, C_769]: (k2_relset_1(A_767, B_768, C_769)=k2_relat_1(C_769) | ~m1_subset_1(C_769, k1_zfmisc_1(k2_zfmisc_1(A_767, B_768))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.86/2.75  tff(c_7019, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_7001])).
% 7.86/2.75  tff(c_7534, plain, (![E_829, A_831, B_830, F_826, C_827, D_828]: (m1_subset_1(k1_partfun1(A_831, B_830, C_827, D_828, E_829, F_826), k1_zfmisc_1(k2_zfmisc_1(A_831, D_828))) | ~m1_subset_1(F_826, k1_zfmisc_1(k2_zfmisc_1(C_827, D_828))) | ~v1_funct_1(F_826) | ~m1_subset_1(E_829, k1_zfmisc_1(k2_zfmisc_1(A_831, B_830))) | ~v1_funct_1(E_829))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.86/2.75  tff(c_7057, plain, (![D_773, C_774, A_775, B_776]: (D_773=C_774 | ~r2_relset_1(A_775, B_776, C_774, D_773) | ~m1_subset_1(D_773, k1_zfmisc_1(k2_zfmisc_1(A_775, B_776))) | ~m1_subset_1(C_774, k1_zfmisc_1(k2_zfmisc_1(A_775, B_776))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.86/2.75  tff(c_7065, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_64, c_7057])).
% 7.86/2.75  tff(c_7080, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_7065])).
% 7.86/2.75  tff(c_7116, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_7080])).
% 7.86/2.75  tff(c_7537, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_7534, c_7116])).
% 7.86/2.75  tff(c_7565, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_70, c_66, c_7537])).
% 7.86/2.75  tff(c_7566, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_7080])).
% 7.86/2.75  tff(c_8335, plain, (![A_903, B_904, C_905, D_906]: (k2_relset_1(A_903, B_904, C_905)=B_904 | ~r2_relset_1(B_904, B_904, k1_partfun1(B_904, A_903, A_903, B_904, D_906, C_905), k6_partfun1(B_904)) | ~m1_subset_1(D_906, k1_zfmisc_1(k2_zfmisc_1(B_904, A_903))) | ~v1_funct_2(D_906, B_904, A_903) | ~v1_funct_1(D_906) | ~m1_subset_1(C_905, k1_zfmisc_1(k2_zfmisc_1(A_903, B_904))) | ~v1_funct_2(C_905, A_903, B_904) | ~v1_funct_1(C_905))), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.86/2.75  tff(c_8341, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7566, c_8335])).
% 7.86/2.75  tff(c_8348, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_76, c_74, c_72, c_6984, c_7019, c_8341])).
% 7.86/2.75  tff(c_44, plain, (![B_26]: (v2_funct_2(B_26, k2_relat_1(B_26)) | ~v5_relat_1(B_26, k2_relat_1(B_26)) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.86/2.75  tff(c_8354, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8348, c_44])).
% 7.86/2.75  tff(c_8358, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6699, c_6746, c_8348, c_8354])).
% 7.86/2.75  tff(c_8360, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6593, c_8358])).
% 7.86/2.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.86/2.75  
% 7.86/2.75  Inference rules
% 7.86/2.75  ----------------------
% 7.86/2.75  #Ref     : 8
% 7.86/2.75  #Sup     : 1730
% 7.86/2.75  #Fact    : 0
% 7.86/2.75  #Define  : 0
% 7.86/2.75  #Split   : 57
% 7.86/2.75  #Chain   : 0
% 7.86/2.75  #Close   : 0
% 7.86/2.75  
% 7.86/2.75  Ordering : KBO
% 7.86/2.75  
% 7.86/2.75  Simplification rules
% 7.86/2.75  ----------------------
% 7.86/2.75  #Subsume      : 345
% 7.86/2.75  #Demod        : 1309
% 7.86/2.75  #Tautology    : 498
% 7.86/2.75  #SimpNegUnit  : 36
% 7.86/2.75  #BackRed      : 74
% 7.86/2.75  
% 7.86/2.75  #Partial instantiations: 0
% 7.86/2.75  #Strategies tried      : 1
% 7.86/2.75  
% 7.86/2.75  Timing (in seconds)
% 7.86/2.75  ----------------------
% 8.02/2.76  Preprocessing        : 0.37
% 8.02/2.76  Parsing              : 0.20
% 8.02/2.76  CNF conversion       : 0.03
% 8.02/2.76  Main loop            : 1.58
% 8.02/2.76  Inferencing          : 0.54
% 8.02/2.76  Reduction            : 0.56
% 8.02/2.76  Demodulation         : 0.40
% 8.02/2.76  BG Simplification    : 0.05
% 8.02/2.76  Subsumption          : 0.29
% 8.02/2.76  Abstraction          : 0.07
% 8.02/2.76  MUC search           : 0.00
% 8.02/2.76  Cooper               : 0.00
% 8.02/2.76  Total                : 2.03
% 8.02/2.76  Index Insertion      : 0.00
% 8.02/2.76  Index Deletion       : 0.00
% 8.02/2.76  Index Matching       : 0.00
% 8.02/2.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
