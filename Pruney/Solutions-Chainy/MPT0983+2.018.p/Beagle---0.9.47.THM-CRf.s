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
% DateTime   : Thu Dec  3 10:12:03 EST 2020

% Result     : Theorem 4.74s
% Output     : CNFRefutation 4.74s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 336 expanded)
%              Number of leaves         :   44 ( 140 expanded)
%              Depth                    :   10
%              Number of atoms          :  215 (1067 expanded)
%              Number of equality atoms :   30 (  97 expanded)
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

tff(f_170,negated_conjecture,(
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

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_111,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_109,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_89,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_150,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_75,axiom,(
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

tff(f_128,axiom,(
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

tff(f_97,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_133,plain,(
    ! [A_58] :
      ( v2_funct_1(A_58)
      | ~ v1_funct_1(A_58)
      | ~ v1_relat_1(A_58)
      | ~ v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_58,plain,
    ( ~ v2_funct_2('#skF_5','#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_116,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_136,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_133,c_116])).

tff(c_139,plain,
    ( ~ v1_relat_1('#skF_4')
    | ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_136])).

tff(c_140,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_66,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_64,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_62,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_50,plain,(
    ! [A_35] : k6_relat_1(A_35) = k6_partfun1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_26,plain,(
    ! [A_12] : v2_funct_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_74,plain,(
    ! [A_12] : v2_funct_1(k6_partfun1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_26])).

tff(c_1019,plain,(
    ! [E_223,B_220,C_224,D_219,A_221,F_222] :
      ( m1_subset_1(k1_partfun1(A_221,B_220,C_224,D_219,E_223,F_222),k1_zfmisc_1(k2_zfmisc_1(A_221,D_219)))
      | ~ m1_subset_1(F_222,k1_zfmisc_1(k2_zfmisc_1(C_224,D_219)))
      | ~ v1_funct_1(F_222)
      | ~ m1_subset_1(E_223,k1_zfmisc_1(k2_zfmisc_1(A_221,B_220)))
      | ~ v1_funct_1(E_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_40,plain,(
    ! [A_26] : m1_subset_1(k6_relat_1(A_26),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_73,plain,(
    ! [A_26] : m1_subset_1(k6_partfun1(A_26),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_40])).

tff(c_60,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_861,plain,(
    ! [D_187,C_188,A_189,B_190] :
      ( D_187 = C_188
      | ~ r2_relset_1(A_189,B_190,C_188,D_187)
      | ~ m1_subset_1(D_187,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190)))
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_869,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_60,c_861])).

tff(c_884,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_869])).

tff(c_902,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_884])).

tff(c_1025,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1019,c_902])).

tff(c_1054,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_66,c_62,c_1025])).

tff(c_1055,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_884])).

tff(c_1293,plain,(
    ! [D_278,C_277,B_279,E_275,A_276] :
      ( k1_xboole_0 = C_277
      | v2_funct_1(D_278)
      | ~ v2_funct_1(k1_partfun1(A_276,B_279,B_279,C_277,D_278,E_275))
      | ~ m1_subset_1(E_275,k1_zfmisc_1(k2_zfmisc_1(B_279,C_277)))
      | ~ v1_funct_2(E_275,B_279,C_277)
      | ~ v1_funct_1(E_275)
      | ~ m1_subset_1(D_278,k1_zfmisc_1(k2_zfmisc_1(A_276,B_279)))
      | ~ v1_funct_2(D_278,A_276,B_279)
      | ~ v1_funct_1(D_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_1295,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1055,c_1293])).

tff(c_1300,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_64,c_62,c_74,c_1295])).

tff(c_1301,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_1300])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1336,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1301,c_6])).

tff(c_12,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1334,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_2',B_6) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1301,c_1301,c_12])).

tff(c_196,plain,(
    ! [C_69,B_70,A_71] :
      ( ~ v1_xboole_0(C_69)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(C_69))
      | ~ r2_hidden(A_71,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_210,plain,(
    ! [A_71] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_71,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_196])).

tff(c_746,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_210])).

tff(c_1401,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1334,c_746])).

tff(c_1405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1336,c_1401])).

tff(c_1408,plain,(
    ! [A_282] : ~ r2_hidden(A_282,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_1412,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_1408])).

tff(c_1416,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_1412])).

tff(c_1417,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_1419,plain,(
    ! [C_283,A_284,B_285] :
      ( v1_relat_1(C_283)
      | ~ m1_subset_1(C_283,k1_zfmisc_1(k2_zfmisc_1(A_284,B_285))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1428,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_1419])).

tff(c_1439,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1417,c_1428])).

tff(c_1440,plain,(
    ~ v2_funct_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1470,plain,(
    ! [C_293,A_294,B_295] :
      ( v1_relat_1(C_293)
      | ~ m1_subset_1(C_293,k1_zfmisc_1(k2_zfmisc_1(A_294,B_295))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1486,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_1470])).

tff(c_1494,plain,(
    ! [C_297,B_298,A_299] :
      ( v5_relat_1(C_297,B_298)
      | ~ m1_subset_1(C_297,k1_zfmisc_1(k2_zfmisc_1(A_299,B_298))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1511,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_1494])).

tff(c_1577,plain,(
    ! [A_316,B_317,D_318] :
      ( r2_relset_1(A_316,B_317,D_318,D_318)
      | ~ m1_subset_1(D_318,k1_zfmisc_1(k2_zfmisc_1(A_316,B_317))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1588,plain,(
    ! [A_26] : r2_relset_1(A_26,A_26,k6_partfun1(A_26),k6_partfun1(A_26)) ),
    inference(resolution,[status(thm)],[c_73,c_1577])).

tff(c_1637,plain,(
    ! [A_325,B_326,C_327] :
      ( k2_relset_1(A_325,B_326,C_327) = k2_relat_1(C_327)
      | ~ m1_subset_1(C_327,k1_zfmisc_1(k2_zfmisc_1(A_325,B_326))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1654,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_1637])).

tff(c_46,plain,(
    ! [E_33,A_29,F_34,D_32,C_31,B_30] :
      ( m1_subset_1(k1_partfun1(A_29,B_30,C_31,D_32,E_33,F_34),k1_zfmisc_1(k2_zfmisc_1(A_29,D_32)))
      | ~ m1_subset_1(F_34,k1_zfmisc_1(k2_zfmisc_1(C_31,D_32)))
      | ~ v1_funct_1(F_34)
      | ~ m1_subset_1(E_33,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30)))
      | ~ v1_funct_1(E_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1673,plain,(
    ! [D_329,C_330,A_331,B_332] :
      ( D_329 = C_330
      | ~ r2_relset_1(A_331,B_332,C_330,D_329)
      | ~ m1_subset_1(D_329,k1_zfmisc_1(k2_zfmisc_1(A_331,B_332)))
      | ~ m1_subset_1(C_330,k1_zfmisc_1(k2_zfmisc_1(A_331,B_332))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1681,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_60,c_1673])).

tff(c_1696,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_1681])).

tff(c_1917,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1696])).

tff(c_1920,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_1917])).

tff(c_1924,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_66,c_62,c_1920])).

tff(c_1925,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1696])).

tff(c_2024,plain,(
    ! [A_418,B_419,C_420,D_421] :
      ( k2_relset_1(A_418,B_419,C_420) = B_419
      | ~ r2_relset_1(B_419,B_419,k1_partfun1(B_419,A_418,A_418,B_419,D_421,C_420),k6_partfun1(B_419))
      | ~ m1_subset_1(D_421,k1_zfmisc_1(k2_zfmisc_1(B_419,A_418)))
      | ~ v1_funct_2(D_421,B_419,A_418)
      | ~ v1_funct_1(D_421)
      | ~ m1_subset_1(C_420,k1_zfmisc_1(k2_zfmisc_1(A_418,B_419)))
      | ~ v1_funct_2(C_420,A_418,B_419)
      | ~ v1_funct_1(C_420) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_2027,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1925,c_2024])).

tff(c_2029,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_72,c_70,c_68,c_1588,c_1654,c_2027])).

tff(c_42,plain,(
    ! [B_28] :
      ( v2_funct_2(B_28,k2_relat_1(B_28))
      | ~ v5_relat_1(B_28,k2_relat_1(B_28))
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2034,plain,
    ( v2_funct_2('#skF_5',k2_relat_1('#skF_5'))
    | ~ v5_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2029,c_42])).

tff(c_2038,plain,(
    v2_funct_2('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1486,c_1511,c_2029,c_2034])).

tff(c_2040,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1440,c_2038])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:42:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.74/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.74/1.85  
% 4.74/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.74/1.85  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 4.74/1.85  
% 4.74/1.85  %Foreground sorts:
% 4.74/1.85  
% 4.74/1.85  
% 4.74/1.85  %Background operators:
% 4.74/1.85  
% 4.74/1.85  
% 4.74/1.85  %Foreground operators:
% 4.74/1.85  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.74/1.85  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.74/1.85  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.74/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.74/1.85  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.74/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.74/1.85  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.74/1.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.74/1.85  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.74/1.85  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.74/1.85  tff('#skF_5', type, '#skF_5': $i).
% 4.74/1.85  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.74/1.85  tff('#skF_2', type, '#skF_2': $i).
% 4.74/1.85  tff('#skF_3', type, '#skF_3': $i).
% 4.74/1.85  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.74/1.85  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.74/1.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.74/1.85  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.74/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.74/1.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.74/1.85  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.74/1.85  tff('#skF_4', type, '#skF_4': $i).
% 4.74/1.85  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.74/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.74/1.85  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.74/1.85  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.74/1.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.74/1.85  
% 4.74/1.87  tff(f_170, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 4.74/1.87  tff(f_61, axiom, (![A]: (((v1_xboole_0(A) & v1_relat_1(A)) & v1_funct_1(A)) => ((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_1)).
% 4.74/1.87  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.74/1.87  tff(f_111, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.74/1.87  tff(f_65, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.74/1.87  tff(f_109, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.74/1.87  tff(f_89, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 4.74/1.87  tff(f_87, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.74/1.87  tff(f_150, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 4.74/1.87  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.74/1.87  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.74/1.87  tff(f_45, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.74/1.87  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.74/1.87  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.74/1.87  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.74/1.87  tff(f_128, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 4.74/1.87  tff(f_97, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 4.74/1.87  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.74/1.87  tff(c_133, plain, (![A_58]: (v2_funct_1(A_58) | ~v1_funct_1(A_58) | ~v1_relat_1(A_58) | ~v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.74/1.87  tff(c_58, plain, (~v2_funct_2('#skF_5', '#skF_2') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.74/1.87  tff(c_116, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_58])).
% 4.74/1.87  tff(c_136, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_133, c_116])).
% 4.74/1.87  tff(c_139, plain, (~v1_relat_1('#skF_4') | ~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_136])).
% 4.74/1.87  tff(c_140, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_139])).
% 4.74/1.87  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.74/1.87  tff(c_70, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.74/1.87  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.74/1.87  tff(c_66, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.74/1.87  tff(c_64, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.74/1.87  tff(c_62, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.74/1.87  tff(c_50, plain, (![A_35]: (k6_relat_1(A_35)=k6_partfun1(A_35))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.74/1.87  tff(c_26, plain, (![A_12]: (v2_funct_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.74/1.87  tff(c_74, plain, (![A_12]: (v2_funct_1(k6_partfun1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_26])).
% 4.74/1.87  tff(c_1019, plain, (![E_223, B_220, C_224, D_219, A_221, F_222]: (m1_subset_1(k1_partfun1(A_221, B_220, C_224, D_219, E_223, F_222), k1_zfmisc_1(k2_zfmisc_1(A_221, D_219))) | ~m1_subset_1(F_222, k1_zfmisc_1(k2_zfmisc_1(C_224, D_219))) | ~v1_funct_1(F_222) | ~m1_subset_1(E_223, k1_zfmisc_1(k2_zfmisc_1(A_221, B_220))) | ~v1_funct_1(E_223))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.74/1.87  tff(c_40, plain, (![A_26]: (m1_subset_1(k6_relat_1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.74/1.87  tff(c_73, plain, (![A_26]: (m1_subset_1(k6_partfun1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_40])).
% 4.74/1.87  tff(c_60, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.74/1.87  tff(c_861, plain, (![D_187, C_188, A_189, B_190]: (D_187=C_188 | ~r2_relset_1(A_189, B_190, C_188, D_187) | ~m1_subset_1(D_187, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))) | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.74/1.87  tff(c_869, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_60, c_861])).
% 4.74/1.87  tff(c_884, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_869])).
% 4.74/1.87  tff(c_902, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_884])).
% 4.74/1.87  tff(c_1025, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_1019, c_902])).
% 4.74/1.87  tff(c_1054, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_66, c_62, c_1025])).
% 4.74/1.87  tff(c_1055, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_884])).
% 4.74/1.87  tff(c_1293, plain, (![D_278, C_277, B_279, E_275, A_276]: (k1_xboole_0=C_277 | v2_funct_1(D_278) | ~v2_funct_1(k1_partfun1(A_276, B_279, B_279, C_277, D_278, E_275)) | ~m1_subset_1(E_275, k1_zfmisc_1(k2_zfmisc_1(B_279, C_277))) | ~v1_funct_2(E_275, B_279, C_277) | ~v1_funct_1(E_275) | ~m1_subset_1(D_278, k1_zfmisc_1(k2_zfmisc_1(A_276, B_279))) | ~v1_funct_2(D_278, A_276, B_279) | ~v1_funct_1(D_278))), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.74/1.87  tff(c_1295, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1055, c_1293])).
% 4.74/1.87  tff(c_1300, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_64, c_62, c_74, c_1295])).
% 4.74/1.87  tff(c_1301, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_116, c_1300])).
% 4.74/1.87  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.74/1.87  tff(c_1336, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1301, c_6])).
% 4.74/1.87  tff(c_12, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.74/1.87  tff(c_1334, plain, (![B_6]: (k2_zfmisc_1('#skF_2', B_6)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1301, c_1301, c_12])).
% 4.74/1.87  tff(c_196, plain, (![C_69, B_70, A_71]: (~v1_xboole_0(C_69) | ~m1_subset_1(B_70, k1_zfmisc_1(C_69)) | ~r2_hidden(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.74/1.87  tff(c_210, plain, (![A_71]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_71, '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_196])).
% 4.74/1.87  tff(c_746, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_210])).
% 4.74/1.87  tff(c_1401, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1334, c_746])).
% 4.74/1.87  tff(c_1405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1336, c_1401])).
% 4.74/1.87  tff(c_1408, plain, (![A_282]: (~r2_hidden(A_282, '#skF_4'))), inference(splitRight, [status(thm)], [c_210])).
% 4.74/1.87  tff(c_1412, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_1408])).
% 4.74/1.87  tff(c_1416, plain, $false, inference(negUnitSimplification, [status(thm)], [c_140, c_1412])).
% 4.74/1.87  tff(c_1417, plain, (~v1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_139])).
% 4.74/1.87  tff(c_1419, plain, (![C_283, A_284, B_285]: (v1_relat_1(C_283) | ~m1_subset_1(C_283, k1_zfmisc_1(k2_zfmisc_1(A_284, B_285))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.74/1.87  tff(c_1428, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_1419])).
% 4.74/1.87  tff(c_1439, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1417, c_1428])).
% 4.74/1.87  tff(c_1440, plain, (~v2_funct_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_58])).
% 4.74/1.87  tff(c_1470, plain, (![C_293, A_294, B_295]: (v1_relat_1(C_293) | ~m1_subset_1(C_293, k1_zfmisc_1(k2_zfmisc_1(A_294, B_295))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.74/1.87  tff(c_1486, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_1470])).
% 4.74/1.87  tff(c_1494, plain, (![C_297, B_298, A_299]: (v5_relat_1(C_297, B_298) | ~m1_subset_1(C_297, k1_zfmisc_1(k2_zfmisc_1(A_299, B_298))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.74/1.87  tff(c_1511, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_1494])).
% 4.74/1.87  tff(c_1577, plain, (![A_316, B_317, D_318]: (r2_relset_1(A_316, B_317, D_318, D_318) | ~m1_subset_1(D_318, k1_zfmisc_1(k2_zfmisc_1(A_316, B_317))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.74/1.87  tff(c_1588, plain, (![A_26]: (r2_relset_1(A_26, A_26, k6_partfun1(A_26), k6_partfun1(A_26)))), inference(resolution, [status(thm)], [c_73, c_1577])).
% 4.74/1.87  tff(c_1637, plain, (![A_325, B_326, C_327]: (k2_relset_1(A_325, B_326, C_327)=k2_relat_1(C_327) | ~m1_subset_1(C_327, k1_zfmisc_1(k2_zfmisc_1(A_325, B_326))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.74/1.87  tff(c_1654, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_1637])).
% 4.74/1.87  tff(c_46, plain, (![E_33, A_29, F_34, D_32, C_31, B_30]: (m1_subset_1(k1_partfun1(A_29, B_30, C_31, D_32, E_33, F_34), k1_zfmisc_1(k2_zfmisc_1(A_29, D_32))) | ~m1_subset_1(F_34, k1_zfmisc_1(k2_zfmisc_1(C_31, D_32))) | ~v1_funct_1(F_34) | ~m1_subset_1(E_33, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))) | ~v1_funct_1(E_33))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.74/1.87  tff(c_1673, plain, (![D_329, C_330, A_331, B_332]: (D_329=C_330 | ~r2_relset_1(A_331, B_332, C_330, D_329) | ~m1_subset_1(D_329, k1_zfmisc_1(k2_zfmisc_1(A_331, B_332))) | ~m1_subset_1(C_330, k1_zfmisc_1(k2_zfmisc_1(A_331, B_332))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.74/1.87  tff(c_1681, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_60, c_1673])).
% 4.74/1.87  tff(c_1696, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_1681])).
% 4.74/1.87  tff(c_1917, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1696])).
% 4.74/1.87  tff(c_1920, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_1917])).
% 4.74/1.87  tff(c_1924, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_66, c_62, c_1920])).
% 4.74/1.87  tff(c_1925, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_1696])).
% 4.74/1.87  tff(c_2024, plain, (![A_418, B_419, C_420, D_421]: (k2_relset_1(A_418, B_419, C_420)=B_419 | ~r2_relset_1(B_419, B_419, k1_partfun1(B_419, A_418, A_418, B_419, D_421, C_420), k6_partfun1(B_419)) | ~m1_subset_1(D_421, k1_zfmisc_1(k2_zfmisc_1(B_419, A_418))) | ~v1_funct_2(D_421, B_419, A_418) | ~v1_funct_1(D_421) | ~m1_subset_1(C_420, k1_zfmisc_1(k2_zfmisc_1(A_418, B_419))) | ~v1_funct_2(C_420, A_418, B_419) | ~v1_funct_1(C_420))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.74/1.87  tff(c_2027, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1925, c_2024])).
% 4.74/1.87  tff(c_2029, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_72, c_70, c_68, c_1588, c_1654, c_2027])).
% 4.74/1.87  tff(c_42, plain, (![B_28]: (v2_funct_2(B_28, k2_relat_1(B_28)) | ~v5_relat_1(B_28, k2_relat_1(B_28)) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.74/1.87  tff(c_2034, plain, (v2_funct_2('#skF_5', k2_relat_1('#skF_5')) | ~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2029, c_42])).
% 4.74/1.87  tff(c_2038, plain, (v2_funct_2('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1486, c_1511, c_2029, c_2034])).
% 4.74/1.87  tff(c_2040, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1440, c_2038])).
% 4.74/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.74/1.87  
% 4.74/1.87  Inference rules
% 4.74/1.87  ----------------------
% 4.74/1.87  #Ref     : 0
% 4.74/1.87  #Sup     : 423
% 4.74/1.87  #Fact    : 0
% 4.74/1.87  #Define  : 0
% 4.74/1.87  #Split   : 15
% 4.74/1.87  #Chain   : 0
% 4.74/1.87  #Close   : 0
% 4.74/1.87  
% 4.74/1.87  Ordering : KBO
% 4.74/1.87  
% 4.74/1.87  Simplification rules
% 4.74/1.87  ----------------------
% 4.74/1.87  #Subsume      : 15
% 4.74/1.87  #Demod        : 346
% 4.74/1.87  #Tautology    : 135
% 4.74/1.87  #SimpNegUnit  : 5
% 4.74/1.87  #BackRed      : 81
% 4.74/1.87  
% 4.74/1.87  #Partial instantiations: 0
% 4.74/1.87  #Strategies tried      : 1
% 4.74/1.87  
% 4.74/1.87  Timing (in seconds)
% 4.74/1.87  ----------------------
% 4.74/1.88  Preprocessing        : 0.34
% 4.74/1.88  Parsing              : 0.18
% 4.74/1.88  CNF conversion       : 0.02
% 4.74/1.88  Main loop            : 0.71
% 4.74/1.88  Inferencing          : 0.25
% 4.74/1.88  Reduction            : 0.25
% 4.74/1.88  Demodulation         : 0.18
% 4.74/1.88  BG Simplification    : 0.03
% 4.74/1.88  Subsumption          : 0.12
% 4.74/1.88  Abstraction          : 0.03
% 4.74/1.88  MUC search           : 0.00
% 4.74/1.88  Cooper               : 0.00
% 4.74/1.88  Total                : 1.09
% 4.74/1.88  Index Insertion      : 0.00
% 4.74/1.88  Index Deletion       : 0.00
% 4.74/1.88  Index Matching       : 0.00
% 4.74/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
