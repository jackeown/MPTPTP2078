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
% DateTime   : Thu Dec  3 10:12:02 EST 2020

% Result     : Theorem 4.83s
% Output     : CNFRefutation 5.02s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 288 expanded)
%              Number of leaves         :   49 ( 122 expanded)
%              Depth                    :    9
%              Number of atoms          :  252 ( 853 expanded)
%              Number of equality atoms :   34 (  80 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(f_187,negated_conjecture,(
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

tff(f_64,axiom,(
    ! [A] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_128,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_122,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_126,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_167,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_48,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v4_relat_1(k1_xboole_0,A)
      & v5_relat_1(k1_xboole_0,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l222_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_145,axiom,(
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

tff(f_110,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_84,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_178,plain,(
    ! [A_71] :
      ( v2_funct_1(A_71)
      | ~ v1_funct_1(A_71)
      | ~ v1_relat_1(A_71)
      | ~ v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_70,plain,
    ( ~ v2_funct_2('#skF_5','#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_148,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_181,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_178,c_148])).

tff(c_184,plain,
    ( ~ v1_relat_1('#skF_4')
    | ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_181])).

tff(c_185,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_80,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_296,plain,(
    ! [C_95,A_96,B_97] :
      ( v1_xboole_0(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97)))
      | ~ v1_xboole_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_305,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_296])).

tff(c_316,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_185,c_305])).

tff(c_82,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_78,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_76,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_74,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_62,plain,(
    ! [A_42] : k6_relat_1(A_42) = k6_partfun1(A_42) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_32,plain,(
    ! [A_13] : v2_funct_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_85,plain,(
    ! [A_13] : v2_funct_1(k6_partfun1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_32])).

tff(c_54,plain,(
    ! [A_35,F_40,B_36,C_37,D_38,E_39] :
      ( m1_subset_1(k1_partfun1(A_35,B_36,C_37,D_38,E_39,F_40),k1_zfmisc_1(k2_zfmisc_1(A_35,D_38)))
      | ~ m1_subset_1(F_40,k1_zfmisc_1(k2_zfmisc_1(C_37,D_38)))
      | ~ v1_funct_1(F_40)
      | ~ m1_subset_1(E_39,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36)))
      | ~ v1_funct_1(E_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_60,plain,(
    ! [A_41] : m1_subset_1(k6_partfun1(A_41),k1_zfmisc_1(k2_zfmisc_1(A_41,A_41))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_72,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_602,plain,(
    ! [D_133,C_134,A_135,B_136] :
      ( D_133 = C_134
      | ~ r2_relset_1(A_135,B_136,C_134,D_133)
      | ~ m1_subset_1(D_133,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136)))
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_612,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_72,c_602])).

tff(c_631,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_612])).

tff(c_841,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_631])).

tff(c_844,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_841])).

tff(c_848,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_78,c_74,c_844])).

tff(c_849,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_631])).

tff(c_870,plain,(
    ! [A_185,D_183,B_184,C_186,E_182] :
      ( k1_xboole_0 = C_186
      | v2_funct_1(D_183)
      | ~ v2_funct_1(k1_partfun1(A_185,B_184,B_184,C_186,D_183,E_182))
      | ~ m1_subset_1(E_182,k1_zfmisc_1(k2_zfmisc_1(B_184,C_186)))
      | ~ v1_funct_2(E_182,B_184,C_186)
      | ~ v1_funct_1(E_182)
      | ~ m1_subset_1(D_183,k1_zfmisc_1(k2_zfmisc_1(A_185,B_184)))
      | ~ v1_funct_2(D_183,A_185,B_184)
      | ~ v1_funct_1(D_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_872,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_849,c_870])).

tff(c_877,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_76,c_74,c_85,c_872])).

tff(c_878,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_877])).

tff(c_10,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_311,plain,(
    ! [C_95] :
      ( v1_xboole_0(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_296])).

tff(c_338,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_311])).

tff(c_105,plain,(
    ! [A_61] : k6_relat_1(A_61) = k6_partfun1(A_61) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_20,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_111,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_20])).

tff(c_8,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_161,plain,(
    ! [A_70] : m1_subset_1(k6_partfun1(A_70),k1_zfmisc_1(k2_zfmisc_1(A_70,A_70))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_165,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_161])).

tff(c_173,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_165])).

tff(c_30,plain,(
    ! [A_13] : v1_relat_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_86,plain,(
    ! [A_13] : v1_relat_1(k6_partfun1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_30])).

tff(c_122,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_86])).

tff(c_18,plain,(
    ! [B_10] : v5_relat_1(k1_xboole_0,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v5_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_308,plain,(
    ! [C_95,A_5] :
      ( v1_xboole_0(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_296])).

tff(c_372,plain,(
    ! [A_5] : ~ v1_xboole_0(A_5) ),
    inference(splitLeft,[status(thm)],[c_308])).

tff(c_151,plain,(
    ! [A_68] :
      ( v1_xboole_0(A_68)
      | r2_hidden('#skF_1'(A_68),A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    ! [B_15,A_14] :
      ( ~ r1_tarski(B_15,A_14)
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_158,plain,(
    ! [A_68] :
      ( ~ r1_tarski(A_68,'#skF_1'(A_68))
      | v1_xboole_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_151,c_34])).

tff(c_383,plain,(
    ! [A_106] : ~ r1_tarski(A_106,'#skF_1'(A_106)) ),
    inference(negUnitSimplification,[status(thm)],[c_372,c_158])).

tff(c_470,plain,(
    ! [B_118] :
      ( ~ v5_relat_1(B_118,'#skF_1'(k2_relat_1(B_118)))
      | ~ v1_relat_1(B_118) ) ),
    inference(resolution,[status(thm)],[c_14,c_383])).

tff(c_474,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_470])).

tff(c_478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_474])).

tff(c_480,plain,(
    ! [C_119] :
      ( v1_xboole_0(C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(splitRight,[status(thm)],[c_308])).

tff(c_483,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_173,c_480])).

tff(c_487,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_338,c_483])).

tff(c_489,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_311])).

tff(c_901,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_878,c_489])).

tff(c_918,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_316,c_901])).

tff(c_919,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_937,plain,(
    ! [C_189,A_190,B_191] :
      ( v1_relat_1(C_189)
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_190,B_191))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_946,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_937])).

tff(c_957,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_919,c_946])).

tff(c_958,plain,(
    ~ v2_funct_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_1001,plain,(
    ! [C_202,A_203,B_204] :
      ( v1_relat_1(C_202)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_203,B_204))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1017,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_1001])).

tff(c_1019,plain,(
    ! [C_205,B_206,A_207] :
      ( v5_relat_1(C_205,B_206)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_207,B_206))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1036,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_1019])).

tff(c_1256,plain,(
    ! [A_242,B_243,D_244] :
      ( r2_relset_1(A_242,B_243,D_244,D_244)
      | ~ m1_subset_1(D_244,k1_zfmisc_1(k2_zfmisc_1(A_242,B_243))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1267,plain,(
    ! [A_41] : r2_relset_1(A_41,A_41,k6_partfun1(A_41),k6_partfun1(A_41)) ),
    inference(resolution,[status(thm)],[c_60,c_1256])).

tff(c_1279,plain,(
    ! [A_246,B_247,C_248] :
      ( k2_relset_1(A_246,B_247,C_248) = k2_relat_1(C_248)
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(A_246,B_247))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1296,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_1279])).

tff(c_1468,plain,(
    ! [A_277,C_279,D_281,E_280,F_278,B_282] :
      ( m1_subset_1(k1_partfun1(A_277,B_282,C_279,D_281,E_280,F_278),k1_zfmisc_1(k2_zfmisc_1(A_277,D_281)))
      | ~ m1_subset_1(F_278,k1_zfmisc_1(k2_zfmisc_1(C_279,D_281)))
      | ~ v1_funct_1(F_278)
      | ~ m1_subset_1(E_280,k1_zfmisc_1(k2_zfmisc_1(A_277,B_282)))
      | ~ v1_funct_1(E_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1320,plain,(
    ! [D_250,C_251,A_252,B_253] :
      ( D_250 = C_251
      | ~ r2_relset_1(A_252,B_253,C_251,D_250)
      | ~ m1_subset_1(D_250,k1_zfmisc_1(k2_zfmisc_1(A_252,B_253)))
      | ~ m1_subset_1(C_251,k1_zfmisc_1(k2_zfmisc_1(A_252,B_253))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1330,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_72,c_1320])).

tff(c_1349,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1330])).

tff(c_1366,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1349])).

tff(c_1471,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1468,c_1366])).

tff(c_1503,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_78,c_74,c_1471])).

tff(c_1504,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1349])).

tff(c_1839,plain,(
    ! [A_362,B_363,C_364,D_365] :
      ( k2_relset_1(A_362,B_363,C_364) = B_363
      | ~ r2_relset_1(B_363,B_363,k1_partfun1(B_363,A_362,A_362,B_363,D_365,C_364),k6_partfun1(B_363))
      | ~ m1_subset_1(D_365,k1_zfmisc_1(k2_zfmisc_1(B_363,A_362)))
      | ~ v1_funct_2(D_365,B_363,A_362)
      | ~ v1_funct_1(D_365)
      | ~ m1_subset_1(C_364,k1_zfmisc_1(k2_zfmisc_1(A_362,B_363)))
      | ~ v1_funct_2(C_364,A_362,B_363)
      | ~ v1_funct_1(C_364) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1842,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1504,c_1839])).

tff(c_1847,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_84,c_82,c_80,c_1267,c_1296,c_1842])).

tff(c_50,plain,(
    ! [B_34] :
      ( v2_funct_2(B_34,k2_relat_1(B_34))
      | ~ v5_relat_1(B_34,k2_relat_1(B_34))
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1856,plain,
    ( v2_funct_2('#skF_5',k2_relat_1('#skF_5'))
    | ~ v5_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1847,c_50])).

tff(c_1869,plain,(
    v2_funct_2('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1017,c_1036,c_1847,c_1856])).

tff(c_1871,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_958,c_1869])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:21:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.83/1.99  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.83/2.00  
% 4.83/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.83/2.00  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 4.83/2.00  
% 4.83/2.00  %Foreground sorts:
% 4.83/2.00  
% 4.83/2.00  
% 4.83/2.00  %Background operators:
% 4.83/2.00  
% 4.83/2.00  
% 4.83/2.00  %Foreground operators:
% 4.83/2.00  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.83/2.00  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.83/2.00  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.83/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.83/2.00  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.83/2.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.83/2.00  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.83/2.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.83/2.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.83/2.00  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.83/2.00  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.83/2.00  tff('#skF_5', type, '#skF_5': $i).
% 4.83/2.00  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.83/2.00  tff('#skF_2', type, '#skF_2': $i).
% 4.83/2.00  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.83/2.00  tff('#skF_3', type, '#skF_3': $i).
% 4.83/2.00  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.83/2.00  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.83/2.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.83/2.00  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.83/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.83/2.00  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.83/2.00  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.83/2.00  tff('#skF_4', type, '#skF_4': $i).
% 4.83/2.00  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.83/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.83/2.00  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.83/2.00  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.83/2.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.83/2.00  
% 5.02/2.02  tff(f_187, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 5.02/2.02  tff(f_64, axiom, (![A]: (((v1_xboole_0(A) & v1_relat_1(A)) & v1_funct_1(A)) => ((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_1)).
% 5.02/2.02  tff(f_90, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 5.02/2.02  tff(f_128, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.02/2.02  tff(f_68, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.02/2.02  tff(f_122, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.02/2.02  tff(f_126, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.02/2.02  tff(f_102, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.02/2.02  tff(f_167, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 5.02/2.02  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.02/2.02  tff(f_48, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 5.02/2.02  tff(f_47, axiom, (![A, B]: (v4_relat_1(k1_xboole_0, A) & v5_relat_1(k1_xboole_0, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l222_relat_1)).
% 5.02/2.02  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 5.02/2.02  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.02/2.02  tff(f_73, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.02/2.02  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.02/2.02  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.02/2.02  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.02/2.02  tff(f_145, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 5.02/2.02  tff(f_110, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 5.02/2.02  tff(c_84, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.02/2.02  tff(c_178, plain, (![A_71]: (v2_funct_1(A_71) | ~v1_funct_1(A_71) | ~v1_relat_1(A_71) | ~v1_xboole_0(A_71))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.02/2.02  tff(c_70, plain, (~v2_funct_2('#skF_5', '#skF_2') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.02/2.02  tff(c_148, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_70])).
% 5.02/2.02  tff(c_181, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_178, c_148])).
% 5.02/2.02  tff(c_184, plain, (~v1_relat_1('#skF_4') | ~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_181])).
% 5.02/2.02  tff(c_185, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_184])).
% 5.02/2.02  tff(c_80, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.02/2.02  tff(c_296, plain, (![C_95, A_96, B_97]: (v1_xboole_0(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))) | ~v1_xboole_0(A_96))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.02/2.02  tff(c_305, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_80, c_296])).
% 5.02/2.02  tff(c_316, plain, (~v1_xboole_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_185, c_305])).
% 5.02/2.02  tff(c_82, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.02/2.02  tff(c_78, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.02/2.02  tff(c_76, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.02/2.02  tff(c_74, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.02/2.02  tff(c_62, plain, (![A_42]: (k6_relat_1(A_42)=k6_partfun1(A_42))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.02/2.02  tff(c_32, plain, (![A_13]: (v2_funct_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.02/2.02  tff(c_85, plain, (![A_13]: (v2_funct_1(k6_partfun1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_32])).
% 5.02/2.02  tff(c_54, plain, (![A_35, F_40, B_36, C_37, D_38, E_39]: (m1_subset_1(k1_partfun1(A_35, B_36, C_37, D_38, E_39, F_40), k1_zfmisc_1(k2_zfmisc_1(A_35, D_38))) | ~m1_subset_1(F_40, k1_zfmisc_1(k2_zfmisc_1(C_37, D_38))) | ~v1_funct_1(F_40) | ~m1_subset_1(E_39, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))) | ~v1_funct_1(E_39))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.02/2.02  tff(c_60, plain, (![A_41]: (m1_subset_1(k6_partfun1(A_41), k1_zfmisc_1(k2_zfmisc_1(A_41, A_41))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.02/2.02  tff(c_72, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.02/2.02  tff(c_602, plain, (![D_133, C_134, A_135, B_136]: (D_133=C_134 | ~r2_relset_1(A_135, B_136, C_134, D_133) | ~m1_subset_1(D_133, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.02/2.02  tff(c_612, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_72, c_602])).
% 5.02/2.02  tff(c_631, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_612])).
% 5.02/2.02  tff(c_841, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_631])).
% 5.02/2.02  tff(c_844, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_841])).
% 5.02/2.02  tff(c_848, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_78, c_74, c_844])).
% 5.02/2.02  tff(c_849, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_631])).
% 5.02/2.02  tff(c_870, plain, (![A_185, D_183, B_184, C_186, E_182]: (k1_xboole_0=C_186 | v2_funct_1(D_183) | ~v2_funct_1(k1_partfun1(A_185, B_184, B_184, C_186, D_183, E_182)) | ~m1_subset_1(E_182, k1_zfmisc_1(k2_zfmisc_1(B_184, C_186))) | ~v1_funct_2(E_182, B_184, C_186) | ~v1_funct_1(E_182) | ~m1_subset_1(D_183, k1_zfmisc_1(k2_zfmisc_1(A_185, B_184))) | ~v1_funct_2(D_183, A_185, B_184) | ~v1_funct_1(D_183))), inference(cnfTransformation, [status(thm)], [f_167])).
% 5.02/2.02  tff(c_872, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_849, c_870])).
% 5.02/2.02  tff(c_877, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_78, c_76, c_74, c_85, c_872])).
% 5.02/2.02  tff(c_878, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_148, c_877])).
% 5.02/2.02  tff(c_10, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.02/2.02  tff(c_311, plain, (![C_95]: (v1_xboole_0(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_296])).
% 5.02/2.02  tff(c_338, plain, (~v1_xboole_0(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_311])).
% 5.02/2.02  tff(c_105, plain, (![A_61]: (k6_relat_1(A_61)=k6_partfun1(A_61))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.02/2.02  tff(c_20, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.02/2.02  tff(c_111, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_105, c_20])).
% 5.02/2.02  tff(c_8, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.02/2.02  tff(c_161, plain, (![A_70]: (m1_subset_1(k6_partfun1(A_70), k1_zfmisc_1(k2_zfmisc_1(A_70, A_70))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.02/2.02  tff(c_165, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_161])).
% 5.02/2.02  tff(c_173, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_165])).
% 5.02/2.02  tff(c_30, plain, (![A_13]: (v1_relat_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.02/2.02  tff(c_86, plain, (![A_13]: (v1_relat_1(k6_partfun1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_30])).
% 5.02/2.02  tff(c_122, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_111, c_86])).
% 5.02/2.02  tff(c_18, plain, (![B_10]: (v5_relat_1(k1_xboole_0, B_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.02/2.02  tff(c_14, plain, (![B_8, A_7]: (r1_tarski(k2_relat_1(B_8), A_7) | ~v5_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.02/2.02  tff(c_308, plain, (![C_95, A_5]: (v1_xboole_0(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_296])).
% 5.02/2.02  tff(c_372, plain, (![A_5]: (~v1_xboole_0(A_5))), inference(splitLeft, [status(thm)], [c_308])).
% 5.02/2.02  tff(c_151, plain, (![A_68]: (v1_xboole_0(A_68) | r2_hidden('#skF_1'(A_68), A_68))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.02/2.02  tff(c_34, plain, (![B_15, A_14]: (~r1_tarski(B_15, A_14) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.02/2.02  tff(c_158, plain, (![A_68]: (~r1_tarski(A_68, '#skF_1'(A_68)) | v1_xboole_0(A_68))), inference(resolution, [status(thm)], [c_151, c_34])).
% 5.02/2.02  tff(c_383, plain, (![A_106]: (~r1_tarski(A_106, '#skF_1'(A_106)))), inference(negUnitSimplification, [status(thm)], [c_372, c_158])).
% 5.02/2.02  tff(c_470, plain, (![B_118]: (~v5_relat_1(B_118, '#skF_1'(k2_relat_1(B_118))) | ~v1_relat_1(B_118))), inference(resolution, [status(thm)], [c_14, c_383])).
% 5.02/2.02  tff(c_474, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_470])).
% 5.02/2.02  tff(c_478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_122, c_474])).
% 5.02/2.02  tff(c_480, plain, (![C_119]: (v1_xboole_0(C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_308])).
% 5.02/2.02  tff(c_483, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_173, c_480])).
% 5.02/2.02  tff(c_487, plain, $false, inference(negUnitSimplification, [status(thm)], [c_338, c_483])).
% 5.02/2.02  tff(c_489, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_311])).
% 5.02/2.02  tff(c_901, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_878, c_489])).
% 5.02/2.02  tff(c_918, plain, $false, inference(negUnitSimplification, [status(thm)], [c_316, c_901])).
% 5.02/2.02  tff(c_919, plain, (~v1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_184])).
% 5.02/2.02  tff(c_937, plain, (![C_189, A_190, B_191]: (v1_relat_1(C_189) | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_190, B_191))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.02/2.02  tff(c_946, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_80, c_937])).
% 5.02/2.02  tff(c_957, plain, $false, inference(negUnitSimplification, [status(thm)], [c_919, c_946])).
% 5.02/2.02  tff(c_958, plain, (~v2_funct_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_70])).
% 5.02/2.02  tff(c_1001, plain, (![C_202, A_203, B_204]: (v1_relat_1(C_202) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(A_203, B_204))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.02/2.02  tff(c_1017, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_1001])).
% 5.02/2.02  tff(c_1019, plain, (![C_205, B_206, A_207]: (v5_relat_1(C_205, B_206) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(A_207, B_206))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.02/2.02  tff(c_1036, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_74, c_1019])).
% 5.02/2.02  tff(c_1256, plain, (![A_242, B_243, D_244]: (r2_relset_1(A_242, B_243, D_244, D_244) | ~m1_subset_1(D_244, k1_zfmisc_1(k2_zfmisc_1(A_242, B_243))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.02/2.02  tff(c_1267, plain, (![A_41]: (r2_relset_1(A_41, A_41, k6_partfun1(A_41), k6_partfun1(A_41)))), inference(resolution, [status(thm)], [c_60, c_1256])).
% 5.02/2.02  tff(c_1279, plain, (![A_246, B_247, C_248]: (k2_relset_1(A_246, B_247, C_248)=k2_relat_1(C_248) | ~m1_subset_1(C_248, k1_zfmisc_1(k2_zfmisc_1(A_246, B_247))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.02/2.02  tff(c_1296, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_1279])).
% 5.02/2.02  tff(c_1468, plain, (![A_277, C_279, D_281, E_280, F_278, B_282]: (m1_subset_1(k1_partfun1(A_277, B_282, C_279, D_281, E_280, F_278), k1_zfmisc_1(k2_zfmisc_1(A_277, D_281))) | ~m1_subset_1(F_278, k1_zfmisc_1(k2_zfmisc_1(C_279, D_281))) | ~v1_funct_1(F_278) | ~m1_subset_1(E_280, k1_zfmisc_1(k2_zfmisc_1(A_277, B_282))) | ~v1_funct_1(E_280))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.02/2.02  tff(c_1320, plain, (![D_250, C_251, A_252, B_253]: (D_250=C_251 | ~r2_relset_1(A_252, B_253, C_251, D_250) | ~m1_subset_1(D_250, k1_zfmisc_1(k2_zfmisc_1(A_252, B_253))) | ~m1_subset_1(C_251, k1_zfmisc_1(k2_zfmisc_1(A_252, B_253))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.02/2.02  tff(c_1330, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_72, c_1320])).
% 5.02/2.02  tff(c_1349, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1330])).
% 5.02/2.02  tff(c_1366, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1349])).
% 5.02/2.02  tff(c_1471, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_1468, c_1366])).
% 5.02/2.02  tff(c_1503, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_78, c_74, c_1471])).
% 5.02/2.02  tff(c_1504, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_1349])).
% 5.02/2.02  tff(c_1839, plain, (![A_362, B_363, C_364, D_365]: (k2_relset_1(A_362, B_363, C_364)=B_363 | ~r2_relset_1(B_363, B_363, k1_partfun1(B_363, A_362, A_362, B_363, D_365, C_364), k6_partfun1(B_363)) | ~m1_subset_1(D_365, k1_zfmisc_1(k2_zfmisc_1(B_363, A_362))) | ~v1_funct_2(D_365, B_363, A_362) | ~v1_funct_1(D_365) | ~m1_subset_1(C_364, k1_zfmisc_1(k2_zfmisc_1(A_362, B_363))) | ~v1_funct_2(C_364, A_362, B_363) | ~v1_funct_1(C_364))), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.02/2.02  tff(c_1842, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1504, c_1839])).
% 5.02/2.02  tff(c_1847, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_84, c_82, c_80, c_1267, c_1296, c_1842])).
% 5.02/2.02  tff(c_50, plain, (![B_34]: (v2_funct_2(B_34, k2_relat_1(B_34)) | ~v5_relat_1(B_34, k2_relat_1(B_34)) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.02/2.02  tff(c_1856, plain, (v2_funct_2('#skF_5', k2_relat_1('#skF_5')) | ~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1847, c_50])).
% 5.02/2.02  tff(c_1869, plain, (v2_funct_2('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1017, c_1036, c_1847, c_1856])).
% 5.02/2.02  tff(c_1871, plain, $false, inference(negUnitSimplification, [status(thm)], [c_958, c_1869])).
% 5.02/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.02/2.02  
% 5.02/2.02  Inference rules
% 5.02/2.02  ----------------------
% 5.02/2.02  #Ref     : 0
% 5.02/2.02  #Sup     : 379
% 5.02/2.02  #Fact    : 0
% 5.02/2.02  #Define  : 0
% 5.02/2.02  #Split   : 16
% 5.02/2.02  #Chain   : 0
% 5.02/2.02  #Close   : 0
% 5.02/2.02  
% 5.02/2.02  Ordering : KBO
% 5.02/2.02  
% 5.02/2.02  Simplification rules
% 5.02/2.02  ----------------------
% 5.02/2.02  #Subsume      : 34
% 5.02/2.02  #Demod        : 298
% 5.02/2.02  #Tautology    : 132
% 5.02/2.02  #SimpNegUnit  : 15
% 5.02/2.02  #BackRed      : 45
% 5.02/2.02  
% 5.02/2.02  #Partial instantiations: 0
% 5.02/2.02  #Strategies tried      : 1
% 5.02/2.02  
% 5.02/2.02  Timing (in seconds)
% 5.02/2.02  ----------------------
% 5.02/2.03  Preprocessing        : 0.50
% 5.02/2.03  Parsing              : 0.31
% 5.02/2.03  CNF conversion       : 0.03
% 5.02/2.03  Main loop            : 0.66
% 5.02/2.03  Inferencing          : 0.24
% 5.02/2.03  Reduction            : 0.23
% 5.02/2.03  Demodulation         : 0.17
% 5.02/2.03  BG Simplification    : 0.03
% 5.02/2.03  Subsumption          : 0.11
% 5.02/2.03  Abstraction          : 0.03
% 5.02/2.03  MUC search           : 0.00
% 5.02/2.03  Cooper               : 0.00
% 5.02/2.03  Total                : 1.21
% 5.02/2.03  Index Insertion      : 0.00
% 5.02/2.03  Index Deletion       : 0.00
% 5.02/2.03  Index Matching       : 0.00
% 5.02/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
