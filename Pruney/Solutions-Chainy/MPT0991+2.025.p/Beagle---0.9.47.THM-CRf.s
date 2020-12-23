%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:30 EST 2020

% Result     : Theorem 5.30s
% Output     : CNFRefutation 5.30s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 232 expanded)
%              Number of leaves         :   61 ( 111 expanded)
%              Depth                    :    7
%              Number of atoms          :  211 ( 528 expanded)
%              Number of equality atoms :   62 ( 122 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k1_partfun1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_222,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( B != k1_xboole_0
            & ? [D] :
                ( v1_funct_1(D)
                & v1_funct_2(D,B,A)
                & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
                & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A)) )
            & ~ v2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_funct_2)).

tff(f_55,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_125,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_153,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_177,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_84,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_104,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_117,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( ? [B] :
            ( v1_relat_1(B)
            & v1_funct_1(B)
            & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
       => v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).

tff(f_165,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_135,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_133,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_199,axiom,(
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

tff(f_102,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( ! [B] :
            ~ ( r2_hidden(B,k2_relat_1(A))
              & ! [C] : k10_relat_1(A,k1_tarski(B)) != k1_tarski(C) )
      <=> v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_funct_1)).

tff(c_96,plain,(
    ~ v2_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_24,plain,(
    ! [A_33] : v1_xboole_0('#skF_1'(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_123,plain,(
    ! [A_100] :
      ( k1_xboole_0 = A_100
      | ~ v1_xboole_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_127,plain,(
    ! [A_33] : '#skF_1'(A_33) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_123])).

tff(c_26,plain,(
    ! [A_33] : m1_subset_1('#skF_1'(A_33),k1_zfmisc_1(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_186,plain,(
    ! [A_33] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_33)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_26])).

tff(c_2221,plain,(
    ! [C_381,B_382,A_383] :
      ( ~ v1_xboole_0(C_381)
      | ~ m1_subset_1(B_382,k1_zfmisc_1(C_381))
      | ~ r2_hidden(A_383,B_382) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2239,plain,(
    ! [A_33,A_383] :
      ( ~ v1_xboole_0(A_33)
      | ~ r2_hidden(A_383,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_186,c_2221])).

tff(c_2244,plain,(
    ! [A_383] : ~ r2_hidden(A_383,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2239])).

tff(c_108,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_312,plain,(
    ! [C_127,A_128,B_129] :
      ( v1_relat_1(C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_337,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_108,c_312])).

tff(c_112,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_106,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_110,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_595,plain,(
    ! [A_178,B_179,C_180] :
      ( k1_relset_1(A_178,B_179,C_180) = k1_relat_1(C_180)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_620,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_108,c_595])).

tff(c_927,plain,(
    ! [B_240,A_241,C_242] :
      ( k1_xboole_0 = B_240
      | k1_relset_1(A_241,B_240,C_242) = A_241
      | ~ v1_funct_2(C_242,A_241,B_240)
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(A_241,B_240))) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_937,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_108,c_927])).

tff(c_954,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_620,c_937])).

tff(c_955,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_954])).

tff(c_40,plain,(
    ! [A_44] :
      ( k1_relat_1(A_44) = k1_xboole_0
      | k2_relat_1(A_44) != k1_xboole_0
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_344,plain,
    ( k1_relat_1('#skF_7') = k1_xboole_0
    | k2_relat_1('#skF_7') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_337,c_40])).

tff(c_382,plain,(
    k2_relat_1('#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_344])).

tff(c_345,plain,(
    ! [A_130] :
      ( k2_relat_1(A_130) = k1_xboole_0
      | k1_relat_1(A_130) != k1_xboole_0
      | ~ v1_relat_1(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_352,plain,
    ( k2_relat_1('#skF_7') = k1_xboole_0
    | k1_relat_1('#skF_7') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_337,c_345])).

tff(c_383,plain,(
    k1_relat_1('#skF_7') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_382,c_352])).

tff(c_999,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_955,c_383])).

tff(c_104,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_102,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_100,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_90,plain,(
    ! [A_89] : k6_relat_1(A_89) = k6_partfun1(A_89) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_48,plain,(
    ! [A_46] : v1_relat_1(k6_relat_1(A_46)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_117,plain,(
    ! [A_46] : v1_relat_1(k6_partfun1(A_46)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_48])).

tff(c_50,plain,(
    ! [A_46] : v1_funct_1(k6_relat_1(A_46)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_116,plain,(
    ! [A_46] : v1_funct_1(k6_partfun1(A_46)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_50])).

tff(c_44,plain,(
    ! [A_45] : k1_relat_1(k6_relat_1(A_45)) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_119,plain,(
    ! [A_45] : k1_relat_1(k6_partfun1(A_45)) = A_45 ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_44])).

tff(c_58,plain,(
    ! [B_59,A_58] : k5_relat_1(k6_relat_1(B_59),k6_relat_1(A_58)) = k6_relat_1(k3_xboole_0(A_58,B_59)) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_115,plain,(
    ! [B_59,A_58] : k5_relat_1(k6_partfun1(B_59),k6_partfun1(A_58)) = k6_partfun1(k3_xboole_0(A_58,B_59)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_90,c_90,c_58])).

tff(c_60,plain,(
    ! [A_60,B_62] :
      ( v2_funct_1(A_60)
      | k6_relat_1(k1_relat_1(A_60)) != k5_relat_1(A_60,B_62)
      | ~ v1_funct_1(B_62)
      | ~ v1_relat_1(B_62)
      | ~ v1_funct_1(A_60)
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_863,plain,(
    ! [A_223,B_224] :
      ( v2_funct_1(A_223)
      | k6_partfun1(k1_relat_1(A_223)) != k5_relat_1(A_223,B_224)
      | ~ v1_funct_1(B_224)
      | ~ v1_relat_1(B_224)
      | ~ v1_funct_1(A_223)
      | ~ v1_relat_1(A_223) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_60])).

tff(c_865,plain,(
    ! [B_59,A_58] :
      ( v2_funct_1(k6_partfun1(B_59))
      | k6_partfun1(k3_xboole_0(A_58,B_59)) != k6_partfun1(k1_relat_1(k6_partfun1(B_59)))
      | ~ v1_funct_1(k6_partfun1(A_58))
      | ~ v1_relat_1(k6_partfun1(A_58))
      | ~ v1_funct_1(k6_partfun1(B_59))
      | ~ v1_relat_1(k6_partfun1(B_59)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_863])).

tff(c_872,plain,(
    ! [B_225,A_226] :
      ( v2_funct_1(k6_partfun1(B_225))
      | k6_partfun1(k3_xboole_0(A_226,B_225)) != k6_partfun1(B_225) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_116,c_117,c_116,c_119,c_865])).

tff(c_875,plain,(
    ! [A_1] : v2_funct_1(k6_partfun1(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_872])).

tff(c_1501,plain,(
    ! [A_308,D_307,E_312,C_311,B_309,F_310] :
      ( m1_subset_1(k1_partfun1(A_308,B_309,C_311,D_307,E_312,F_310),k1_zfmisc_1(k2_zfmisc_1(A_308,D_307)))
      | ~ m1_subset_1(F_310,k1_zfmisc_1(k2_zfmisc_1(C_311,D_307)))
      | ~ v1_funct_1(F_310)
      | ~ m1_subset_1(E_312,k1_zfmisc_1(k2_zfmisc_1(A_308,B_309)))
      | ~ v1_funct_1(E_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_70,plain,(
    ! [A_73] : m1_subset_1(k6_relat_1(A_73),k1_zfmisc_1(k2_zfmisc_1(A_73,A_73))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_113,plain,(
    ! [A_73] : m1_subset_1(k6_partfun1(A_73),k1_zfmisc_1(k2_zfmisc_1(A_73,A_73))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_70])).

tff(c_98,plain,(
    r2_relset_1('#skF_5','#skF_5',k1_partfun1('#skF_5','#skF_6','#skF_6','#skF_5','#skF_7','#skF_8'),k6_partfun1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_1119,plain,(
    ! [D_258,C_259,A_260,B_261] :
      ( D_258 = C_259
      | ~ r2_relset_1(A_260,B_261,C_259,D_258)
      | ~ m1_subset_1(D_258,k1_zfmisc_1(k2_zfmisc_1(A_260,B_261)))
      | ~ m1_subset_1(C_259,k1_zfmisc_1(k2_zfmisc_1(A_260,B_261))) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1131,plain,
    ( k1_partfun1('#skF_5','#skF_6','#skF_6','#skF_5','#skF_7','#skF_8') = k6_partfun1('#skF_5')
    | ~ m1_subset_1(k6_partfun1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5')))
    | ~ m1_subset_1(k1_partfun1('#skF_5','#skF_6','#skF_6','#skF_5','#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_98,c_1119])).

tff(c_1154,plain,
    ( k1_partfun1('#skF_5','#skF_6','#skF_6','#skF_5','#skF_7','#skF_8') = k6_partfun1('#skF_5')
    | ~ m1_subset_1(k1_partfun1('#skF_5','#skF_6','#skF_6','#skF_5','#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_1131])).

tff(c_1171,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_5','#skF_6','#skF_6','#skF_5','#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_1154])).

tff(c_1517,plain,
    ( ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5')))
    | ~ v1_funct_1('#skF_8')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_1501,c_1171])).

tff(c_1566,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_108,c_104,c_100,c_1517])).

tff(c_1567,plain,(
    k1_partfun1('#skF_5','#skF_6','#skF_6','#skF_5','#skF_7','#skF_8') = k6_partfun1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1154])).

tff(c_2149,plain,(
    ! [B_368,A_372,E_371,C_370,D_369] :
      ( k1_xboole_0 = C_370
      | v2_funct_1(D_369)
      | ~ v2_funct_1(k1_partfun1(A_372,B_368,B_368,C_370,D_369,E_371))
      | ~ m1_subset_1(E_371,k1_zfmisc_1(k2_zfmisc_1(B_368,C_370)))
      | ~ v1_funct_2(E_371,B_368,C_370)
      | ~ v1_funct_1(E_371)
      | ~ m1_subset_1(D_369,k1_zfmisc_1(k2_zfmisc_1(A_372,B_368)))
      | ~ v1_funct_2(D_369,A_372,B_368)
      | ~ v1_funct_1(D_369) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_2153,plain,
    ( k1_xboole_0 = '#skF_5'
    | v2_funct_1('#skF_7')
    | ~ v2_funct_1(k6_partfun1('#skF_5'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5')))
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_5')
    | ~ v1_funct_1('#skF_8')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1567,c_2149])).

tff(c_2158,plain,
    ( k1_xboole_0 = '#skF_5'
    | v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_110,c_108,c_104,c_102,c_100,c_875,c_2153])).

tff(c_2160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_999,c_2158])).

tff(c_2162,plain,(
    k2_relat_1('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_344])).

tff(c_2319,plain,(
    ! [A_409] :
      ( r2_hidden('#skF_3'(A_409),k2_relat_1(A_409))
      | v2_funct_1(A_409)
      | ~ v1_funct_1(A_409)
      | ~ v1_relat_1(A_409) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2327,plain,
    ( r2_hidden('#skF_3'('#skF_7'),k1_xboole_0)
    | v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2162,c_2319])).

tff(c_2334,plain,
    ( r2_hidden('#skF_3'('#skF_7'),k1_xboole_0)
    | v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_112,c_2327])).

tff(c_2336,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_2244,c_2334])).

tff(c_2337,plain,(
    ! [A_33] : ~ v1_xboole_0(A_33) ),
    inference(splitRight,[status(thm)],[c_2239])).

tff(c_128,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_24])).

tff(c_2361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2337,c_128])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:48:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.30/1.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.30/1.88  
% 5.30/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.30/1.88  %$ r2_relset_1 > v1_funct_2 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k1_partfun1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_4
% 5.30/1.88  
% 5.30/1.88  %Foreground sorts:
% 5.30/1.88  
% 5.30/1.88  
% 5.30/1.88  %Background operators:
% 5.30/1.88  
% 5.30/1.88  
% 5.30/1.88  %Foreground operators:
% 5.30/1.88  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.30/1.88  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.30/1.88  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.30/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.30/1.88  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.30/1.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.30/1.88  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 5.30/1.88  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.30/1.88  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.30/1.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.30/1.88  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.30/1.88  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.30/1.88  tff('#skF_7', type, '#skF_7': $i).
% 5.30/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.30/1.88  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.30/1.88  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.30/1.88  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.30/1.88  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.30/1.88  tff('#skF_5', type, '#skF_5': $i).
% 5.30/1.88  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.30/1.88  tff('#skF_6', type, '#skF_6': $i).
% 5.30/1.88  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.30/1.88  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.30/1.88  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.30/1.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.30/1.88  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.30/1.88  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.30/1.88  tff('#skF_8', type, '#skF_8': $i).
% 5.30/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.30/1.88  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.30/1.88  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.30/1.88  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.30/1.88  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.30/1.88  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.30/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.30/1.88  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.30/1.88  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.30/1.88  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.30/1.88  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.30/1.88  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.30/1.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.30/1.88  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.30/1.88  
% 5.30/1.90  tff(f_222, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~((~(B = k1_xboole_0) & (?[D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))))) & ~v2_funct_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_funct_2)).
% 5.30/1.90  tff(f_55, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_subset_1)).
% 5.30/1.90  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.30/1.90  tff(f_74, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 5.30/1.90  tff(f_121, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.30/1.90  tff(f_125, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.30/1.90  tff(f_153, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.30/1.90  tff(f_80, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 5.30/1.90  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.30/1.90  tff(f_177, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.30/1.90  tff(f_88, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 5.30/1.90  tff(f_84, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 5.30/1.90  tff(f_104, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 5.30/1.90  tff(f_117, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((?[B]: ((v1_relat_1(B) & v1_funct_1(B)) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A))))) => v2_funct_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_funct_1)).
% 5.30/1.90  tff(f_165, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.30/1.90  tff(f_135, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 5.30/1.90  tff(f_133, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.30/1.90  tff(f_199, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 5.30/1.90  tff(f_102, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((![B]: ~(r2_hidden(B, k2_relat_1(A)) & (![C]: ~(k10_relat_1(A, k1_tarski(B)) = k1_tarski(C))))) <=> v2_funct_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_funct_1)).
% 5.30/1.90  tff(c_96, plain, (~v2_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_222])).
% 5.30/1.90  tff(c_24, plain, (![A_33]: (v1_xboole_0('#skF_1'(A_33)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.30/1.90  tff(c_123, plain, (![A_100]: (k1_xboole_0=A_100 | ~v1_xboole_0(A_100))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.30/1.90  tff(c_127, plain, (![A_33]: ('#skF_1'(A_33)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_123])).
% 5.30/1.90  tff(c_26, plain, (![A_33]: (m1_subset_1('#skF_1'(A_33), k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.30/1.90  tff(c_186, plain, (![A_33]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_33)))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_26])).
% 5.30/1.90  tff(c_2221, plain, (![C_381, B_382, A_383]: (~v1_xboole_0(C_381) | ~m1_subset_1(B_382, k1_zfmisc_1(C_381)) | ~r2_hidden(A_383, B_382))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.30/1.90  tff(c_2239, plain, (![A_33, A_383]: (~v1_xboole_0(A_33) | ~r2_hidden(A_383, k1_xboole_0))), inference(resolution, [status(thm)], [c_186, c_2221])).
% 5.30/1.90  tff(c_2244, plain, (![A_383]: (~r2_hidden(A_383, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_2239])).
% 5.30/1.90  tff(c_108, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_222])).
% 5.30/1.90  tff(c_312, plain, (![C_127, A_128, B_129]: (v1_relat_1(C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.30/1.90  tff(c_337, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_108, c_312])).
% 5.30/1.90  tff(c_112, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_222])).
% 5.30/1.90  tff(c_106, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_222])).
% 5.30/1.90  tff(c_110, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_222])).
% 5.30/1.90  tff(c_595, plain, (![A_178, B_179, C_180]: (k1_relset_1(A_178, B_179, C_180)=k1_relat_1(C_180) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.30/1.90  tff(c_620, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_108, c_595])).
% 5.30/1.90  tff(c_927, plain, (![B_240, A_241, C_242]: (k1_xboole_0=B_240 | k1_relset_1(A_241, B_240, C_242)=A_241 | ~v1_funct_2(C_242, A_241, B_240) | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(A_241, B_240))))), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.30/1.90  tff(c_937, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_5' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_108, c_927])).
% 5.30/1.90  tff(c_954, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_620, c_937])).
% 5.30/1.90  tff(c_955, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_106, c_954])).
% 5.30/1.90  tff(c_40, plain, (![A_44]: (k1_relat_1(A_44)=k1_xboole_0 | k2_relat_1(A_44)!=k1_xboole_0 | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.30/1.90  tff(c_344, plain, (k1_relat_1('#skF_7')=k1_xboole_0 | k2_relat_1('#skF_7')!=k1_xboole_0), inference(resolution, [status(thm)], [c_337, c_40])).
% 5.30/1.90  tff(c_382, plain, (k2_relat_1('#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_344])).
% 5.30/1.90  tff(c_345, plain, (![A_130]: (k2_relat_1(A_130)=k1_xboole_0 | k1_relat_1(A_130)!=k1_xboole_0 | ~v1_relat_1(A_130))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.30/1.90  tff(c_352, plain, (k2_relat_1('#skF_7')=k1_xboole_0 | k1_relat_1('#skF_7')!=k1_xboole_0), inference(resolution, [status(thm)], [c_337, c_345])).
% 5.30/1.90  tff(c_383, plain, (k1_relat_1('#skF_7')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_382, c_352])).
% 5.30/1.90  tff(c_999, plain, (k1_xboole_0!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_955, c_383])).
% 5.30/1.90  tff(c_104, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_222])).
% 5.30/1.90  tff(c_102, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_222])).
% 5.30/1.90  tff(c_100, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_222])).
% 5.30/1.90  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.30/1.90  tff(c_90, plain, (![A_89]: (k6_relat_1(A_89)=k6_partfun1(A_89))), inference(cnfTransformation, [status(thm)], [f_177])).
% 5.30/1.90  tff(c_48, plain, (![A_46]: (v1_relat_1(k6_relat_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.30/1.90  tff(c_117, plain, (![A_46]: (v1_relat_1(k6_partfun1(A_46)))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_48])).
% 5.30/1.90  tff(c_50, plain, (![A_46]: (v1_funct_1(k6_relat_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.30/1.90  tff(c_116, plain, (![A_46]: (v1_funct_1(k6_partfun1(A_46)))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_50])).
% 5.30/1.90  tff(c_44, plain, (![A_45]: (k1_relat_1(k6_relat_1(A_45))=A_45)), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.30/1.90  tff(c_119, plain, (![A_45]: (k1_relat_1(k6_partfun1(A_45))=A_45)), inference(demodulation, [status(thm), theory('equality')], [c_90, c_44])).
% 5.30/1.90  tff(c_58, plain, (![B_59, A_58]: (k5_relat_1(k6_relat_1(B_59), k6_relat_1(A_58))=k6_relat_1(k3_xboole_0(A_58, B_59)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.30/1.90  tff(c_115, plain, (![B_59, A_58]: (k5_relat_1(k6_partfun1(B_59), k6_partfun1(A_58))=k6_partfun1(k3_xboole_0(A_58, B_59)))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_90, c_90, c_58])).
% 5.30/1.90  tff(c_60, plain, (![A_60, B_62]: (v2_funct_1(A_60) | k6_relat_1(k1_relat_1(A_60))!=k5_relat_1(A_60, B_62) | ~v1_funct_1(B_62) | ~v1_relat_1(B_62) | ~v1_funct_1(A_60) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.30/1.90  tff(c_863, plain, (![A_223, B_224]: (v2_funct_1(A_223) | k6_partfun1(k1_relat_1(A_223))!=k5_relat_1(A_223, B_224) | ~v1_funct_1(B_224) | ~v1_relat_1(B_224) | ~v1_funct_1(A_223) | ~v1_relat_1(A_223))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_60])).
% 5.30/1.90  tff(c_865, plain, (![B_59, A_58]: (v2_funct_1(k6_partfun1(B_59)) | k6_partfun1(k3_xboole_0(A_58, B_59))!=k6_partfun1(k1_relat_1(k6_partfun1(B_59))) | ~v1_funct_1(k6_partfun1(A_58)) | ~v1_relat_1(k6_partfun1(A_58)) | ~v1_funct_1(k6_partfun1(B_59)) | ~v1_relat_1(k6_partfun1(B_59)))), inference(superposition, [status(thm), theory('equality')], [c_115, c_863])).
% 5.30/1.90  tff(c_872, plain, (![B_225, A_226]: (v2_funct_1(k6_partfun1(B_225)) | k6_partfun1(k3_xboole_0(A_226, B_225))!=k6_partfun1(B_225))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_116, c_117, c_116, c_119, c_865])).
% 5.30/1.90  tff(c_875, plain, (![A_1]: (v2_funct_1(k6_partfun1(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_872])).
% 5.30/1.90  tff(c_1501, plain, (![A_308, D_307, E_312, C_311, B_309, F_310]: (m1_subset_1(k1_partfun1(A_308, B_309, C_311, D_307, E_312, F_310), k1_zfmisc_1(k2_zfmisc_1(A_308, D_307))) | ~m1_subset_1(F_310, k1_zfmisc_1(k2_zfmisc_1(C_311, D_307))) | ~v1_funct_1(F_310) | ~m1_subset_1(E_312, k1_zfmisc_1(k2_zfmisc_1(A_308, B_309))) | ~v1_funct_1(E_312))), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.30/1.90  tff(c_70, plain, (![A_73]: (m1_subset_1(k6_relat_1(A_73), k1_zfmisc_1(k2_zfmisc_1(A_73, A_73))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.30/1.90  tff(c_113, plain, (![A_73]: (m1_subset_1(k6_partfun1(A_73), k1_zfmisc_1(k2_zfmisc_1(A_73, A_73))))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_70])).
% 5.30/1.90  tff(c_98, plain, (r2_relset_1('#skF_5', '#skF_5', k1_partfun1('#skF_5', '#skF_6', '#skF_6', '#skF_5', '#skF_7', '#skF_8'), k6_partfun1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_222])).
% 5.30/1.90  tff(c_1119, plain, (![D_258, C_259, A_260, B_261]: (D_258=C_259 | ~r2_relset_1(A_260, B_261, C_259, D_258) | ~m1_subset_1(D_258, k1_zfmisc_1(k2_zfmisc_1(A_260, B_261))) | ~m1_subset_1(C_259, k1_zfmisc_1(k2_zfmisc_1(A_260, B_261))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.30/1.90  tff(c_1131, plain, (k1_partfun1('#skF_5', '#skF_6', '#skF_6', '#skF_5', '#skF_7', '#skF_8')=k6_partfun1('#skF_5') | ~m1_subset_1(k6_partfun1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5'))) | ~m1_subset_1(k1_partfun1('#skF_5', '#skF_6', '#skF_6', '#skF_5', '#skF_7', '#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5')))), inference(resolution, [status(thm)], [c_98, c_1119])).
% 5.30/1.90  tff(c_1154, plain, (k1_partfun1('#skF_5', '#skF_6', '#skF_6', '#skF_5', '#skF_7', '#skF_8')=k6_partfun1('#skF_5') | ~m1_subset_1(k1_partfun1('#skF_5', '#skF_6', '#skF_6', '#skF_5', '#skF_7', '#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_1131])).
% 5.30/1.90  tff(c_1171, plain, (~m1_subset_1(k1_partfun1('#skF_5', '#skF_6', '#skF_6', '#skF_5', '#skF_7', '#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5')))), inference(splitLeft, [status(thm)], [c_1154])).
% 5.30/1.90  tff(c_1517, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5'))) | ~v1_funct_1('#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_1501, c_1171])).
% 5.30/1.90  tff(c_1566, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_108, c_104, c_100, c_1517])).
% 5.30/1.90  tff(c_1567, plain, (k1_partfun1('#skF_5', '#skF_6', '#skF_6', '#skF_5', '#skF_7', '#skF_8')=k6_partfun1('#skF_5')), inference(splitRight, [status(thm)], [c_1154])).
% 5.30/1.90  tff(c_2149, plain, (![B_368, A_372, E_371, C_370, D_369]: (k1_xboole_0=C_370 | v2_funct_1(D_369) | ~v2_funct_1(k1_partfun1(A_372, B_368, B_368, C_370, D_369, E_371)) | ~m1_subset_1(E_371, k1_zfmisc_1(k2_zfmisc_1(B_368, C_370))) | ~v1_funct_2(E_371, B_368, C_370) | ~v1_funct_1(E_371) | ~m1_subset_1(D_369, k1_zfmisc_1(k2_zfmisc_1(A_372, B_368))) | ~v1_funct_2(D_369, A_372, B_368) | ~v1_funct_1(D_369))), inference(cnfTransformation, [status(thm)], [f_199])).
% 5.30/1.90  tff(c_2153, plain, (k1_xboole_0='#skF_5' | v2_funct_1('#skF_7') | ~v2_funct_1(k6_partfun1('#skF_5')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5'))) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_5') | ~v1_funct_1('#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6') | ~v1_funct_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1567, c_2149])).
% 5.30/1.90  tff(c_2158, plain, (k1_xboole_0='#skF_5' | v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_110, c_108, c_104, c_102, c_100, c_875, c_2153])).
% 5.30/1.90  tff(c_2160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_999, c_2158])).
% 5.30/1.90  tff(c_2162, plain, (k2_relat_1('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_344])).
% 5.30/1.90  tff(c_2319, plain, (![A_409]: (r2_hidden('#skF_3'(A_409), k2_relat_1(A_409)) | v2_funct_1(A_409) | ~v1_funct_1(A_409) | ~v1_relat_1(A_409))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.30/1.90  tff(c_2327, plain, (r2_hidden('#skF_3'('#skF_7'), k1_xboole_0) | v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2162, c_2319])).
% 5.30/1.90  tff(c_2334, plain, (r2_hidden('#skF_3'('#skF_7'), k1_xboole_0) | v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_337, c_112, c_2327])).
% 5.30/1.90  tff(c_2336, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_2244, c_2334])).
% 5.30/1.90  tff(c_2337, plain, (![A_33]: (~v1_xboole_0(A_33))), inference(splitRight, [status(thm)], [c_2239])).
% 5.30/1.90  tff(c_128, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_127, c_24])).
% 5.30/1.90  tff(c_2361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2337, c_128])).
% 5.30/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.30/1.90  
% 5.30/1.90  Inference rules
% 5.30/1.90  ----------------------
% 5.30/1.90  #Ref     : 0
% 5.30/1.90  #Sup     : 454
% 5.30/1.90  #Fact    : 0
% 5.30/1.90  #Define  : 0
% 5.30/1.90  #Split   : 14
% 5.30/1.90  #Chain   : 0
% 5.30/1.90  #Close   : 0
% 5.30/1.90  
% 5.30/1.90  Ordering : KBO
% 5.30/1.90  
% 5.30/1.90  Simplification rules
% 5.30/1.90  ----------------------
% 5.30/1.90  #Subsume      : 49
% 5.30/1.90  #Demod        : 282
% 5.30/1.90  #Tautology    : 184
% 5.30/1.90  #SimpNegUnit  : 31
% 5.30/1.90  #BackRed      : 13
% 5.30/1.90  
% 5.30/1.90  #Partial instantiations: 0
% 5.30/1.90  #Strategies tried      : 1
% 5.30/1.90  
% 5.30/1.90  Timing (in seconds)
% 5.30/1.90  ----------------------
% 5.30/1.90  Preprocessing        : 0.40
% 5.30/1.90  Parsing              : 0.20
% 5.30/1.90  CNF conversion       : 0.03
% 5.30/1.90  Main loop            : 0.71
% 5.30/1.90  Inferencing          : 0.26
% 5.30/1.90  Reduction            : 0.25
% 5.30/1.90  Demodulation         : 0.17
% 5.30/1.90  BG Simplification    : 0.03
% 5.30/1.90  Subsumption          : 0.12
% 5.30/1.90  Abstraction          : 0.03
% 5.30/1.90  MUC search           : 0.00
% 5.30/1.90  Cooper               : 0.00
% 5.30/1.90  Total                : 1.15
% 5.30/1.90  Index Insertion      : 0.00
% 5.30/1.90  Index Deletion       : 0.00
% 5.30/1.90  Index Matching       : 0.00
% 5.30/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
