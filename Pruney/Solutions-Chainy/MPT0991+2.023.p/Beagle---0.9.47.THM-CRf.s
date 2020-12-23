%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:29 EST 2020

% Result     : Theorem 4.91s
% Output     : CNFRefutation 4.91s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 218 expanded)
%              Number of leaves         :   62 ( 107 expanded)
%              Depth                    :    7
%              Number of atoms          :  205 ( 500 expanded)
%              Number of equality atoms :   57 ( 110 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_subset_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k1_partfun1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_4

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(f_224,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_funct_2)).

tff(f_55,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_125,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_151,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_179,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_84,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_104,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_117,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( ? [B] :
            ( v1_relat_1(B)
            & v1_funct_1(B)
            & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
       => v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).

tff(f_163,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_167,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_133,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_201,axiom,(
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

tff(f_102,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( ! [B] :
            ~ ( r2_hidden(B,k2_relat_1(A))
              & ! [C] : k10_relat_1(A,k1_tarski(B)) != k1_tarski(C) )
      <=> v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_funct_1)).

tff(c_98,plain,(
    ~ v2_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_24,plain,(
    ! [A_33] : v1_xboole_0('#skF_1'(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_124,plain,(
    ! [A_100] :
      ( k1_xboole_0 = A_100
      | ~ v1_xboole_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_128,plain,(
    ! [A_33] : '#skF_1'(A_33) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_124])).

tff(c_26,plain,(
    ! [A_33] : m1_subset_1('#skF_1'(A_33),k1_zfmisc_1(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_197,plain,(
    ! [A_33] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_33)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_26])).

tff(c_2256,plain,(
    ! [C_359,B_360,A_361] :
      ( ~ v1_xboole_0(C_359)
      | ~ m1_subset_1(B_360,k1_zfmisc_1(C_359))
      | ~ r2_hidden(A_361,B_360) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2274,plain,(
    ! [A_33,A_361] :
      ( ~ v1_xboole_0(A_33)
      | ~ r2_hidden(A_361,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_197,c_2256])).

tff(c_2279,plain,(
    ! [A_361] : ~ r2_hidden(A_361,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2274])).

tff(c_110,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_314,plain,(
    ! [C_128,A_129,B_130] :
      ( v1_relat_1(C_128)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_339,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_110,c_314])).

tff(c_114,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_108,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_112,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_548,plain,(
    ! [A_171,B_172,C_173] :
      ( k1_relset_1(A_171,B_172,C_173) = k1_relat_1(C_173)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_573,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_110,c_548])).

tff(c_929,plain,(
    ! [B_241,A_242,C_243] :
      ( k1_xboole_0 = B_241
      | k1_relset_1(A_242,B_241,C_243) = A_242
      | ~ v1_funct_2(C_243,A_242,B_241)
      | ~ m1_subset_1(C_243,k1_zfmisc_1(k2_zfmisc_1(A_242,B_241))) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_939,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_110,c_929])).

tff(c_956,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_573,c_939])).

tff(c_957,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_956])).

tff(c_42,plain,(
    ! [A_44] :
      ( k2_relat_1(A_44) = k1_xboole_0
      | k1_relat_1(A_44) != k1_xboole_0
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_355,plain,
    ( k2_relat_1('#skF_7') = k1_xboole_0
    | k1_relat_1('#skF_7') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_339,c_42])).

tff(c_384,plain,(
    k1_relat_1('#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_355])).

tff(c_966,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_957,c_384])).

tff(c_106,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_104,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_102,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_92,plain,(
    ! [A_89] : k6_relat_1(A_89) = k6_partfun1(A_89) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_48,plain,(
    ! [A_46] : v1_relat_1(k6_relat_1(A_46)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_118,plain,(
    ! [A_46] : v1_relat_1(k6_partfun1(A_46)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_48])).

tff(c_50,plain,(
    ! [A_46] : v1_funct_1(k6_relat_1(A_46)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_117,plain,(
    ! [A_46] : v1_funct_1(k6_partfun1(A_46)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_50])).

tff(c_44,plain,(
    ! [A_45] : k1_relat_1(k6_relat_1(A_45)) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_120,plain,(
    ! [A_45] : k1_relat_1(k6_partfun1(A_45)) = A_45 ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_44])).

tff(c_58,plain,(
    ! [B_59,A_58] : k5_relat_1(k6_relat_1(B_59),k6_relat_1(A_58)) = k6_relat_1(k3_xboole_0(A_58,B_59)) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_116,plain,(
    ! [B_59,A_58] : k5_relat_1(k6_partfun1(B_59),k6_partfun1(A_58)) = k6_partfun1(k3_xboole_0(A_58,B_59)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_92,c_92,c_58])).

tff(c_60,plain,(
    ! [A_60,B_62] :
      ( v2_funct_1(A_60)
      | k6_relat_1(k1_relat_1(A_60)) != k5_relat_1(A_60,B_62)
      | ~ v1_funct_1(B_62)
      | ~ v1_relat_1(B_62)
      | ~ v1_funct_1(A_60)
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_864,plain,(
    ! [A_223,B_224] :
      ( v2_funct_1(A_223)
      | k6_partfun1(k1_relat_1(A_223)) != k5_relat_1(A_223,B_224)
      | ~ v1_funct_1(B_224)
      | ~ v1_relat_1(B_224)
      | ~ v1_funct_1(A_223)
      | ~ v1_relat_1(A_223) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_60])).

tff(c_866,plain,(
    ! [B_59,A_58] :
      ( v2_funct_1(k6_partfun1(B_59))
      | k6_partfun1(k3_xboole_0(A_58,B_59)) != k6_partfun1(k1_relat_1(k6_partfun1(B_59)))
      | ~ v1_funct_1(k6_partfun1(A_58))
      | ~ v1_relat_1(k6_partfun1(A_58))
      | ~ v1_funct_1(k6_partfun1(B_59))
      | ~ v1_relat_1(k6_partfun1(B_59)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_864])).

tff(c_880,plain,(
    ! [B_226,A_227] :
      ( v2_funct_1(k6_partfun1(B_226))
      | k6_partfun1(k3_xboole_0(A_227,B_226)) != k6_partfun1(B_226) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_117,c_118,c_117,c_120,c_866])).

tff(c_883,plain,(
    ! [A_1] : v2_funct_1(k6_partfun1(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_880])).

tff(c_1467,plain,(
    ! [E_305,A_307,D_309,F_306,B_304,C_308] :
      ( m1_subset_1(k1_partfun1(A_307,B_304,C_308,D_309,E_305,F_306),k1_zfmisc_1(k2_zfmisc_1(A_307,D_309)))
      | ~ m1_subset_1(F_306,k1_zfmisc_1(k2_zfmisc_1(C_308,D_309)))
      | ~ v1_funct_1(F_306)
      | ~ m1_subset_1(E_305,k1_zfmisc_1(k2_zfmisc_1(A_307,B_304)))
      | ~ v1_funct_1(E_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_88,plain,(
    ! [A_82] : m1_subset_1(k6_partfun1(A_82),k1_zfmisc_1(k2_zfmisc_1(A_82,A_82))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_100,plain,(
    r2_relset_1('#skF_5','#skF_5',k1_partfun1('#skF_5','#skF_6','#skF_6','#skF_5','#skF_7','#skF_8'),k6_partfun1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_1227,plain,(
    ! [D_274,C_275,A_276,B_277] :
      ( D_274 = C_275
      | ~ r2_relset_1(A_276,B_277,C_275,D_274)
      | ~ m1_subset_1(D_274,k1_zfmisc_1(k2_zfmisc_1(A_276,B_277)))
      | ~ m1_subset_1(C_275,k1_zfmisc_1(k2_zfmisc_1(A_276,B_277))) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1239,plain,
    ( k1_partfun1('#skF_5','#skF_6','#skF_6','#skF_5','#skF_7','#skF_8') = k6_partfun1('#skF_5')
    | ~ m1_subset_1(k6_partfun1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5')))
    | ~ m1_subset_1(k1_partfun1('#skF_5','#skF_6','#skF_6','#skF_5','#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_100,c_1227])).

tff(c_1262,plain,
    ( k1_partfun1('#skF_5','#skF_6','#skF_6','#skF_5','#skF_7','#skF_8') = k6_partfun1('#skF_5')
    | ~ m1_subset_1(k1_partfun1('#skF_5','#skF_6','#skF_6','#skF_5','#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1239])).

tff(c_1263,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_5','#skF_6','#skF_6','#skF_5','#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_1262])).

tff(c_1483,plain,
    ( ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5')))
    | ~ v1_funct_1('#skF_8')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_1467,c_1263])).

tff(c_1529,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_110,c_106,c_102,c_1483])).

tff(c_1530,plain,(
    k1_partfun1('#skF_5','#skF_6','#skF_6','#skF_5','#skF_7','#skF_8') = k6_partfun1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1262])).

tff(c_2226,plain,(
    ! [C_356,A_358,E_357,D_355,B_354] :
      ( k1_xboole_0 = C_356
      | v2_funct_1(D_355)
      | ~ v2_funct_1(k1_partfun1(A_358,B_354,B_354,C_356,D_355,E_357))
      | ~ m1_subset_1(E_357,k1_zfmisc_1(k2_zfmisc_1(B_354,C_356)))
      | ~ v1_funct_2(E_357,B_354,C_356)
      | ~ v1_funct_1(E_357)
      | ~ m1_subset_1(D_355,k1_zfmisc_1(k2_zfmisc_1(A_358,B_354)))
      | ~ v1_funct_2(D_355,A_358,B_354)
      | ~ v1_funct_1(D_355) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_2233,plain,
    ( k1_xboole_0 = '#skF_5'
    | v2_funct_1('#skF_7')
    | ~ v2_funct_1(k6_partfun1('#skF_5'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5')))
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_5')
    | ~ v1_funct_1('#skF_8')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1530,c_2226])).

tff(c_2241,plain,
    ( k1_xboole_0 = '#skF_5'
    | v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_112,c_110,c_106,c_104,c_102,c_883,c_2233])).

tff(c_2243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_966,c_2241])).

tff(c_2244,plain,(
    k2_relat_1('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_355])).

tff(c_2402,plain,(
    ! [A_395] :
      ( r2_hidden('#skF_3'(A_395),k2_relat_1(A_395))
      | v2_funct_1(A_395)
      | ~ v1_funct_1(A_395)
      | ~ v1_relat_1(A_395) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2410,plain,
    ( r2_hidden('#skF_3'('#skF_7'),k1_xboole_0)
    | v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2244,c_2402])).

tff(c_2417,plain,
    ( r2_hidden('#skF_3'('#skF_7'),k1_xboole_0)
    | v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_114,c_2410])).

tff(c_2419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_2279,c_2417])).

tff(c_2420,plain,(
    ! [A_33] : ~ v1_xboole_0(A_33) ),
    inference(splitRight,[status(thm)],[c_2274])).

tff(c_129,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_24])).

tff(c_2431,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2420,c_129])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n018.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 15:32:27 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.91/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.91/1.85  
% 4.91/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.91/1.85  %$ r2_relset_1 > v1_funct_2 > v1_subset_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k1_partfun1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_4
% 4.91/1.85  
% 4.91/1.85  %Foreground sorts:
% 4.91/1.85  
% 4.91/1.85  
% 4.91/1.85  %Background operators:
% 4.91/1.85  
% 4.91/1.85  
% 4.91/1.85  %Foreground operators:
% 4.91/1.85  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.91/1.85  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.91/1.85  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.91/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.91/1.85  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.91/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.91/1.85  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.91/1.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.91/1.85  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.91/1.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.91/1.85  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.91/1.85  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.91/1.85  tff('#skF_7', type, '#skF_7': $i).
% 4.91/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.91/1.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.91/1.85  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.91/1.85  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.91/1.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.91/1.85  tff('#skF_5', type, '#skF_5': $i).
% 4.91/1.85  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.91/1.85  tff('#skF_6', type, '#skF_6': $i).
% 4.91/1.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.91/1.85  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.91/1.85  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.91/1.85  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.91/1.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.91/1.85  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.91/1.85  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.91/1.85  tff('#skF_8', type, '#skF_8': $i).
% 4.91/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.91/1.85  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.91/1.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.91/1.85  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.91/1.85  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.91/1.85  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.91/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.91/1.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.91/1.85  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.91/1.85  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.91/1.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.91/1.85  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.91/1.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.91/1.85  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.91/1.85  
% 4.91/1.87  tff(f_224, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~((~(B = k1_xboole_0) & (?[D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))))) & ~v2_funct_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_funct_2)).
% 4.91/1.87  tff(f_55, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_subset_1)).
% 4.91/1.87  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.91/1.87  tff(f_74, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 4.91/1.87  tff(f_121, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.91/1.87  tff(f_125, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.91/1.87  tff(f_151, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.91/1.87  tff(f_80, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 4.91/1.87  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.91/1.87  tff(f_179, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.91/1.87  tff(f_88, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 4.91/1.87  tff(f_84, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 4.91/1.87  tff(f_104, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 4.91/1.87  tff(f_117, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((?[B]: ((v1_relat_1(B) & v1_funct_1(B)) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A))))) => v2_funct_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_funct_1)).
% 4.91/1.87  tff(f_163, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.91/1.87  tff(f_167, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.91/1.87  tff(f_133, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.91/1.87  tff(f_201, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 4.91/1.87  tff(f_102, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((![B]: ~(r2_hidden(B, k2_relat_1(A)) & (![C]: ~(k10_relat_1(A, k1_tarski(B)) = k1_tarski(C))))) <=> v2_funct_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_funct_1)).
% 4.91/1.87  tff(c_98, plain, (~v2_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.91/1.87  tff(c_24, plain, (![A_33]: (v1_xboole_0('#skF_1'(A_33)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.91/1.87  tff(c_124, plain, (![A_100]: (k1_xboole_0=A_100 | ~v1_xboole_0(A_100))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.91/1.87  tff(c_128, plain, (![A_33]: ('#skF_1'(A_33)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_124])).
% 4.91/1.87  tff(c_26, plain, (![A_33]: (m1_subset_1('#skF_1'(A_33), k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.91/1.87  tff(c_197, plain, (![A_33]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_33)))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_26])).
% 4.91/1.87  tff(c_2256, plain, (![C_359, B_360, A_361]: (~v1_xboole_0(C_359) | ~m1_subset_1(B_360, k1_zfmisc_1(C_359)) | ~r2_hidden(A_361, B_360))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.91/1.87  tff(c_2274, plain, (![A_33, A_361]: (~v1_xboole_0(A_33) | ~r2_hidden(A_361, k1_xboole_0))), inference(resolution, [status(thm)], [c_197, c_2256])).
% 4.91/1.87  tff(c_2279, plain, (![A_361]: (~r2_hidden(A_361, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_2274])).
% 4.91/1.87  tff(c_110, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.91/1.87  tff(c_314, plain, (![C_128, A_129, B_130]: (v1_relat_1(C_128) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.91/1.87  tff(c_339, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_110, c_314])).
% 4.91/1.87  tff(c_114, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.91/1.87  tff(c_108, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.91/1.87  tff(c_112, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.91/1.87  tff(c_548, plain, (![A_171, B_172, C_173]: (k1_relset_1(A_171, B_172, C_173)=k1_relat_1(C_173) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.91/1.87  tff(c_573, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_110, c_548])).
% 4.91/1.87  tff(c_929, plain, (![B_241, A_242, C_243]: (k1_xboole_0=B_241 | k1_relset_1(A_242, B_241, C_243)=A_242 | ~v1_funct_2(C_243, A_242, B_241) | ~m1_subset_1(C_243, k1_zfmisc_1(k2_zfmisc_1(A_242, B_241))))), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.91/1.87  tff(c_939, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_5' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_110, c_929])).
% 4.91/1.87  tff(c_956, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_573, c_939])).
% 4.91/1.87  tff(c_957, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_108, c_956])).
% 4.91/1.87  tff(c_42, plain, (![A_44]: (k2_relat_1(A_44)=k1_xboole_0 | k1_relat_1(A_44)!=k1_xboole_0 | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.91/1.87  tff(c_355, plain, (k2_relat_1('#skF_7')=k1_xboole_0 | k1_relat_1('#skF_7')!=k1_xboole_0), inference(resolution, [status(thm)], [c_339, c_42])).
% 4.91/1.87  tff(c_384, plain, (k1_relat_1('#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_355])).
% 4.91/1.87  tff(c_966, plain, (k1_xboole_0!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_957, c_384])).
% 4.91/1.87  tff(c_106, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.91/1.87  tff(c_104, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.91/1.87  tff(c_102, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.91/1.87  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.91/1.87  tff(c_92, plain, (![A_89]: (k6_relat_1(A_89)=k6_partfun1(A_89))), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.91/1.87  tff(c_48, plain, (![A_46]: (v1_relat_1(k6_relat_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.91/1.87  tff(c_118, plain, (![A_46]: (v1_relat_1(k6_partfun1(A_46)))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_48])).
% 4.91/1.87  tff(c_50, plain, (![A_46]: (v1_funct_1(k6_relat_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.91/1.87  tff(c_117, plain, (![A_46]: (v1_funct_1(k6_partfun1(A_46)))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_50])).
% 4.91/1.87  tff(c_44, plain, (![A_45]: (k1_relat_1(k6_relat_1(A_45))=A_45)), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.91/1.87  tff(c_120, plain, (![A_45]: (k1_relat_1(k6_partfun1(A_45))=A_45)), inference(demodulation, [status(thm), theory('equality')], [c_92, c_44])).
% 4.91/1.87  tff(c_58, plain, (![B_59, A_58]: (k5_relat_1(k6_relat_1(B_59), k6_relat_1(A_58))=k6_relat_1(k3_xboole_0(A_58, B_59)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.91/1.87  tff(c_116, plain, (![B_59, A_58]: (k5_relat_1(k6_partfun1(B_59), k6_partfun1(A_58))=k6_partfun1(k3_xboole_0(A_58, B_59)))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_92, c_92, c_58])).
% 4.91/1.87  tff(c_60, plain, (![A_60, B_62]: (v2_funct_1(A_60) | k6_relat_1(k1_relat_1(A_60))!=k5_relat_1(A_60, B_62) | ~v1_funct_1(B_62) | ~v1_relat_1(B_62) | ~v1_funct_1(A_60) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.91/1.87  tff(c_864, plain, (![A_223, B_224]: (v2_funct_1(A_223) | k6_partfun1(k1_relat_1(A_223))!=k5_relat_1(A_223, B_224) | ~v1_funct_1(B_224) | ~v1_relat_1(B_224) | ~v1_funct_1(A_223) | ~v1_relat_1(A_223))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_60])).
% 4.91/1.87  tff(c_866, plain, (![B_59, A_58]: (v2_funct_1(k6_partfun1(B_59)) | k6_partfun1(k3_xboole_0(A_58, B_59))!=k6_partfun1(k1_relat_1(k6_partfun1(B_59))) | ~v1_funct_1(k6_partfun1(A_58)) | ~v1_relat_1(k6_partfun1(A_58)) | ~v1_funct_1(k6_partfun1(B_59)) | ~v1_relat_1(k6_partfun1(B_59)))), inference(superposition, [status(thm), theory('equality')], [c_116, c_864])).
% 4.91/1.87  tff(c_880, plain, (![B_226, A_227]: (v2_funct_1(k6_partfun1(B_226)) | k6_partfun1(k3_xboole_0(A_227, B_226))!=k6_partfun1(B_226))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_117, c_118, c_117, c_120, c_866])).
% 4.91/1.87  tff(c_883, plain, (![A_1]: (v2_funct_1(k6_partfun1(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_880])).
% 4.91/1.87  tff(c_1467, plain, (![E_305, A_307, D_309, F_306, B_304, C_308]: (m1_subset_1(k1_partfun1(A_307, B_304, C_308, D_309, E_305, F_306), k1_zfmisc_1(k2_zfmisc_1(A_307, D_309))) | ~m1_subset_1(F_306, k1_zfmisc_1(k2_zfmisc_1(C_308, D_309))) | ~v1_funct_1(F_306) | ~m1_subset_1(E_305, k1_zfmisc_1(k2_zfmisc_1(A_307, B_304))) | ~v1_funct_1(E_305))), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.91/1.87  tff(c_88, plain, (![A_82]: (m1_subset_1(k6_partfun1(A_82), k1_zfmisc_1(k2_zfmisc_1(A_82, A_82))))), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.91/1.87  tff(c_100, plain, (r2_relset_1('#skF_5', '#skF_5', k1_partfun1('#skF_5', '#skF_6', '#skF_6', '#skF_5', '#skF_7', '#skF_8'), k6_partfun1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.91/1.87  tff(c_1227, plain, (![D_274, C_275, A_276, B_277]: (D_274=C_275 | ~r2_relset_1(A_276, B_277, C_275, D_274) | ~m1_subset_1(D_274, k1_zfmisc_1(k2_zfmisc_1(A_276, B_277))) | ~m1_subset_1(C_275, k1_zfmisc_1(k2_zfmisc_1(A_276, B_277))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.91/1.87  tff(c_1239, plain, (k1_partfun1('#skF_5', '#skF_6', '#skF_6', '#skF_5', '#skF_7', '#skF_8')=k6_partfun1('#skF_5') | ~m1_subset_1(k6_partfun1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5'))) | ~m1_subset_1(k1_partfun1('#skF_5', '#skF_6', '#skF_6', '#skF_5', '#skF_7', '#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5')))), inference(resolution, [status(thm)], [c_100, c_1227])).
% 4.91/1.87  tff(c_1262, plain, (k1_partfun1('#skF_5', '#skF_6', '#skF_6', '#skF_5', '#skF_7', '#skF_8')=k6_partfun1('#skF_5') | ~m1_subset_1(k1_partfun1('#skF_5', '#skF_6', '#skF_6', '#skF_5', '#skF_7', '#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1239])).
% 4.91/1.87  tff(c_1263, plain, (~m1_subset_1(k1_partfun1('#skF_5', '#skF_6', '#skF_6', '#skF_5', '#skF_7', '#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5')))), inference(splitLeft, [status(thm)], [c_1262])).
% 4.91/1.87  tff(c_1483, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5'))) | ~v1_funct_1('#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_1467, c_1263])).
% 4.91/1.87  tff(c_1529, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114, c_110, c_106, c_102, c_1483])).
% 4.91/1.87  tff(c_1530, plain, (k1_partfun1('#skF_5', '#skF_6', '#skF_6', '#skF_5', '#skF_7', '#skF_8')=k6_partfun1('#skF_5')), inference(splitRight, [status(thm)], [c_1262])).
% 4.91/1.87  tff(c_2226, plain, (![C_356, A_358, E_357, D_355, B_354]: (k1_xboole_0=C_356 | v2_funct_1(D_355) | ~v2_funct_1(k1_partfun1(A_358, B_354, B_354, C_356, D_355, E_357)) | ~m1_subset_1(E_357, k1_zfmisc_1(k2_zfmisc_1(B_354, C_356))) | ~v1_funct_2(E_357, B_354, C_356) | ~v1_funct_1(E_357) | ~m1_subset_1(D_355, k1_zfmisc_1(k2_zfmisc_1(A_358, B_354))) | ~v1_funct_2(D_355, A_358, B_354) | ~v1_funct_1(D_355))), inference(cnfTransformation, [status(thm)], [f_201])).
% 4.91/1.87  tff(c_2233, plain, (k1_xboole_0='#skF_5' | v2_funct_1('#skF_7') | ~v2_funct_1(k6_partfun1('#skF_5')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5'))) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_5') | ~v1_funct_1('#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6') | ~v1_funct_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1530, c_2226])).
% 4.91/1.87  tff(c_2241, plain, (k1_xboole_0='#skF_5' | v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_112, c_110, c_106, c_104, c_102, c_883, c_2233])).
% 4.91/1.87  tff(c_2243, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_966, c_2241])).
% 4.91/1.87  tff(c_2244, plain, (k2_relat_1('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_355])).
% 4.91/1.87  tff(c_2402, plain, (![A_395]: (r2_hidden('#skF_3'(A_395), k2_relat_1(A_395)) | v2_funct_1(A_395) | ~v1_funct_1(A_395) | ~v1_relat_1(A_395))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.91/1.87  tff(c_2410, plain, (r2_hidden('#skF_3'('#skF_7'), k1_xboole_0) | v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2244, c_2402])).
% 4.91/1.87  tff(c_2417, plain, (r2_hidden('#skF_3'('#skF_7'), k1_xboole_0) | v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_339, c_114, c_2410])).
% 4.91/1.87  tff(c_2419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_2279, c_2417])).
% 4.91/1.87  tff(c_2420, plain, (![A_33]: (~v1_xboole_0(A_33))), inference(splitRight, [status(thm)], [c_2274])).
% 4.91/1.87  tff(c_129, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_128, c_24])).
% 4.91/1.87  tff(c_2431, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2420, c_129])).
% 4.91/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.91/1.87  
% 4.91/1.87  Inference rules
% 4.91/1.87  ----------------------
% 4.91/1.87  #Ref     : 0
% 4.91/1.87  #Sup     : 469
% 4.91/1.87  #Fact    : 0
% 4.91/1.87  #Define  : 0
% 4.91/1.87  #Split   : 15
% 4.91/1.87  #Chain   : 0
% 4.91/1.87  #Close   : 0
% 4.91/1.87  
% 4.91/1.87  Ordering : KBO
% 4.91/1.87  
% 4.91/1.87  Simplification rules
% 4.91/1.87  ----------------------
% 4.91/1.87  #Subsume      : 42
% 4.91/1.87  #Demod        : 286
% 4.91/1.87  #Tautology    : 175
% 4.91/1.87  #SimpNegUnit  : 33
% 4.91/1.87  #BackRed      : 13
% 4.91/1.87  
% 4.91/1.87  #Partial instantiations: 0
% 4.91/1.87  #Strategies tried      : 1
% 4.91/1.87  
% 4.91/1.87  Timing (in seconds)
% 4.91/1.87  ----------------------
% 4.91/1.88  Preprocessing        : 0.39
% 4.91/1.88  Parsing              : 0.20
% 4.91/1.88  CNF conversion       : 0.03
% 4.91/1.88  Main loop            : 0.72
% 4.91/1.88  Inferencing          : 0.25
% 4.91/1.88  Reduction            : 0.26
% 4.91/1.88  Demodulation         : 0.18
% 4.91/1.88  BG Simplification    : 0.03
% 4.91/1.88  Subsumption          : 0.11
% 4.91/1.88  Abstraction          : 0.03
% 4.91/1.88  MUC search           : 0.00
% 4.91/1.88  Cooper               : 0.00
% 4.91/1.88  Total                : 1.15
% 4.91/1.88  Index Insertion      : 0.00
% 4.91/1.88  Index Deletion       : 0.00
% 4.91/1.88  Index Matching       : 0.00
% 4.91/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
