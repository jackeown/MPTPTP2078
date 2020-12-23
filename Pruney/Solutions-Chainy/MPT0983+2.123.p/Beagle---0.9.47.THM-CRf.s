%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:19 EST 2020

% Result     : Theorem 6.11s
% Output     : CNFRefutation 6.42s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 337 expanded)
%              Number of leaves         :   48 ( 138 expanded)
%              Depth                    :   15
%              Number of atoms          :  241 (1023 expanded)
%              Number of equality atoms :   46 ( 105 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

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

tff(f_132,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_120,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_100,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_98,axiom,(
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

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_80,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_68,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_79,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_130,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_66,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_165,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_80,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_78,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_76,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_72,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_60,plain,(
    ! [A_44] : k6_relat_1(A_44) = k6_partfun1(A_44) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_38,plain,(
    ! [A_21] : v2_funct_1(k6_relat_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_82,plain,(
    ! [A_21] : v2_funct_1(k6_partfun1(A_21)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_38])).

tff(c_2480,plain,(
    ! [E_313,F_315,C_316,A_317,B_314,D_318] :
      ( m1_subset_1(k1_partfun1(A_317,B_314,C_316,D_318,E_313,F_315),k1_zfmisc_1(k2_zfmisc_1(A_317,D_318)))
      | ~ m1_subset_1(F_315,k1_zfmisc_1(k2_zfmisc_1(C_316,D_318)))
      | ~ v1_funct_1(F_315)
      | ~ m1_subset_1(E_313,k1_zfmisc_1(k2_zfmisc_1(A_317,B_314)))
      | ~ v1_funct_1(E_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_48,plain,(
    ! [A_29] : m1_subset_1(k6_relat_1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_81,plain,(
    ! [A_29] : m1_subset_1(k6_partfun1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_48])).

tff(c_68,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_2145,plain,(
    ! [D_268,C_269,A_270,B_271] :
      ( D_268 = C_269
      | ~ r2_relset_1(A_270,B_271,C_269,D_268)
      | ~ m1_subset_1(D_268,k1_zfmisc_1(k2_zfmisc_1(A_270,B_271)))
      | ~ m1_subset_1(C_269,k1_zfmisc_1(k2_zfmisc_1(A_270,B_271))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2155,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_68,c_2145])).

tff(c_2174,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_2155])).

tff(c_2219,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2174])).

tff(c_2483,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2480,c_2219])).

tff(c_2517,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_2483])).

tff(c_2518,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2174])).

tff(c_3404,plain,(
    ! [C_420,D_419,E_418,B_416,A_417] :
      ( k1_xboole_0 = C_420
      | v2_funct_1(D_419)
      | ~ v2_funct_1(k1_partfun1(A_417,B_416,B_416,C_420,D_419,E_418))
      | ~ m1_subset_1(E_418,k1_zfmisc_1(k2_zfmisc_1(B_416,C_420)))
      | ~ v1_funct_2(E_418,B_416,C_420)
      | ~ v1_funct_1(E_418)
      | ~ m1_subset_1(D_419,k1_zfmisc_1(k2_zfmisc_1(A_417,B_416)))
      | ~ v1_funct_2(D_419,A_417,B_416)
      | ~ v1_funct_1(D_419) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_3408,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2518,c_3404])).

tff(c_3412,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_74,c_72,c_70,c_82,c_3408])).

tff(c_3413,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_3412])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_3449,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3413,c_2])).

tff(c_16,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3447,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_1',B_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3413,c_3413,c_16])).

tff(c_209,plain,(
    ! [B_66,A_67] :
      ( v1_xboole_0(B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_67))
      | ~ v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_227,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_76,c_209])).

tff(c_254,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_227])).

tff(c_3710,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3447,c_254])).

tff(c_3714,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3449,c_3710])).

tff(c_3715,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_227])).

tff(c_182,plain,(
    ! [B_62,A_63] :
      ( ~ v1_xboole_0(B_62)
      | B_62 = A_63
      | ~ v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_185,plain,(
    ! [A_63] :
      ( k1_xboole_0 = A_63
      | ~ v1_xboole_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_2,c_182])).

tff(c_3722,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3715,c_185])).

tff(c_115,plain,(
    ! [A_59] : k6_relat_1(A_59) = k6_partfun1(A_59) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_34,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_121,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_34])).

tff(c_137,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_82])).

tff(c_3740,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3722,c_137])).

tff(c_3748,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_3740])).

tff(c_3749,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_26,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3835,plain,(
    ! [B_446,A_447] :
      ( v1_relat_1(B_446)
      | ~ m1_subset_1(B_446,k1_zfmisc_1(A_447))
      | ~ v1_relat_1(A_447) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3844,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_70,c_3835])).

tff(c_3856,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_3844])).

tff(c_3909,plain,(
    ! [C_458,B_459,A_460] :
      ( v5_relat_1(C_458,B_459)
      | ~ m1_subset_1(C_458,k1_zfmisc_1(k2_zfmisc_1(A_460,B_459))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3926,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_3909])).

tff(c_3847,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_76,c_3835])).

tff(c_3859,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_3847])).

tff(c_32,plain,(
    ! [A_20] : k2_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_84,plain,(
    ! [A_20] : k2_relat_1(k6_partfun1(A_20)) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_32])).

tff(c_4338,plain,(
    ! [E_513,D_516,F_514,A_511,C_515,B_512] :
      ( k1_partfun1(A_511,B_512,C_515,D_516,E_513,F_514) = k5_relat_1(E_513,F_514)
      | ~ m1_subset_1(F_514,k1_zfmisc_1(k2_zfmisc_1(C_515,D_516)))
      | ~ v1_funct_1(F_514)
      | ~ m1_subset_1(E_513,k1_zfmisc_1(k2_zfmisc_1(A_511,B_512)))
      | ~ v1_funct_1(E_513) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_4342,plain,(
    ! [A_511,B_512,E_513] :
      ( k1_partfun1(A_511,B_512,'#skF_2','#skF_1',E_513,'#skF_4') = k5_relat_1(E_513,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_513,k1_zfmisc_1(k2_zfmisc_1(A_511,B_512)))
      | ~ v1_funct_1(E_513) ) ),
    inference(resolution,[status(thm)],[c_70,c_4338])).

tff(c_4719,plain,(
    ! [A_551,B_552,E_553] :
      ( k1_partfun1(A_551,B_552,'#skF_2','#skF_1',E_553,'#skF_4') = k5_relat_1(E_553,'#skF_4')
      | ~ m1_subset_1(E_553,k1_zfmisc_1(k2_zfmisc_1(A_551,B_552)))
      | ~ v1_funct_1(E_553) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_4342])).

tff(c_4737,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_4719])).

tff(c_4757,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4737])).

tff(c_54,plain,(
    ! [B_33,C_34,E_36,F_37,A_32,D_35] :
      ( m1_subset_1(k1_partfun1(A_32,B_33,C_34,D_35,E_36,F_37),k1_zfmisc_1(k2_zfmisc_1(A_32,D_35)))
      | ~ m1_subset_1(F_37,k1_zfmisc_1(k2_zfmisc_1(C_34,D_35)))
      | ~ v1_funct_1(F_37)
      | ~ m1_subset_1(E_36,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | ~ v1_funct_1(E_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_4866,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4757,c_54])).

tff(c_4872,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_4866])).

tff(c_4162,plain,(
    ! [D_488,C_489,A_490,B_491] :
      ( D_488 = C_489
      | ~ r2_relset_1(A_490,B_491,C_489,D_488)
      | ~ m1_subset_1(D_488,k1_zfmisc_1(k2_zfmisc_1(A_490,B_491)))
      | ~ m1_subset_1(C_489,k1_zfmisc_1(k2_zfmisc_1(A_490,B_491))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4168,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_68,c_4162])).

tff(c_4179,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_4168])).

tff(c_4968,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4872,c_4757,c_4757,c_4179])).

tff(c_28,plain,(
    ! [A_17,B_19] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_17,B_19)),k2_relat_1(B_19))
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4990,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_1')),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4968,c_28])).

tff(c_4998,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3859,c_3856,c_84,c_4990])).

tff(c_3871,plain,(
    ! [B_450,A_451] :
      ( r1_tarski(k2_relat_1(B_450),A_451)
      | ~ v5_relat_1(B_450,A_451)
      | ~ v1_relat_1(B_450) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3880,plain,(
    ! [B_450,A_451] :
      ( k2_relat_1(B_450) = A_451
      | ~ r1_tarski(A_451,k2_relat_1(B_450))
      | ~ v5_relat_1(B_450,A_451)
      | ~ v1_relat_1(B_450) ) ),
    inference(resolution,[status(thm)],[c_3871,c_4])).

tff(c_5002,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4998,c_3880])).

tff(c_5007,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3856,c_3926,c_5002])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3950,plain,(
    ! [B_465,A_466] :
      ( v5_relat_1(B_465,A_466)
      | ~ r1_tarski(k2_relat_1(B_465),A_466)
      | ~ v1_relat_1(B_465) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3969,plain,(
    ! [B_465] :
      ( v5_relat_1(B_465,k2_relat_1(B_465))
      | ~ v1_relat_1(B_465) ) ),
    inference(resolution,[status(thm)],[c_8,c_3950])).

tff(c_4002,plain,(
    ! [B_470] :
      ( v2_funct_2(B_470,k2_relat_1(B_470))
      | ~ v5_relat_1(B_470,k2_relat_1(B_470))
      | ~ v1_relat_1(B_470) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_4019,plain,(
    ! [B_465] :
      ( v2_funct_2(B_465,k2_relat_1(B_465))
      | ~ v1_relat_1(B_465) ) ),
    inference(resolution,[status(thm)],[c_3969,c_4002])).

tff(c_5026,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5007,c_4019])).

tff(c_5047,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3856,c_5026])).

tff(c_5049,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3749,c_5047])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:26:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.11/2.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.42/2.23  
% 6.42/2.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.42/2.23  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.42/2.23  
% 6.42/2.23  %Foreground sorts:
% 6.42/2.23  
% 6.42/2.23  
% 6.42/2.23  %Background operators:
% 6.42/2.23  
% 6.42/2.23  
% 6.42/2.23  %Foreground operators:
% 6.42/2.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.42/2.23  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.42/2.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.42/2.23  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.42/2.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.42/2.23  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.42/2.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.42/2.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.42/2.23  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.42/2.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.42/2.23  tff('#skF_2', type, '#skF_2': $i).
% 6.42/2.23  tff('#skF_3', type, '#skF_3': $i).
% 6.42/2.23  tff('#skF_1', type, '#skF_1': $i).
% 6.42/2.23  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.42/2.23  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.42/2.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.42/2.23  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.42/2.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.42/2.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.42/2.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.42/2.23  tff('#skF_4', type, '#skF_4': $i).
% 6.42/2.23  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.42/2.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.42/2.23  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.42/2.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.42/2.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.42/2.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.42/2.23  
% 6.42/2.25  tff(f_174, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 6.42/2.25  tff(f_132, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.42/2.25  tff(f_84, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 6.42/2.25  tff(f_120, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.42/2.25  tff(f_100, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 6.42/2.25  tff(f_98, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.42/2.25  tff(f_154, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 6.42/2.25  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.42/2.25  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.42/2.25  tff(f_53, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 6.42/2.25  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 6.42/2.25  tff(f_80, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 6.42/2.25  tff(f_68, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.42/2.25  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.42/2.25  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.42/2.25  tff(f_79, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 6.42/2.25  tff(f_130, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.42/2.25  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 6.42/2.25  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 6.42/2.25  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.42/2.25  tff(f_108, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 6.42/2.25  tff(c_66, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_174])).
% 6.42/2.25  tff(c_165, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_66])).
% 6.42/2.25  tff(c_80, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_174])).
% 6.42/2.25  tff(c_78, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_174])).
% 6.42/2.25  tff(c_76, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_174])).
% 6.42/2.25  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_174])).
% 6.42/2.25  tff(c_72, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_174])).
% 6.42/2.25  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_174])).
% 6.42/2.25  tff(c_60, plain, (![A_44]: (k6_relat_1(A_44)=k6_partfun1(A_44))), inference(cnfTransformation, [status(thm)], [f_132])).
% 6.42/2.25  tff(c_38, plain, (![A_21]: (v2_funct_1(k6_relat_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.42/2.25  tff(c_82, plain, (![A_21]: (v2_funct_1(k6_partfun1(A_21)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_38])).
% 6.42/2.25  tff(c_2480, plain, (![E_313, F_315, C_316, A_317, B_314, D_318]: (m1_subset_1(k1_partfun1(A_317, B_314, C_316, D_318, E_313, F_315), k1_zfmisc_1(k2_zfmisc_1(A_317, D_318))) | ~m1_subset_1(F_315, k1_zfmisc_1(k2_zfmisc_1(C_316, D_318))) | ~v1_funct_1(F_315) | ~m1_subset_1(E_313, k1_zfmisc_1(k2_zfmisc_1(A_317, B_314))) | ~v1_funct_1(E_313))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.42/2.25  tff(c_48, plain, (![A_29]: (m1_subset_1(k6_relat_1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.42/2.25  tff(c_81, plain, (![A_29]: (m1_subset_1(k6_partfun1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_48])).
% 6.42/2.25  tff(c_68, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_174])).
% 6.42/2.25  tff(c_2145, plain, (![D_268, C_269, A_270, B_271]: (D_268=C_269 | ~r2_relset_1(A_270, B_271, C_269, D_268) | ~m1_subset_1(D_268, k1_zfmisc_1(k2_zfmisc_1(A_270, B_271))) | ~m1_subset_1(C_269, k1_zfmisc_1(k2_zfmisc_1(A_270, B_271))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.42/2.25  tff(c_2155, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_68, c_2145])).
% 6.42/2.25  tff(c_2174, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_2155])).
% 6.42/2.25  tff(c_2219, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2174])).
% 6.42/2.25  tff(c_2483, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2480, c_2219])).
% 6.42/2.25  tff(c_2517, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_2483])).
% 6.42/2.25  tff(c_2518, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2174])).
% 6.42/2.25  tff(c_3404, plain, (![C_420, D_419, E_418, B_416, A_417]: (k1_xboole_0=C_420 | v2_funct_1(D_419) | ~v2_funct_1(k1_partfun1(A_417, B_416, B_416, C_420, D_419, E_418)) | ~m1_subset_1(E_418, k1_zfmisc_1(k2_zfmisc_1(B_416, C_420))) | ~v1_funct_2(E_418, B_416, C_420) | ~v1_funct_1(E_418) | ~m1_subset_1(D_419, k1_zfmisc_1(k2_zfmisc_1(A_417, B_416))) | ~v1_funct_2(D_419, A_417, B_416) | ~v1_funct_1(D_419))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.42/2.25  tff(c_3408, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2518, c_3404])).
% 6.42/2.25  tff(c_3412, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_74, c_72, c_70, c_82, c_3408])).
% 6.42/2.25  tff(c_3413, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_165, c_3412])).
% 6.42/2.25  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.42/2.25  tff(c_3449, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3413, c_2])).
% 6.42/2.25  tff(c_16, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.42/2.25  tff(c_3447, plain, (![B_6]: (k2_zfmisc_1('#skF_1', B_6)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3413, c_3413, c_16])).
% 6.42/2.25  tff(c_209, plain, (![B_66, A_67]: (v1_xboole_0(B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(A_67)) | ~v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.42/2.25  tff(c_227, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_76, c_209])).
% 6.42/2.25  tff(c_254, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_227])).
% 6.42/2.25  tff(c_3710, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3447, c_254])).
% 6.42/2.25  tff(c_3714, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3449, c_3710])).
% 6.42/2.25  tff(c_3715, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_227])).
% 6.42/2.25  tff(c_182, plain, (![B_62, A_63]: (~v1_xboole_0(B_62) | B_62=A_63 | ~v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.42/2.25  tff(c_185, plain, (![A_63]: (k1_xboole_0=A_63 | ~v1_xboole_0(A_63))), inference(resolution, [status(thm)], [c_2, c_182])).
% 6.42/2.25  tff(c_3722, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3715, c_185])).
% 6.42/2.25  tff(c_115, plain, (![A_59]: (k6_relat_1(A_59)=k6_partfun1(A_59))), inference(cnfTransformation, [status(thm)], [f_132])).
% 6.42/2.25  tff(c_34, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.42/2.25  tff(c_121, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_115, c_34])).
% 6.42/2.25  tff(c_137, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_121, c_82])).
% 6.42/2.25  tff(c_3740, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3722, c_137])).
% 6.42/2.25  tff(c_3748, plain, $false, inference(negUnitSimplification, [status(thm)], [c_165, c_3740])).
% 6.42/2.25  tff(c_3749, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_66])).
% 6.42/2.25  tff(c_26, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.42/2.25  tff(c_3835, plain, (![B_446, A_447]: (v1_relat_1(B_446) | ~m1_subset_1(B_446, k1_zfmisc_1(A_447)) | ~v1_relat_1(A_447))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.42/2.25  tff(c_3844, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_70, c_3835])).
% 6.42/2.25  tff(c_3856, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_3844])).
% 6.42/2.25  tff(c_3909, plain, (![C_458, B_459, A_460]: (v5_relat_1(C_458, B_459) | ~m1_subset_1(C_458, k1_zfmisc_1(k2_zfmisc_1(A_460, B_459))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.42/2.25  tff(c_3926, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_70, c_3909])).
% 6.42/2.25  tff(c_3847, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_76, c_3835])).
% 6.42/2.25  tff(c_3859, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_3847])).
% 6.42/2.25  tff(c_32, plain, (![A_20]: (k2_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.42/2.25  tff(c_84, plain, (![A_20]: (k2_relat_1(k6_partfun1(A_20))=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_32])).
% 6.42/2.25  tff(c_4338, plain, (![E_513, D_516, F_514, A_511, C_515, B_512]: (k1_partfun1(A_511, B_512, C_515, D_516, E_513, F_514)=k5_relat_1(E_513, F_514) | ~m1_subset_1(F_514, k1_zfmisc_1(k2_zfmisc_1(C_515, D_516))) | ~v1_funct_1(F_514) | ~m1_subset_1(E_513, k1_zfmisc_1(k2_zfmisc_1(A_511, B_512))) | ~v1_funct_1(E_513))), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.42/2.25  tff(c_4342, plain, (![A_511, B_512, E_513]: (k1_partfun1(A_511, B_512, '#skF_2', '#skF_1', E_513, '#skF_4')=k5_relat_1(E_513, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_513, k1_zfmisc_1(k2_zfmisc_1(A_511, B_512))) | ~v1_funct_1(E_513))), inference(resolution, [status(thm)], [c_70, c_4338])).
% 6.42/2.25  tff(c_4719, plain, (![A_551, B_552, E_553]: (k1_partfun1(A_551, B_552, '#skF_2', '#skF_1', E_553, '#skF_4')=k5_relat_1(E_553, '#skF_4') | ~m1_subset_1(E_553, k1_zfmisc_1(k2_zfmisc_1(A_551, B_552))) | ~v1_funct_1(E_553))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_4342])).
% 6.42/2.25  tff(c_4737, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_4719])).
% 6.42/2.25  tff(c_4757, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4737])).
% 6.42/2.25  tff(c_54, plain, (![B_33, C_34, E_36, F_37, A_32, D_35]: (m1_subset_1(k1_partfun1(A_32, B_33, C_34, D_35, E_36, F_37), k1_zfmisc_1(k2_zfmisc_1(A_32, D_35))) | ~m1_subset_1(F_37, k1_zfmisc_1(k2_zfmisc_1(C_34, D_35))) | ~v1_funct_1(F_37) | ~m1_subset_1(E_36, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | ~v1_funct_1(E_36))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.42/2.25  tff(c_4866, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4757, c_54])).
% 6.42/2.25  tff(c_4872, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_4866])).
% 6.42/2.25  tff(c_4162, plain, (![D_488, C_489, A_490, B_491]: (D_488=C_489 | ~r2_relset_1(A_490, B_491, C_489, D_488) | ~m1_subset_1(D_488, k1_zfmisc_1(k2_zfmisc_1(A_490, B_491))) | ~m1_subset_1(C_489, k1_zfmisc_1(k2_zfmisc_1(A_490, B_491))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.42/2.25  tff(c_4168, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_68, c_4162])).
% 6.42/2.25  tff(c_4179, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_4168])).
% 6.42/2.25  tff(c_4968, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4872, c_4757, c_4757, c_4179])).
% 6.42/2.25  tff(c_28, plain, (![A_17, B_19]: (r1_tarski(k2_relat_1(k5_relat_1(A_17, B_19)), k2_relat_1(B_19)) | ~v1_relat_1(B_19) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.42/2.25  tff(c_4990, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_1')), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4968, c_28])).
% 6.42/2.25  tff(c_4998, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3859, c_3856, c_84, c_4990])).
% 6.42/2.25  tff(c_3871, plain, (![B_450, A_451]: (r1_tarski(k2_relat_1(B_450), A_451) | ~v5_relat_1(B_450, A_451) | ~v1_relat_1(B_450))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.42/2.25  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.42/2.25  tff(c_3880, plain, (![B_450, A_451]: (k2_relat_1(B_450)=A_451 | ~r1_tarski(A_451, k2_relat_1(B_450)) | ~v5_relat_1(B_450, A_451) | ~v1_relat_1(B_450))), inference(resolution, [status(thm)], [c_3871, c_4])).
% 6.42/2.25  tff(c_5002, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4998, c_3880])).
% 6.42/2.25  tff(c_5007, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3856, c_3926, c_5002])).
% 6.42/2.25  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.42/2.25  tff(c_3950, plain, (![B_465, A_466]: (v5_relat_1(B_465, A_466) | ~r1_tarski(k2_relat_1(B_465), A_466) | ~v1_relat_1(B_465))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.42/2.25  tff(c_3969, plain, (![B_465]: (v5_relat_1(B_465, k2_relat_1(B_465)) | ~v1_relat_1(B_465))), inference(resolution, [status(thm)], [c_8, c_3950])).
% 6.42/2.25  tff(c_4002, plain, (![B_470]: (v2_funct_2(B_470, k2_relat_1(B_470)) | ~v5_relat_1(B_470, k2_relat_1(B_470)) | ~v1_relat_1(B_470))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.42/2.25  tff(c_4019, plain, (![B_465]: (v2_funct_2(B_465, k2_relat_1(B_465)) | ~v1_relat_1(B_465))), inference(resolution, [status(thm)], [c_3969, c_4002])).
% 6.42/2.25  tff(c_5026, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5007, c_4019])).
% 6.42/2.25  tff(c_5047, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3856, c_5026])).
% 6.42/2.25  tff(c_5049, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3749, c_5047])).
% 6.42/2.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.42/2.25  
% 6.42/2.25  Inference rules
% 6.42/2.25  ----------------------
% 6.42/2.25  #Ref     : 0
% 6.42/2.25  #Sup     : 1031
% 6.42/2.25  #Fact    : 0
% 6.42/2.25  #Define  : 0
% 6.42/2.25  #Split   : 17
% 6.42/2.25  #Chain   : 0
% 6.42/2.25  #Close   : 0
% 6.42/2.25  
% 6.42/2.25  Ordering : KBO
% 6.42/2.25  
% 6.42/2.25  Simplification rules
% 6.42/2.25  ----------------------
% 6.42/2.25  #Subsume      : 110
% 6.42/2.25  #Demod        : 1133
% 6.42/2.25  #Tautology    : 308
% 6.42/2.25  #SimpNegUnit  : 8
% 6.42/2.25  #BackRed      : 154
% 6.42/2.25  
% 6.42/2.25  #Partial instantiations: 0
% 6.42/2.25  #Strategies tried      : 1
% 6.42/2.25  
% 6.42/2.25  Timing (in seconds)
% 6.42/2.25  ----------------------
% 6.42/2.25  Preprocessing        : 0.34
% 6.42/2.25  Parsing              : 0.18
% 6.42/2.25  CNF conversion       : 0.02
% 6.42/2.25  Main loop            : 1.11
% 6.42/2.25  Inferencing          : 0.38
% 6.42/2.25  Reduction            : 0.41
% 6.42/2.25  Demodulation         : 0.29
% 6.42/2.25  BG Simplification    : 0.04
% 6.42/2.25  Subsumption          : 0.18
% 6.42/2.25  Abstraction          : 0.05
% 6.42/2.25  MUC search           : 0.00
% 6.42/2.25  Cooper               : 0.00
% 6.42/2.25  Total                : 1.50
% 6.42/2.25  Index Insertion      : 0.00
% 6.42/2.25  Index Deletion       : 0.00
% 6.42/2.25  Index Matching       : 0.00
% 6.42/2.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
