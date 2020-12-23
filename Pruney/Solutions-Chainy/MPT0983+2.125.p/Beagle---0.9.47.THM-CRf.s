%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:19 EST 2020

% Result     : Theorem 9.21s
% Output     : CNFRefutation 9.34s
% Verified   : 
% Statistics : Number of formulae       :  188 ( 597 expanded)
%              Number of leaves         :   49 ( 222 expanded)
%              Depth                    :   15
%              Number of atoms          :  360 (1646 expanded)
%              Number of equality atoms :   60 ( 147 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_180,negated_conjecture,(
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

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_138,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_126,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_106,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_104,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_160,axiom,(
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

tff(f_75,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_114,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_86,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_136,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_39,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_68,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_152,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_8,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_82,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_80,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_78,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_74,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_62,plain,(
    ! [A_47] : k6_relat_1(A_47) = k6_partfun1(A_47) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_40,plain,(
    ! [A_24] : v2_funct_1(k6_relat_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_84,plain,(
    ! [A_24] : v2_funct_1(k6_partfun1(A_24)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_40])).

tff(c_2015,plain,(
    ! [B_296,C_293,D_295,A_291,F_292,E_294] :
      ( m1_subset_1(k1_partfun1(A_291,B_296,C_293,D_295,E_294,F_292),k1_zfmisc_1(k2_zfmisc_1(A_291,D_295)))
      | ~ m1_subset_1(F_292,k1_zfmisc_1(k2_zfmisc_1(C_293,D_295)))
      | ~ v1_funct_1(F_292)
      | ~ m1_subset_1(E_294,k1_zfmisc_1(k2_zfmisc_1(A_291,B_296)))
      | ~ v1_funct_1(E_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_50,plain,(
    ! [A_32] : m1_subset_1(k6_relat_1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_83,plain,(
    ! [A_32] : m1_subset_1(k6_partfun1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50])).

tff(c_70,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_1657,plain,(
    ! [D_246,C_247,A_248,B_249] :
      ( D_246 = C_247
      | ~ r2_relset_1(A_248,B_249,C_247,D_246)
      | ~ m1_subset_1(D_246,k1_zfmisc_1(k2_zfmisc_1(A_248,B_249)))
      | ~ m1_subset_1(C_247,k1_zfmisc_1(k2_zfmisc_1(A_248,B_249))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1667,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_70,c_1657])).

tff(c_1686,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_1667])).

tff(c_1754,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1686])).

tff(c_2018,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2015,c_1754])).

tff(c_2052,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_76,c_72,c_2018])).

tff(c_2053,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1686])).

tff(c_2557,plain,(
    ! [C_357,D_354,E_353,B_355,A_356] :
      ( k1_xboole_0 = C_357
      | v2_funct_1(D_354)
      | ~ v2_funct_1(k1_partfun1(A_356,B_355,B_355,C_357,D_354,E_353))
      | ~ m1_subset_1(E_353,k1_zfmisc_1(k2_zfmisc_1(B_355,C_357)))
      | ~ v1_funct_2(E_353,B_355,C_357)
      | ~ v1_funct_1(E_353)
      | ~ m1_subset_1(D_354,k1_zfmisc_1(k2_zfmisc_1(A_356,B_355)))
      | ~ v1_funct_2(D_354,A_356,B_355)
      | ~ v1_funct_1(D_354) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_2561,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2053,c_2557])).

tff(c_2565,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_76,c_74,c_72,c_84,c_2561])).

tff(c_2566,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_2565])).

tff(c_30,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_242,plain,(
    ! [B_79,A_80] :
      ( v1_relat_1(B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_80))
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_251,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_72,c_242])).

tff(c_263,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_251])).

tff(c_310,plain,(
    ! [C_81,B_82,A_83] :
      ( v5_relat_1(C_81,B_82)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_83,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_327,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_310])).

tff(c_557,plain,(
    ! [B_108,A_109] :
      ( k2_relat_1(B_108) = A_109
      | ~ v2_funct_2(B_108,A_109)
      | ~ v5_relat_1(B_108,A_109)
      | ~ v1_relat_1(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_575,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_327,c_557])).

tff(c_592,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_575])).

tff(c_600,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_592])).

tff(c_254,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_78,c_242])).

tff(c_266,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_254])).

tff(c_36,plain,(
    ! [A_23] : k2_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_86,plain,(
    ! [A_23] : k2_relat_1(k6_partfun1(A_23)) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_36])).

tff(c_1007,plain,(
    ! [D_170,F_167,A_166,E_169,B_171,C_168] :
      ( m1_subset_1(k1_partfun1(A_166,B_171,C_168,D_170,E_169,F_167),k1_zfmisc_1(k2_zfmisc_1(A_166,D_170)))
      | ~ m1_subset_1(F_167,k1_zfmisc_1(k2_zfmisc_1(C_168,D_170)))
      | ~ v1_funct_1(F_167)
      | ~ m1_subset_1(E_169,k1_zfmisc_1(k2_zfmisc_1(A_166,B_171)))
      | ~ v1_funct_1(E_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_690,plain,(
    ! [D_123,C_124,A_125,B_126] :
      ( D_123 = C_124
      | ~ r2_relset_1(A_125,B_126,C_124,D_123)
      | ~ m1_subset_1(D_123,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126)))
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_700,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_70,c_690])).

tff(c_719,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_700])).

tff(c_764,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_719])).

tff(c_1013,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1007,c_764])).

tff(c_1045,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_76,c_72,c_1013])).

tff(c_1046,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_719])).

tff(c_1250,plain,(
    ! [B_205,E_200,D_203,C_202,F_204,A_201] :
      ( k1_partfun1(A_201,B_205,C_202,D_203,E_200,F_204) = k5_relat_1(E_200,F_204)
      | ~ m1_subset_1(F_204,k1_zfmisc_1(k2_zfmisc_1(C_202,D_203)))
      | ~ v1_funct_1(F_204)
      | ~ m1_subset_1(E_200,k1_zfmisc_1(k2_zfmisc_1(A_201,B_205)))
      | ~ v1_funct_1(E_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1254,plain,(
    ! [A_201,B_205,E_200] :
      ( k1_partfun1(A_201,B_205,'#skF_2','#skF_1',E_200,'#skF_4') = k5_relat_1(E_200,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_200,k1_zfmisc_1(k2_zfmisc_1(A_201,B_205)))
      | ~ v1_funct_1(E_200) ) ),
    inference(resolution,[status(thm)],[c_72,c_1250])).

tff(c_1395,plain,(
    ! [A_228,B_229,E_230] :
      ( k1_partfun1(A_228,B_229,'#skF_2','#skF_1',E_230,'#skF_4') = k5_relat_1(E_230,'#skF_4')
      | ~ m1_subset_1(E_230,k1_zfmisc_1(k2_zfmisc_1(A_228,B_229)))
      | ~ v1_funct_1(E_230) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1254])).

tff(c_1407,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_1395])).

tff(c_1421,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1046,c_1407])).

tff(c_32,plain,(
    ! [A_20,B_22] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_20,B_22)),k2_relat_1(B_22))
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1428,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_1')),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1421,c_32])).

tff(c_1434,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_263,c_86,c_1428])).

tff(c_388,plain,(
    ! [B_93,A_94] :
      ( r1_tarski(k2_relat_1(B_93),A_94)
      | ~ v5_relat_1(B_93,A_94)
      | ~ v1_relat_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( B_3 = A_2
      | ~ r1_tarski(B_3,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_411,plain,(
    ! [B_93,A_94] :
      ( k2_relat_1(B_93) = A_94
      | ~ r1_tarski(A_94,k2_relat_1(B_93))
      | ~ v5_relat_1(B_93,A_94)
      | ~ v1_relat_1(B_93) ) ),
    inference(resolution,[status(thm)],[c_388,c_4])).

tff(c_1438,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1434,c_411])).

tff(c_1443,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_327,c_1438])).

tff(c_354,plain,(
    ! [B_87,A_88] :
      ( v5_relat_1(B_87,A_88)
      | ~ r1_tarski(k2_relat_1(B_87),A_88)
      | ~ v1_relat_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_369,plain,(
    ! [B_87] :
      ( v5_relat_1(B_87,k2_relat_1(B_87))
      | ~ v1_relat_1(B_87) ) ),
    inference(resolution,[status(thm)],[c_8,c_354])).

tff(c_521,plain,(
    ! [B_106] :
      ( v2_funct_2(B_106,k2_relat_1(B_106))
      | ~ v5_relat_1(B_106,k2_relat_1(B_106))
      | ~ v1_relat_1(B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_542,plain,(
    ! [B_87] :
      ( v2_funct_2(B_87,k2_relat_1(B_87))
      | ~ v1_relat_1(B_87) ) ),
    inference(resolution,[status(thm)],[c_369,c_521])).

tff(c_1459,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1443,c_542])).

tff(c_1481,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_1459])).

tff(c_1483,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_600,c_1481])).

tff(c_1484,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_592])).

tff(c_26,plain,(
    ! [B_17,A_16] :
      ( v5_relat_1(B_17,A_16)
      | ~ r1_tarski(k2_relat_1(B_17),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1501,plain,(
    ! [A_16] :
      ( v5_relat_1('#skF_4',A_16)
      | ~ r1_tarski('#skF_1',A_16)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1484,c_26])).

tff(c_1576,plain,(
    ! [A_235] :
      ( v5_relat_1('#skF_4',A_235)
      | ~ r1_tarski('#skF_1',A_235) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_1501])).

tff(c_12,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_186,plain,(
    ! [B_72,A_73] :
      ( ~ r1_xboole_0(B_72,A_73)
      | ~ r1_tarski(B_72,A_73)
      | v1_xboole_0(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_190,plain,(
    ! [A_5] :
      ( ~ r1_tarski(A_5,k1_xboole_0)
      | v1_xboole_0(A_5) ) ),
    inference(resolution,[status(thm)],[c_12,c_186])).

tff(c_409,plain,(
    ! [B_93] :
      ( v1_xboole_0(k2_relat_1(B_93))
      | ~ v5_relat_1(B_93,k1_xboole_0)
      | ~ v1_relat_1(B_93) ) ),
    inference(resolution,[status(thm)],[c_388,c_190])).

tff(c_1492,plain,
    ( v1_xboole_0('#skF_1')
    | ~ v5_relat_1('#skF_4',k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1484,c_409])).

tff(c_1507,plain,
    ( v1_xboole_0('#skF_1')
    | ~ v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_1492])).

tff(c_1539,plain,(
    ~ v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1507])).

tff(c_1591,plain,(
    ~ r1_tarski('#skF_1',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1576,c_1539])).

tff(c_2581,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2566,c_1591])).

tff(c_2607,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2581])).

tff(c_2608,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1507])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2613,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2608,c_2])).

tff(c_20,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2634,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_1',B_9) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2613,c_2613,c_20])).

tff(c_219,plain,(
    ! [B_77,A_78] :
      ( v1_xboole_0(B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_78))
      | ~ v1_xboole_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_237,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_78,c_219])).

tff(c_333,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_237])).

tff(c_2821,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2634,c_333])).

tff(c_2825,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2608,c_2821])).

tff(c_2826,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_237])).

tff(c_2831,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2826,c_2])).

tff(c_191,plain,(
    ! [A_74] :
      ( ~ r1_tarski(A_74,k1_xboole_0)
      | v1_xboole_0(A_74) ) ),
    inference(resolution,[status(thm)],[c_12,c_186])).

tff(c_200,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_191])).

tff(c_18,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_153,plain,(
    ! [A_68] : m1_subset_1(k6_partfun1(A_68),k1_zfmisc_1(k2_zfmisc_1(A_68,A_68))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50])).

tff(c_157,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_153])).

tff(c_222,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_157,c_219])).

tff(c_234,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_222])).

tff(c_241,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_234,c_2])).

tff(c_283,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_84])).

tff(c_2835,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2831,c_283])).

tff(c_2848,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_2835])).

tff(c_2849,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_3034,plain,(
    ! [B_393,A_394] :
      ( v1_relat_1(B_393)
      | ~ m1_subset_1(B_393,k1_zfmisc_1(A_394))
      | ~ v1_relat_1(A_394) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3043,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_72,c_3034])).

tff(c_3055,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3043])).

tff(c_3073,plain,(
    ! [C_396,B_397,A_398] :
      ( v5_relat_1(C_396,B_397)
      | ~ m1_subset_1(C_396,k1_zfmisc_1(k2_zfmisc_1(A_398,B_397))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_3090,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_3073])).

tff(c_3046,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_78,c_3034])).

tff(c_3058,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3046])).

tff(c_3557,plain,(
    ! [A_454,F_457,D_456,E_453,C_455,B_458] :
      ( k1_partfun1(A_454,B_458,C_455,D_456,E_453,F_457) = k5_relat_1(E_453,F_457)
      | ~ m1_subset_1(F_457,k1_zfmisc_1(k2_zfmisc_1(C_455,D_456)))
      | ~ v1_funct_1(F_457)
      | ~ m1_subset_1(E_453,k1_zfmisc_1(k2_zfmisc_1(A_454,B_458)))
      | ~ v1_funct_1(E_453) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_3561,plain,(
    ! [A_454,B_458,E_453] :
      ( k1_partfun1(A_454,B_458,'#skF_2','#skF_1',E_453,'#skF_4') = k5_relat_1(E_453,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_453,k1_zfmisc_1(k2_zfmisc_1(A_454,B_458)))
      | ~ v1_funct_1(E_453) ) ),
    inference(resolution,[status(thm)],[c_72,c_3557])).

tff(c_3755,plain,(
    ! [A_481,B_482,E_483] :
      ( k1_partfun1(A_481,B_482,'#skF_2','#skF_1',E_483,'#skF_4') = k5_relat_1(E_483,'#skF_4')
      | ~ m1_subset_1(E_483,k1_zfmisc_1(k2_zfmisc_1(A_481,B_482)))
      | ~ v1_funct_1(E_483) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_3561])).

tff(c_3767,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_3755])).

tff(c_3781,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_3767])).

tff(c_56,plain,(
    ! [A_35,F_40,B_36,C_37,D_38,E_39] :
      ( m1_subset_1(k1_partfun1(A_35,B_36,C_37,D_38,E_39,F_40),k1_zfmisc_1(k2_zfmisc_1(A_35,D_38)))
      | ~ m1_subset_1(F_40,k1_zfmisc_1(k2_zfmisc_1(C_37,D_38)))
      | ~ v1_funct_1(F_40)
      | ~ m1_subset_1(E_39,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36)))
      | ~ v1_funct_1(E_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_3883,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3781,c_56])).

tff(c_3887,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_76,c_72,c_3883])).

tff(c_3384,plain,(
    ! [D_433,C_434,A_435,B_436] :
      ( D_433 = C_434
      | ~ r2_relset_1(A_435,B_436,C_434,D_433)
      | ~ m1_subset_1(D_433,k1_zfmisc_1(k2_zfmisc_1(A_435,B_436)))
      | ~ m1_subset_1(C_434,k1_zfmisc_1(k2_zfmisc_1(A_435,B_436))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3392,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_70,c_3384])).

tff(c_3407,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_3392])).

tff(c_4193,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3887,c_3781,c_3781,c_3407])).

tff(c_4217,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_1')),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4193,c_32])).

tff(c_4225,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3058,c_3055,c_86,c_4217])).

tff(c_3115,plain,(
    ! [B_403,A_404] :
      ( r1_tarski(k2_relat_1(B_403),A_404)
      | ~ v5_relat_1(B_403,A_404)
      | ~ v1_relat_1(B_403) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3134,plain,(
    ! [B_403,A_404] :
      ( k2_relat_1(B_403) = A_404
      | ~ r1_tarski(A_404,k2_relat_1(B_403))
      | ~ v5_relat_1(B_403,A_404)
      | ~ v1_relat_1(B_403) ) ),
    inference(resolution,[status(thm)],[c_3115,c_4])).

tff(c_4229,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4225,c_3134])).

tff(c_4234,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3055,c_3090,c_4229])).

tff(c_3159,plain,(
    ! [B_411,A_412] :
      ( v5_relat_1(B_411,A_412)
      | ~ r1_tarski(k2_relat_1(B_411),A_412)
      | ~ v1_relat_1(B_411) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3178,plain,(
    ! [B_411] :
      ( v5_relat_1(B_411,k2_relat_1(B_411))
      | ~ v1_relat_1(B_411) ) ),
    inference(resolution,[status(thm)],[c_8,c_3159])).

tff(c_3209,plain,(
    ! [B_417] :
      ( v2_funct_2(B_417,k2_relat_1(B_417))
      | ~ v5_relat_1(B_417,k2_relat_1(B_417))
      | ~ v1_relat_1(B_417) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_3230,plain,(
    ! [B_411] :
      ( v2_funct_2(B_411,k2_relat_1(B_411))
      | ~ v1_relat_1(B_411) ) ),
    inference(resolution,[status(thm)],[c_3178,c_3209])).

tff(c_4256,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4234,c_3230])).

tff(c_4279,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3055,c_4256])).

tff(c_4281,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2849,c_4279])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:57:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.21/3.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.34/3.27  
% 9.34/3.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.34/3.28  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.34/3.28  
% 9.34/3.28  %Foreground sorts:
% 9.34/3.28  
% 9.34/3.28  
% 9.34/3.28  %Background operators:
% 9.34/3.28  
% 9.34/3.28  
% 9.34/3.28  %Foreground operators:
% 9.34/3.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.34/3.28  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.34/3.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.34/3.28  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.34/3.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.34/3.28  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.34/3.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.34/3.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.34/3.28  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.34/3.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.34/3.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.34/3.28  tff('#skF_2', type, '#skF_2': $i).
% 9.34/3.28  tff('#skF_3', type, '#skF_3': $i).
% 9.34/3.28  tff('#skF_1', type, '#skF_1': $i).
% 9.34/3.28  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 9.34/3.28  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.34/3.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.34/3.28  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.34/3.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.34/3.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.34/3.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.34/3.28  tff('#skF_4', type, '#skF_4': $i).
% 9.34/3.28  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.34/3.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.34/3.28  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.34/3.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.34/3.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.34/3.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.34/3.28  
% 9.34/3.32  tff(f_180, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 9.34/3.32  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.34/3.32  tff(f_138, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.34/3.32  tff(f_90, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 9.34/3.32  tff(f_126, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 9.34/3.32  tff(f_106, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 9.34/3.32  tff(f_104, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 9.34/3.32  tff(f_160, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 9.34/3.32  tff(f_75, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.34/3.32  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.34/3.32  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.34/3.32  tff(f_114, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 9.34/3.32  tff(f_86, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 9.34/3.32  tff(f_136, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 9.34/3.32  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 9.34/3.32  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 9.34/3.32  tff(f_39, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 9.34/3.32  tff(f_47, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 9.34/3.32  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 9.34/3.32  tff(f_53, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.34/3.32  tff(f_60, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 9.34/3.32  tff(c_68, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 9.34/3.32  tff(c_152, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_68])).
% 9.34/3.32  tff(c_8, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.34/3.32  tff(c_82, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 9.34/3.32  tff(c_80, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_180])).
% 9.34/3.32  tff(c_78, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_180])).
% 9.34/3.32  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_180])).
% 9.34/3.32  tff(c_74, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_180])).
% 9.34/3.32  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_180])).
% 9.34/3.32  tff(c_62, plain, (![A_47]: (k6_relat_1(A_47)=k6_partfun1(A_47))), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.34/3.32  tff(c_40, plain, (![A_24]: (v2_funct_1(k6_relat_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.34/3.32  tff(c_84, plain, (![A_24]: (v2_funct_1(k6_partfun1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_40])).
% 9.34/3.32  tff(c_2015, plain, (![B_296, C_293, D_295, A_291, F_292, E_294]: (m1_subset_1(k1_partfun1(A_291, B_296, C_293, D_295, E_294, F_292), k1_zfmisc_1(k2_zfmisc_1(A_291, D_295))) | ~m1_subset_1(F_292, k1_zfmisc_1(k2_zfmisc_1(C_293, D_295))) | ~v1_funct_1(F_292) | ~m1_subset_1(E_294, k1_zfmisc_1(k2_zfmisc_1(A_291, B_296))) | ~v1_funct_1(E_294))), inference(cnfTransformation, [status(thm)], [f_126])).
% 9.34/3.32  tff(c_50, plain, (![A_32]: (m1_subset_1(k6_relat_1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.34/3.32  tff(c_83, plain, (![A_32]: (m1_subset_1(k6_partfun1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_50])).
% 9.34/3.32  tff(c_70, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_180])).
% 9.34/3.32  tff(c_1657, plain, (![D_246, C_247, A_248, B_249]: (D_246=C_247 | ~r2_relset_1(A_248, B_249, C_247, D_246) | ~m1_subset_1(D_246, k1_zfmisc_1(k2_zfmisc_1(A_248, B_249))) | ~m1_subset_1(C_247, k1_zfmisc_1(k2_zfmisc_1(A_248, B_249))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.34/3.32  tff(c_1667, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_70, c_1657])).
% 9.34/3.32  tff(c_1686, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_1667])).
% 9.34/3.32  tff(c_1754, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1686])).
% 9.34/3.32  tff(c_2018, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2015, c_1754])).
% 9.34/3.32  tff(c_2052, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_76, c_72, c_2018])).
% 9.34/3.32  tff(c_2053, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1686])).
% 9.34/3.32  tff(c_2557, plain, (![C_357, D_354, E_353, B_355, A_356]: (k1_xboole_0=C_357 | v2_funct_1(D_354) | ~v2_funct_1(k1_partfun1(A_356, B_355, B_355, C_357, D_354, E_353)) | ~m1_subset_1(E_353, k1_zfmisc_1(k2_zfmisc_1(B_355, C_357))) | ~v1_funct_2(E_353, B_355, C_357) | ~v1_funct_1(E_353) | ~m1_subset_1(D_354, k1_zfmisc_1(k2_zfmisc_1(A_356, B_355))) | ~v1_funct_2(D_354, A_356, B_355) | ~v1_funct_1(D_354))), inference(cnfTransformation, [status(thm)], [f_160])).
% 9.34/3.32  tff(c_2561, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2053, c_2557])).
% 9.34/3.32  tff(c_2565, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_76, c_74, c_72, c_84, c_2561])).
% 9.34/3.32  tff(c_2566, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_152, c_2565])).
% 9.34/3.32  tff(c_30, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.34/3.32  tff(c_242, plain, (![B_79, A_80]: (v1_relat_1(B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(A_80)) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.34/3.32  tff(c_251, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_72, c_242])).
% 9.34/3.32  tff(c_263, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_251])).
% 9.34/3.32  tff(c_310, plain, (![C_81, B_82, A_83]: (v5_relat_1(C_81, B_82) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_83, B_82))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.34/3.32  tff(c_327, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_72, c_310])).
% 9.34/3.32  tff(c_557, plain, (![B_108, A_109]: (k2_relat_1(B_108)=A_109 | ~v2_funct_2(B_108, A_109) | ~v5_relat_1(B_108, A_109) | ~v1_relat_1(B_108))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.34/3.32  tff(c_575, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_327, c_557])).
% 9.34/3.32  tff(c_592, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_263, c_575])).
% 9.34/3.32  tff(c_600, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_592])).
% 9.34/3.32  tff(c_254, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_78, c_242])).
% 9.34/3.32  tff(c_266, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_254])).
% 9.34/3.32  tff(c_36, plain, (![A_23]: (k2_relat_1(k6_relat_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.34/3.32  tff(c_86, plain, (![A_23]: (k2_relat_1(k6_partfun1(A_23))=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_36])).
% 9.34/3.32  tff(c_1007, plain, (![D_170, F_167, A_166, E_169, B_171, C_168]: (m1_subset_1(k1_partfun1(A_166, B_171, C_168, D_170, E_169, F_167), k1_zfmisc_1(k2_zfmisc_1(A_166, D_170))) | ~m1_subset_1(F_167, k1_zfmisc_1(k2_zfmisc_1(C_168, D_170))) | ~v1_funct_1(F_167) | ~m1_subset_1(E_169, k1_zfmisc_1(k2_zfmisc_1(A_166, B_171))) | ~v1_funct_1(E_169))), inference(cnfTransformation, [status(thm)], [f_126])).
% 9.34/3.32  tff(c_690, plain, (![D_123, C_124, A_125, B_126]: (D_123=C_124 | ~r2_relset_1(A_125, B_126, C_124, D_123) | ~m1_subset_1(D_123, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.34/3.32  tff(c_700, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_70, c_690])).
% 9.34/3.32  tff(c_719, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_700])).
% 9.34/3.32  tff(c_764, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_719])).
% 9.34/3.32  tff(c_1013, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1007, c_764])).
% 9.34/3.32  tff(c_1045, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_76, c_72, c_1013])).
% 9.34/3.32  tff(c_1046, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_719])).
% 9.34/3.32  tff(c_1250, plain, (![B_205, E_200, D_203, C_202, F_204, A_201]: (k1_partfun1(A_201, B_205, C_202, D_203, E_200, F_204)=k5_relat_1(E_200, F_204) | ~m1_subset_1(F_204, k1_zfmisc_1(k2_zfmisc_1(C_202, D_203))) | ~v1_funct_1(F_204) | ~m1_subset_1(E_200, k1_zfmisc_1(k2_zfmisc_1(A_201, B_205))) | ~v1_funct_1(E_200))), inference(cnfTransformation, [status(thm)], [f_136])).
% 9.34/3.32  tff(c_1254, plain, (![A_201, B_205, E_200]: (k1_partfun1(A_201, B_205, '#skF_2', '#skF_1', E_200, '#skF_4')=k5_relat_1(E_200, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_200, k1_zfmisc_1(k2_zfmisc_1(A_201, B_205))) | ~v1_funct_1(E_200))), inference(resolution, [status(thm)], [c_72, c_1250])).
% 9.34/3.32  tff(c_1395, plain, (![A_228, B_229, E_230]: (k1_partfun1(A_228, B_229, '#skF_2', '#skF_1', E_230, '#skF_4')=k5_relat_1(E_230, '#skF_4') | ~m1_subset_1(E_230, k1_zfmisc_1(k2_zfmisc_1(A_228, B_229))) | ~v1_funct_1(E_230))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1254])).
% 9.34/3.32  tff(c_1407, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_1395])).
% 9.34/3.32  tff(c_1421, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1046, c_1407])).
% 9.34/3.32  tff(c_32, plain, (![A_20, B_22]: (r1_tarski(k2_relat_1(k5_relat_1(A_20, B_22)), k2_relat_1(B_22)) | ~v1_relat_1(B_22) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.34/3.32  tff(c_1428, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_1')), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1421, c_32])).
% 9.34/3.32  tff(c_1434, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_266, c_263, c_86, c_1428])).
% 9.34/3.32  tff(c_388, plain, (![B_93, A_94]: (r1_tarski(k2_relat_1(B_93), A_94) | ~v5_relat_1(B_93, A_94) | ~v1_relat_1(B_93))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.34/3.32  tff(c_4, plain, (![B_3, A_2]: (B_3=A_2 | ~r1_tarski(B_3, A_2) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.34/3.32  tff(c_411, plain, (![B_93, A_94]: (k2_relat_1(B_93)=A_94 | ~r1_tarski(A_94, k2_relat_1(B_93)) | ~v5_relat_1(B_93, A_94) | ~v1_relat_1(B_93))), inference(resolution, [status(thm)], [c_388, c_4])).
% 9.34/3.32  tff(c_1438, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1434, c_411])).
% 9.34/3.32  tff(c_1443, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_263, c_327, c_1438])).
% 9.34/3.32  tff(c_354, plain, (![B_87, A_88]: (v5_relat_1(B_87, A_88) | ~r1_tarski(k2_relat_1(B_87), A_88) | ~v1_relat_1(B_87))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.34/3.32  tff(c_369, plain, (![B_87]: (v5_relat_1(B_87, k2_relat_1(B_87)) | ~v1_relat_1(B_87))), inference(resolution, [status(thm)], [c_8, c_354])).
% 9.34/3.32  tff(c_521, plain, (![B_106]: (v2_funct_2(B_106, k2_relat_1(B_106)) | ~v5_relat_1(B_106, k2_relat_1(B_106)) | ~v1_relat_1(B_106))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.34/3.32  tff(c_542, plain, (![B_87]: (v2_funct_2(B_87, k2_relat_1(B_87)) | ~v1_relat_1(B_87))), inference(resolution, [status(thm)], [c_369, c_521])).
% 9.34/3.32  tff(c_1459, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1443, c_542])).
% 9.34/3.32  tff(c_1481, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_263, c_1459])).
% 9.34/3.32  tff(c_1483, plain, $false, inference(negUnitSimplification, [status(thm)], [c_600, c_1481])).
% 9.34/3.32  tff(c_1484, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_592])).
% 9.34/3.32  tff(c_26, plain, (![B_17, A_16]: (v5_relat_1(B_17, A_16) | ~r1_tarski(k2_relat_1(B_17), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.34/3.32  tff(c_1501, plain, (![A_16]: (v5_relat_1('#skF_4', A_16) | ~r1_tarski('#skF_1', A_16) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1484, c_26])).
% 9.34/3.32  tff(c_1576, plain, (![A_235]: (v5_relat_1('#skF_4', A_235) | ~r1_tarski('#skF_1', A_235))), inference(demodulation, [status(thm), theory('equality')], [c_263, c_1501])).
% 9.34/3.32  tff(c_12, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.34/3.32  tff(c_186, plain, (![B_72, A_73]: (~r1_xboole_0(B_72, A_73) | ~r1_tarski(B_72, A_73) | v1_xboole_0(B_72))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.34/3.32  tff(c_190, plain, (![A_5]: (~r1_tarski(A_5, k1_xboole_0) | v1_xboole_0(A_5))), inference(resolution, [status(thm)], [c_12, c_186])).
% 9.34/3.32  tff(c_409, plain, (![B_93]: (v1_xboole_0(k2_relat_1(B_93)) | ~v5_relat_1(B_93, k1_xboole_0) | ~v1_relat_1(B_93))), inference(resolution, [status(thm)], [c_388, c_190])).
% 9.34/3.32  tff(c_1492, plain, (v1_xboole_0('#skF_1') | ~v5_relat_1('#skF_4', k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1484, c_409])).
% 9.34/3.32  tff(c_1507, plain, (v1_xboole_0('#skF_1') | ~v5_relat_1('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_263, c_1492])).
% 9.34/3.32  tff(c_1539, plain, (~v5_relat_1('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1507])).
% 9.34/3.32  tff(c_1591, plain, (~r1_tarski('#skF_1', k1_xboole_0)), inference(resolution, [status(thm)], [c_1576, c_1539])).
% 9.34/3.32  tff(c_2581, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2566, c_1591])).
% 9.34/3.32  tff(c_2607, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_2581])).
% 9.34/3.32  tff(c_2608, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_1507])).
% 9.34/3.32  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.34/3.32  tff(c_2613, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_2608, c_2])).
% 9.34/3.32  tff(c_20, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.34/3.32  tff(c_2634, plain, (![B_9]: (k2_zfmisc_1('#skF_1', B_9)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2613, c_2613, c_20])).
% 9.34/3.32  tff(c_219, plain, (![B_77, A_78]: (v1_xboole_0(B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(A_78)) | ~v1_xboole_0(A_78))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.34/3.32  tff(c_237, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_78, c_219])).
% 9.34/3.32  tff(c_333, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_237])).
% 9.34/3.32  tff(c_2821, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2634, c_333])).
% 9.34/3.32  tff(c_2825, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2608, c_2821])).
% 9.34/3.32  tff(c_2826, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_237])).
% 9.34/3.32  tff(c_2831, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2826, c_2])).
% 9.34/3.32  tff(c_191, plain, (![A_74]: (~r1_tarski(A_74, k1_xboole_0) | v1_xboole_0(A_74))), inference(resolution, [status(thm)], [c_12, c_186])).
% 9.34/3.32  tff(c_200, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_191])).
% 9.34/3.32  tff(c_18, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.34/3.32  tff(c_153, plain, (![A_68]: (m1_subset_1(k6_partfun1(A_68), k1_zfmisc_1(k2_zfmisc_1(A_68, A_68))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_50])).
% 9.34/3.32  tff(c_157, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_153])).
% 9.34/3.32  tff(c_222, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_157, c_219])).
% 9.34/3.32  tff(c_234, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_222])).
% 9.34/3.32  tff(c_241, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_234, c_2])).
% 9.34/3.32  tff(c_283, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_241, c_84])).
% 9.34/3.32  tff(c_2835, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2831, c_283])).
% 9.34/3.32  tff(c_2848, plain, $false, inference(negUnitSimplification, [status(thm)], [c_152, c_2835])).
% 9.34/3.32  tff(c_2849, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_68])).
% 9.34/3.32  tff(c_3034, plain, (![B_393, A_394]: (v1_relat_1(B_393) | ~m1_subset_1(B_393, k1_zfmisc_1(A_394)) | ~v1_relat_1(A_394))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.34/3.32  tff(c_3043, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_72, c_3034])).
% 9.34/3.32  tff(c_3055, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3043])).
% 9.34/3.32  tff(c_3073, plain, (![C_396, B_397, A_398]: (v5_relat_1(C_396, B_397) | ~m1_subset_1(C_396, k1_zfmisc_1(k2_zfmisc_1(A_398, B_397))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.34/3.32  tff(c_3090, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_72, c_3073])).
% 9.34/3.32  tff(c_3046, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_78, c_3034])).
% 9.34/3.32  tff(c_3058, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3046])).
% 9.34/3.32  tff(c_3557, plain, (![A_454, F_457, D_456, E_453, C_455, B_458]: (k1_partfun1(A_454, B_458, C_455, D_456, E_453, F_457)=k5_relat_1(E_453, F_457) | ~m1_subset_1(F_457, k1_zfmisc_1(k2_zfmisc_1(C_455, D_456))) | ~v1_funct_1(F_457) | ~m1_subset_1(E_453, k1_zfmisc_1(k2_zfmisc_1(A_454, B_458))) | ~v1_funct_1(E_453))), inference(cnfTransformation, [status(thm)], [f_136])).
% 9.34/3.32  tff(c_3561, plain, (![A_454, B_458, E_453]: (k1_partfun1(A_454, B_458, '#skF_2', '#skF_1', E_453, '#skF_4')=k5_relat_1(E_453, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_453, k1_zfmisc_1(k2_zfmisc_1(A_454, B_458))) | ~v1_funct_1(E_453))), inference(resolution, [status(thm)], [c_72, c_3557])).
% 9.34/3.32  tff(c_3755, plain, (![A_481, B_482, E_483]: (k1_partfun1(A_481, B_482, '#skF_2', '#skF_1', E_483, '#skF_4')=k5_relat_1(E_483, '#skF_4') | ~m1_subset_1(E_483, k1_zfmisc_1(k2_zfmisc_1(A_481, B_482))) | ~v1_funct_1(E_483))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_3561])).
% 9.34/3.32  tff(c_3767, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_3755])).
% 9.34/3.32  tff(c_3781, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_3767])).
% 9.34/3.32  tff(c_56, plain, (![A_35, F_40, B_36, C_37, D_38, E_39]: (m1_subset_1(k1_partfun1(A_35, B_36, C_37, D_38, E_39, F_40), k1_zfmisc_1(k2_zfmisc_1(A_35, D_38))) | ~m1_subset_1(F_40, k1_zfmisc_1(k2_zfmisc_1(C_37, D_38))) | ~v1_funct_1(F_40) | ~m1_subset_1(E_39, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))) | ~v1_funct_1(E_39))), inference(cnfTransformation, [status(thm)], [f_126])).
% 9.34/3.32  tff(c_3883, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3781, c_56])).
% 9.34/3.32  tff(c_3887, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_76, c_72, c_3883])).
% 9.34/3.32  tff(c_3384, plain, (![D_433, C_434, A_435, B_436]: (D_433=C_434 | ~r2_relset_1(A_435, B_436, C_434, D_433) | ~m1_subset_1(D_433, k1_zfmisc_1(k2_zfmisc_1(A_435, B_436))) | ~m1_subset_1(C_434, k1_zfmisc_1(k2_zfmisc_1(A_435, B_436))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.34/3.32  tff(c_3392, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_70, c_3384])).
% 9.34/3.32  tff(c_3407, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_3392])).
% 9.34/3.32  tff(c_4193, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3887, c_3781, c_3781, c_3407])).
% 9.34/3.32  tff(c_4217, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_1')), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4193, c_32])).
% 9.34/3.32  tff(c_4225, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3058, c_3055, c_86, c_4217])).
% 9.34/3.32  tff(c_3115, plain, (![B_403, A_404]: (r1_tarski(k2_relat_1(B_403), A_404) | ~v5_relat_1(B_403, A_404) | ~v1_relat_1(B_403))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.34/3.32  tff(c_3134, plain, (![B_403, A_404]: (k2_relat_1(B_403)=A_404 | ~r1_tarski(A_404, k2_relat_1(B_403)) | ~v5_relat_1(B_403, A_404) | ~v1_relat_1(B_403))), inference(resolution, [status(thm)], [c_3115, c_4])).
% 9.34/3.32  tff(c_4229, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4225, c_3134])).
% 9.34/3.32  tff(c_4234, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3055, c_3090, c_4229])).
% 9.34/3.32  tff(c_3159, plain, (![B_411, A_412]: (v5_relat_1(B_411, A_412) | ~r1_tarski(k2_relat_1(B_411), A_412) | ~v1_relat_1(B_411))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.34/3.32  tff(c_3178, plain, (![B_411]: (v5_relat_1(B_411, k2_relat_1(B_411)) | ~v1_relat_1(B_411))), inference(resolution, [status(thm)], [c_8, c_3159])).
% 9.34/3.32  tff(c_3209, plain, (![B_417]: (v2_funct_2(B_417, k2_relat_1(B_417)) | ~v5_relat_1(B_417, k2_relat_1(B_417)) | ~v1_relat_1(B_417))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.34/3.32  tff(c_3230, plain, (![B_411]: (v2_funct_2(B_411, k2_relat_1(B_411)) | ~v1_relat_1(B_411))), inference(resolution, [status(thm)], [c_3178, c_3209])).
% 9.34/3.32  tff(c_4256, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4234, c_3230])).
% 9.34/3.32  tff(c_4279, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3055, c_4256])).
% 9.34/3.32  tff(c_4281, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2849, c_4279])).
% 9.34/3.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.34/3.32  
% 9.34/3.32  Inference rules
% 9.34/3.32  ----------------------
% 9.34/3.32  #Ref     : 0
% 9.34/3.32  #Sup     : 863
% 9.34/3.32  #Fact    : 0
% 9.34/3.32  #Define  : 0
% 9.34/3.32  #Split   : 21
% 9.34/3.32  #Chain   : 0
% 9.34/3.32  #Close   : 0
% 9.34/3.32  
% 9.34/3.32  Ordering : KBO
% 9.34/3.32  
% 9.34/3.32  Simplification rules
% 9.34/3.32  ----------------------
% 9.34/3.32  #Subsume      : 113
% 9.34/3.32  #Demod        : 869
% 9.34/3.32  #Tautology    : 281
% 9.34/3.32  #SimpNegUnit  : 5
% 9.34/3.32  #BackRed      : 102
% 9.34/3.32  
% 9.34/3.32  #Partial instantiations: 0
% 9.34/3.32  #Strategies tried      : 1
% 9.34/3.32  
% 9.34/3.32  Timing (in seconds)
% 9.34/3.32  ----------------------
% 9.34/3.33  Preprocessing        : 0.58
% 9.34/3.33  Parsing              : 0.30
% 9.34/3.33  CNF conversion       : 0.04
% 9.34/3.33  Main loop            : 1.78
% 9.34/3.33  Inferencing          : 0.65
% 9.34/3.33  Reduction            : 0.62
% 9.34/3.33  Demodulation         : 0.45
% 9.34/3.33  BG Simplification    : 0.06
% 9.34/3.33  Subsumption          : 0.30
% 9.34/3.33  Abstraction          : 0.07
% 9.34/3.33  MUC search           : 0.00
% 9.34/3.33  Cooper               : 0.00
% 9.34/3.33  Total                : 2.45
% 9.34/3.33  Index Insertion      : 0.00
% 9.34/3.33  Index Deletion       : 0.00
% 9.34/3.33  Index Matching       : 0.00
% 9.34/3.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
