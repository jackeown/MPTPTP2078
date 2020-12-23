%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:52 EST 2020

% Result     : Theorem 14.35s
% Output     : CNFRefutation 14.35s
% Verified   : 
% Statistics : Number of formulae       :  149 (3759 expanded)
%              Number of leaves         :   45 (1213 expanded)
%              Depth                    :   16
%              Number of atoms          :  274 (10192 expanded)
%              Number of equality atoms :   58 (1230 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_192,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & v3_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,C),k6_partfun1(A))
             => r2_relset_1(A,A,C,k2_funct_2(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_170,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( ( k2_relset_1(A,B,C) = B
              & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
              & v2_funct_1(C) )
           => ( A = k1_xboole_0
              | B = k1_xboole_0
              | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_126,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_41,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_116,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_1024,plain,(
    ! [A_192,B_193,D_194] :
      ( r2_relset_1(A_192,B_193,D_194,D_194)
      | ~ m1_subset_1(D_194,k1_zfmisc_1(k2_zfmisc_1(A_192,B_193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1038,plain,(
    r2_relset_1('#skF_2','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_1024])).

tff(c_74,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_301,plain,(
    ! [C_100,B_101,A_102] :
      ( v1_xboole_0(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(B_101,A_102)))
      | ~ v1_xboole_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_319,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_301])).

tff(c_325,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_319])).

tff(c_80,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_78,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_70,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_135,plain,(
    ! [C_63,A_64,B_65] :
      ( v1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_151,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_135])).

tff(c_176,plain,(
    ! [C_70,B_71,A_72] :
      ( v5_relat_1(C_70,B_71)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_72,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_194,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_176])).

tff(c_326,plain,(
    ! [B_104,A_105] :
      ( k2_relat_1(B_104) = A_105
      | ~ v2_funct_2(B_104,A_105)
      | ~ v5_relat_1(B_104,A_105)
      | ~ v1_relat_1(B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_335,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_194,c_326])).

tff(c_342,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_335])).

tff(c_835,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_342])).

tff(c_76,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_954,plain,(
    ! [C_184,B_185,A_186] :
      ( v2_funct_2(C_184,B_185)
      | ~ v3_funct_2(C_184,A_186,B_185)
      | ~ v1_funct_1(C_184)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_186,B_185))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_961,plain,
    ( v2_funct_2('#skF_3','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_954])).

tff(c_974,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_961])).

tff(c_976,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_835,c_974])).

tff(c_977,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_342])).

tff(c_1066,plain,(
    ! [A_201,B_202,C_203] :
      ( k2_relset_1(A_201,B_202,C_203) = k2_relat_1(C_203)
      | ~ m1_subset_1(C_203,k1_zfmisc_1(k2_zfmisc_1(A_201,B_202))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1073,plain,(
    k2_relset_1('#skF_2','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_1066])).

tff(c_1085,plain,(
    k2_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_977,c_1073])).

tff(c_1118,plain,(
    ! [C_207,A_208,B_209] :
      ( v2_funct_1(C_207)
      | ~ v3_funct_2(C_207,A_208,B_209)
      | ~ v1_funct_1(C_207)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(A_208,B_209))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1125,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_1118])).

tff(c_1138,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_1125])).

tff(c_64,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_1990,plain,(
    ! [C_287,D_288,B_289,A_290] :
      ( k2_funct_1(C_287) = D_288
      | k1_xboole_0 = B_289
      | k1_xboole_0 = A_290
      | ~ v2_funct_1(C_287)
      | ~ r2_relset_1(A_290,A_290,k1_partfun1(A_290,B_289,B_289,A_290,C_287,D_288),k6_partfun1(A_290))
      | k2_relset_1(A_290,B_289,C_287) != B_289
      | ~ m1_subset_1(D_288,k1_zfmisc_1(k2_zfmisc_1(B_289,A_290)))
      | ~ v1_funct_2(D_288,B_289,A_290)
      | ~ v1_funct_1(D_288)
      | ~ m1_subset_1(C_287,k1_zfmisc_1(k2_zfmisc_1(A_290,B_289)))
      | ~ v1_funct_2(C_287,A_290,B_289)
      | ~ v1_funct_1(C_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_1993,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_2','#skF_2','#skF_3') != '#skF_2'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_1990])).

tff(c_1996,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_74,c_72,c_70,c_66,c_1085,c_1138,c_1993])).

tff(c_1997,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1996])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2034,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1997,c_8])).

tff(c_2036,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_325,c_2034])).

tff(c_2037,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1996])).

tff(c_1448,plain,(
    ! [A_248,B_249] :
      ( k2_funct_2(A_248,B_249) = k2_funct_1(B_249)
      | ~ m1_subset_1(B_249,k1_zfmisc_1(k2_zfmisc_1(A_248,A_248)))
      | ~ v3_funct_2(B_249,A_248,A_248)
      | ~ v1_funct_2(B_249,A_248,A_248)
      | ~ v1_funct_1(B_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1459,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_1448])).

tff(c_1474,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_1459])).

tff(c_62,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4',k2_funct_2('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_1479,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1474,c_62])).

tff(c_2052,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2037,c_1479])).

tff(c_2070,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1038,c_2052])).

tff(c_2071,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_319])).

tff(c_103,plain,(
    ! [B_51,A_52] :
      ( ~ v1_xboole_0(B_51)
      | B_51 = A_52
      | ~ v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_106,plain,(
    ! [A_52] :
      ( k1_xboole_0 = A_52
      | ~ v1_xboole_0(A_52) ) ),
    inference(resolution,[status(thm)],[c_8,c_103])).

tff(c_2078,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2071,c_106])).

tff(c_2072,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_319])).

tff(c_2085,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2072,c_106])).

tff(c_2106,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2078,c_2085])).

tff(c_320,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_301])).

tff(c_2133,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2071,c_2106,c_320])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( ~ v1_xboole_0(B_7)
      | B_7 = A_6
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2086,plain,(
    ! [A_6] :
      ( A_6 = '#skF_2'
      | ~ v1_xboole_0(A_6) ) ),
    inference(resolution,[status(thm)],[c_2072,c_10])).

tff(c_2140,plain,(
    ! [A_295] :
      ( A_295 = '#skF_3'
      | ~ v1_xboole_0(A_295) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2106,c_2086])).

tff(c_2147,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2133,c_2140])).

tff(c_14,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2098,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2078,c_2078,c_14])).

tff(c_2187,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2147,c_2147,c_2098])).

tff(c_2116,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2106,c_2106,c_74])).

tff(c_2285,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2187,c_2147,c_2147,c_2147,c_2116])).

tff(c_2188,plain,(
    ! [A_299] : k2_zfmisc_1(A_299,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2147,c_2147,c_2098])).

tff(c_32,plain,(
    ! [A_25,B_26,D_28] :
      ( r2_relset_1(A_25,B_26,D_28,D_28)
      | ~ m1_subset_1(D_28,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3286,plain,(
    ! [A_455,D_456] :
      ( r2_relset_1(A_455,'#skF_4',D_456,D_456)
      | ~ m1_subset_1(D_456,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2188,c_32])).

tff(c_3292,plain,(
    ! [A_455] : r2_relset_1(A_455,'#skF_4','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_2285,c_3286])).

tff(c_2119,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2106,c_2106,c_70])).

tff(c_2222,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2147,c_2147,c_2119])).

tff(c_68,plain,(
    v3_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_2120,plain,(
    v3_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2106,c_2106,c_68])).

tff(c_2179,plain,(
    v3_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2147,c_2147,c_2120])).

tff(c_16,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2097,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_3',B_9) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2078,c_2078,c_16])).

tff(c_2223,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_4',B_9) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2147,c_2147,c_2097])).

tff(c_128,plain,(
    ! [A_60,B_61] :
      ( r2_hidden('#skF_1'(A_60,B_61),A_60)
      | r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_133,plain,(
    ! [A_60] : r1_tarski(A_60,A_60) ),
    inference(resolution,[status(thm)],[c_128,c_4])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3096,plain,(
    ! [A_435,B_436] :
      ( k2_funct_2(A_435,B_436) = k2_funct_1(B_436)
      | ~ m1_subset_1(B_436,k1_zfmisc_1(k2_zfmisc_1(A_435,A_435)))
      | ~ v3_funct_2(B_436,A_435,A_435)
      | ~ v1_funct_2(B_436,A_435,A_435)
      | ~ v1_funct_1(B_436) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_4918,plain,(
    ! [A_611,A_612] :
      ( k2_funct_2(A_611,A_612) = k2_funct_1(A_612)
      | ~ v3_funct_2(A_612,A_611,A_611)
      | ~ v1_funct_2(A_612,A_611,A_611)
      | ~ v1_funct_1(A_612)
      | ~ r1_tarski(A_612,k2_zfmisc_1(A_611,A_611)) ) ),
    inference(resolution,[status(thm)],[c_20,c_3096])).

tff(c_13788,plain,(
    ! [A_979] :
      ( k2_funct_2('#skF_4',A_979) = k2_funct_1(A_979)
      | ~ v3_funct_2(A_979,'#skF_4','#skF_4')
      | ~ v1_funct_2(A_979,'#skF_4','#skF_4')
      | ~ v1_funct_1(A_979)
      | ~ r1_tarski(A_979,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2223,c_4918])).

tff(c_13799,plain,
    ( k2_funct_2('#skF_4','#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_2179,c_13788])).

tff(c_13806,plain,(
    k2_funct_2('#skF_4','#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_72,c_2222,c_13799])).

tff(c_3398,plain,(
    ! [A_474,B_475] :
      ( m1_subset_1(k2_funct_2(A_474,B_475),k1_zfmisc_1(k2_zfmisc_1(A_474,A_474)))
      | ~ m1_subset_1(B_475,k1_zfmisc_1(k2_zfmisc_1(A_474,A_474)))
      | ~ v3_funct_2(B_475,A_474,A_474)
      | ~ v1_funct_2(B_475,A_474,A_474)
      | ~ v1_funct_1(B_475) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3459,plain,(
    ! [A_474,B_475] :
      ( r1_tarski(k2_funct_2(A_474,B_475),k2_zfmisc_1(A_474,A_474))
      | ~ m1_subset_1(B_475,k1_zfmisc_1(k2_zfmisc_1(A_474,A_474)))
      | ~ v3_funct_2(B_475,A_474,A_474)
      | ~ v1_funct_2(B_475,A_474,A_474)
      | ~ v1_funct_1(B_475) ) ),
    inference(resolution,[status(thm)],[c_3398,c_18])).

tff(c_13844,plain,
    ( r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_4','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
    | ~ v3_funct_2('#skF_4','#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_13806,c_3459])).

tff(c_13881,plain,(
    r1_tarski(k2_funct_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2222,c_2179,c_2285,c_2223,c_2223,c_13844])).

tff(c_2157,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2147,c_2078])).

tff(c_317,plain,(
    ! [C_100] :
      ( v1_xboole_0(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_301])).

tff(c_322,plain,(
    ! [C_100] :
      ( v1_xboole_0(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_317])).

tff(c_2316,plain,(
    ! [C_309] :
      ( v1_xboole_0(C_309)
      | ~ m1_subset_1(C_309,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2157,c_322])).

tff(c_2326,plain,(
    ! [A_10] :
      ( v1_xboole_0(A_10)
      | ~ r1_tarski(A_10,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_20,c_2316])).

tff(c_13965,plain,(
    v1_xboole_0(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_13881,c_2326])).

tff(c_2096,plain,(
    ! [A_52] :
      ( A_52 = '#skF_3'
      | ~ v1_xboole_0(A_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2078,c_106])).

tff(c_2277,plain,(
    ! [A_52] :
      ( A_52 = '#skF_4'
      | ~ v1_xboole_0(A_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2147,c_2096])).

tff(c_14000,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_13965,c_2277])).

tff(c_2115,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_4',k2_funct_2('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2106,c_2106,c_2106,c_62])).

tff(c_2991,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4',k2_funct_2('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2147,c_2147,c_2147,c_2147,c_2115])).

tff(c_13808,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4',k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13806,c_2991])).

tff(c_14020,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3292,c_14000,c_13808])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:06:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.35/5.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.35/5.19  
% 14.35/5.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.35/5.19  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 14.35/5.19  
% 14.35/5.19  %Foreground sorts:
% 14.35/5.19  
% 14.35/5.19  
% 14.35/5.19  %Background operators:
% 14.35/5.19  
% 14.35/5.19  
% 14.35/5.19  %Foreground operators:
% 14.35/5.19  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 14.35/5.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 14.35/5.19  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 14.35/5.19  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 14.35/5.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.35/5.19  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 14.35/5.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.35/5.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.35/5.19  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 14.35/5.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.35/5.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 14.35/5.19  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 14.35/5.19  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 14.35/5.19  tff('#skF_2', type, '#skF_2': $i).
% 14.35/5.19  tff('#skF_3', type, '#skF_3': $i).
% 14.35/5.19  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 14.35/5.19  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 14.35/5.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.35/5.19  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 14.35/5.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.35/5.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.35/5.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.35/5.19  tff('#skF_4', type, '#skF_4': $i).
% 14.35/5.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.35/5.19  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 14.35/5.19  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 14.35/5.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.35/5.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 14.35/5.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.35/5.19  
% 14.35/5.22  tff(f_192, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_2)).
% 14.35/5.22  tff(f_80, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 14.35/5.22  tff(f_68, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 14.35/5.22  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 14.35/5.22  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 14.35/5.22  tff(f_100, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 14.35/5.22  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 14.35/5.22  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 14.35/5.22  tff(f_170, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 14.35/5.22  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 14.35/5.22  tff(f_126, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 14.35/5.22  tff(f_41, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 14.35/5.22  tff(f_47, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 14.35/5.22  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 14.35/5.22  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 14.35/5.22  tff(f_116, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 14.35/5.22  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_192])).
% 14.35/5.22  tff(c_1024, plain, (![A_192, B_193, D_194]: (r2_relset_1(A_192, B_193, D_194, D_194) | ~m1_subset_1(D_194, k1_zfmisc_1(k2_zfmisc_1(A_192, B_193))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 14.35/5.22  tff(c_1038, plain, (r2_relset_1('#skF_2', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_66, c_1024])).
% 14.35/5.22  tff(c_74, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_192])).
% 14.35/5.22  tff(c_301, plain, (![C_100, B_101, A_102]: (v1_xboole_0(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(B_101, A_102))) | ~v1_xboole_0(A_102))), inference(cnfTransformation, [status(thm)], [f_68])).
% 14.35/5.22  tff(c_319, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_74, c_301])).
% 14.35/5.22  tff(c_325, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_319])).
% 14.35/5.22  tff(c_80, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_192])).
% 14.35/5.22  tff(c_78, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 14.35/5.22  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_192])).
% 14.35/5.22  tff(c_70, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 14.35/5.22  tff(c_135, plain, (![C_63, A_64, B_65]: (v1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 14.35/5.22  tff(c_151, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_135])).
% 14.35/5.22  tff(c_176, plain, (![C_70, B_71, A_72]: (v5_relat_1(C_70, B_71) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_72, B_71))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.35/5.22  tff(c_194, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_74, c_176])).
% 14.35/5.22  tff(c_326, plain, (![B_104, A_105]: (k2_relat_1(B_104)=A_105 | ~v2_funct_2(B_104, A_105) | ~v5_relat_1(B_104, A_105) | ~v1_relat_1(B_104))), inference(cnfTransformation, [status(thm)], [f_100])).
% 14.35/5.22  tff(c_335, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_194, c_326])).
% 14.35/5.22  tff(c_342, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_335])).
% 14.35/5.22  tff(c_835, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_342])).
% 14.35/5.22  tff(c_76, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 14.35/5.22  tff(c_954, plain, (![C_184, B_185, A_186]: (v2_funct_2(C_184, B_185) | ~v3_funct_2(C_184, A_186, B_185) | ~v1_funct_1(C_184) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_186, B_185))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 14.35/5.22  tff(c_961, plain, (v2_funct_2('#skF_3', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_954])).
% 14.35/5.22  tff(c_974, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_961])).
% 14.35/5.22  tff(c_976, plain, $false, inference(negUnitSimplification, [status(thm)], [c_835, c_974])).
% 14.35/5.22  tff(c_977, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_342])).
% 14.35/5.22  tff(c_1066, plain, (![A_201, B_202, C_203]: (k2_relset_1(A_201, B_202, C_203)=k2_relat_1(C_203) | ~m1_subset_1(C_203, k1_zfmisc_1(k2_zfmisc_1(A_201, B_202))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 14.35/5.22  tff(c_1073, plain, (k2_relset_1('#skF_2', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_1066])).
% 14.35/5.22  tff(c_1085, plain, (k2_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_977, c_1073])).
% 14.35/5.22  tff(c_1118, plain, (![C_207, A_208, B_209]: (v2_funct_1(C_207) | ~v3_funct_2(C_207, A_208, B_209) | ~v1_funct_1(C_207) | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(A_208, B_209))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 14.35/5.22  tff(c_1125, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_1118])).
% 14.35/5.22  tff(c_1138, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_1125])).
% 14.35/5.22  tff(c_64, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_192])).
% 14.35/5.22  tff(c_1990, plain, (![C_287, D_288, B_289, A_290]: (k2_funct_1(C_287)=D_288 | k1_xboole_0=B_289 | k1_xboole_0=A_290 | ~v2_funct_1(C_287) | ~r2_relset_1(A_290, A_290, k1_partfun1(A_290, B_289, B_289, A_290, C_287, D_288), k6_partfun1(A_290)) | k2_relset_1(A_290, B_289, C_287)!=B_289 | ~m1_subset_1(D_288, k1_zfmisc_1(k2_zfmisc_1(B_289, A_290))) | ~v1_funct_2(D_288, B_289, A_290) | ~v1_funct_1(D_288) | ~m1_subset_1(C_287, k1_zfmisc_1(k2_zfmisc_1(A_290, B_289))) | ~v1_funct_2(C_287, A_290, B_289) | ~v1_funct_1(C_287))), inference(cnfTransformation, [status(thm)], [f_170])).
% 14.35/5.22  tff(c_1993, plain, (k2_funct_1('#skF_3')='#skF_4' | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_2', '#skF_2', '#skF_3')!='#skF_2' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_1990])).
% 14.35/5.22  tff(c_1996, plain, (k2_funct_1('#skF_3')='#skF_4' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_74, c_72, c_70, c_66, c_1085, c_1138, c_1993])).
% 14.35/5.22  tff(c_1997, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1996])).
% 14.35/5.22  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.35/5.22  tff(c_2034, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1997, c_8])).
% 14.35/5.22  tff(c_2036, plain, $false, inference(negUnitSimplification, [status(thm)], [c_325, c_2034])).
% 14.35/5.22  tff(c_2037, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_1996])).
% 14.35/5.22  tff(c_1448, plain, (![A_248, B_249]: (k2_funct_2(A_248, B_249)=k2_funct_1(B_249) | ~m1_subset_1(B_249, k1_zfmisc_1(k2_zfmisc_1(A_248, A_248))) | ~v3_funct_2(B_249, A_248, A_248) | ~v1_funct_2(B_249, A_248, A_248) | ~v1_funct_1(B_249))), inference(cnfTransformation, [status(thm)], [f_126])).
% 14.35/5.22  tff(c_1459, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_1448])).
% 14.35/5.22  tff(c_1474, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_1459])).
% 14.35/5.22  tff(c_62, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', k2_funct_2('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_192])).
% 14.35/5.22  tff(c_1479, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1474, c_62])).
% 14.35/5.22  tff(c_2052, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2037, c_1479])).
% 14.35/5.22  tff(c_2070, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1038, c_2052])).
% 14.35/5.22  tff(c_2071, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_319])).
% 14.35/5.22  tff(c_103, plain, (![B_51, A_52]: (~v1_xboole_0(B_51) | B_51=A_52 | ~v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.35/5.22  tff(c_106, plain, (![A_52]: (k1_xboole_0=A_52 | ~v1_xboole_0(A_52))), inference(resolution, [status(thm)], [c_8, c_103])).
% 14.35/5.22  tff(c_2078, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2071, c_106])).
% 14.35/5.22  tff(c_2072, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_319])).
% 14.35/5.22  tff(c_2085, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_2072, c_106])).
% 14.35/5.22  tff(c_2106, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2078, c_2085])).
% 14.35/5.22  tff(c_320, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_66, c_301])).
% 14.35/5.22  tff(c_2133, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2071, c_2106, c_320])).
% 14.35/5.22  tff(c_10, plain, (![B_7, A_6]: (~v1_xboole_0(B_7) | B_7=A_6 | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.35/5.22  tff(c_2086, plain, (![A_6]: (A_6='#skF_2' | ~v1_xboole_0(A_6))), inference(resolution, [status(thm)], [c_2072, c_10])).
% 14.35/5.22  tff(c_2140, plain, (![A_295]: (A_295='#skF_3' | ~v1_xboole_0(A_295))), inference(demodulation, [status(thm), theory('equality')], [c_2106, c_2086])).
% 14.35/5.22  tff(c_2147, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_2133, c_2140])).
% 14.35/5.22  tff(c_14, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.35/5.22  tff(c_2098, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2078, c_2078, c_14])).
% 14.35/5.22  tff(c_2187, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2147, c_2147, c_2098])).
% 14.35/5.22  tff(c_2116, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2106, c_2106, c_74])).
% 14.35/5.22  tff(c_2285, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2187, c_2147, c_2147, c_2147, c_2116])).
% 14.35/5.22  tff(c_2188, plain, (![A_299]: (k2_zfmisc_1(A_299, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2147, c_2147, c_2098])).
% 14.35/5.22  tff(c_32, plain, (![A_25, B_26, D_28]: (r2_relset_1(A_25, B_26, D_28, D_28) | ~m1_subset_1(D_28, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 14.35/5.22  tff(c_3286, plain, (![A_455, D_456]: (r2_relset_1(A_455, '#skF_4', D_456, D_456) | ~m1_subset_1(D_456, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2188, c_32])).
% 14.35/5.22  tff(c_3292, plain, (![A_455]: (r2_relset_1(A_455, '#skF_4', '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_2285, c_3286])).
% 14.35/5.22  tff(c_2119, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2106, c_2106, c_70])).
% 14.35/5.22  tff(c_2222, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2147, c_2147, c_2119])).
% 14.35/5.22  tff(c_68, plain, (v3_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 14.35/5.22  tff(c_2120, plain, (v3_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2106, c_2106, c_68])).
% 14.35/5.22  tff(c_2179, plain, (v3_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2147, c_2147, c_2120])).
% 14.35/5.22  tff(c_16, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.35/5.22  tff(c_2097, plain, (![B_9]: (k2_zfmisc_1('#skF_3', B_9)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2078, c_2078, c_16])).
% 14.35/5.22  tff(c_2223, plain, (![B_9]: (k2_zfmisc_1('#skF_4', B_9)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2147, c_2147, c_2097])).
% 14.35/5.22  tff(c_128, plain, (![A_60, B_61]: (r2_hidden('#skF_1'(A_60, B_61), A_60) | r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.35/5.22  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.35/5.22  tff(c_133, plain, (![A_60]: (r1_tarski(A_60, A_60))), inference(resolution, [status(thm)], [c_128, c_4])).
% 14.35/5.22  tff(c_20, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.35/5.22  tff(c_3096, plain, (![A_435, B_436]: (k2_funct_2(A_435, B_436)=k2_funct_1(B_436) | ~m1_subset_1(B_436, k1_zfmisc_1(k2_zfmisc_1(A_435, A_435))) | ~v3_funct_2(B_436, A_435, A_435) | ~v1_funct_2(B_436, A_435, A_435) | ~v1_funct_1(B_436))), inference(cnfTransformation, [status(thm)], [f_126])).
% 14.35/5.22  tff(c_4918, plain, (![A_611, A_612]: (k2_funct_2(A_611, A_612)=k2_funct_1(A_612) | ~v3_funct_2(A_612, A_611, A_611) | ~v1_funct_2(A_612, A_611, A_611) | ~v1_funct_1(A_612) | ~r1_tarski(A_612, k2_zfmisc_1(A_611, A_611)))), inference(resolution, [status(thm)], [c_20, c_3096])).
% 14.35/5.22  tff(c_13788, plain, (![A_979]: (k2_funct_2('#skF_4', A_979)=k2_funct_1(A_979) | ~v3_funct_2(A_979, '#skF_4', '#skF_4') | ~v1_funct_2(A_979, '#skF_4', '#skF_4') | ~v1_funct_1(A_979) | ~r1_tarski(A_979, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2223, c_4918])).
% 14.35/5.22  tff(c_13799, plain, (k2_funct_2('#skF_4', '#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_4', '#skF_4') | ~v1_funct_1('#skF_4') | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_2179, c_13788])).
% 14.35/5.22  tff(c_13806, plain, (k2_funct_2('#skF_4', '#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_72, c_2222, c_13799])).
% 14.35/5.22  tff(c_3398, plain, (![A_474, B_475]: (m1_subset_1(k2_funct_2(A_474, B_475), k1_zfmisc_1(k2_zfmisc_1(A_474, A_474))) | ~m1_subset_1(B_475, k1_zfmisc_1(k2_zfmisc_1(A_474, A_474))) | ~v3_funct_2(B_475, A_474, A_474) | ~v1_funct_2(B_475, A_474, A_474) | ~v1_funct_1(B_475))), inference(cnfTransformation, [status(thm)], [f_116])).
% 14.35/5.22  tff(c_18, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.35/5.22  tff(c_3459, plain, (![A_474, B_475]: (r1_tarski(k2_funct_2(A_474, B_475), k2_zfmisc_1(A_474, A_474)) | ~m1_subset_1(B_475, k1_zfmisc_1(k2_zfmisc_1(A_474, A_474))) | ~v3_funct_2(B_475, A_474, A_474) | ~v1_funct_2(B_475, A_474, A_474) | ~v1_funct_1(B_475))), inference(resolution, [status(thm)], [c_3398, c_18])).
% 14.35/5.22  tff(c_13844, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_4', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~v3_funct_2('#skF_4', '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', '#skF_4', '#skF_4') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_13806, c_3459])).
% 14.35/5.22  tff(c_13881, plain, (r1_tarski(k2_funct_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2222, c_2179, c_2285, c_2223, c_2223, c_13844])).
% 14.35/5.22  tff(c_2157, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2147, c_2078])).
% 14.35/5.22  tff(c_317, plain, (![C_100]: (v1_xboole_0(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_301])).
% 14.35/5.22  tff(c_322, plain, (![C_100]: (v1_xboole_0(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_317])).
% 14.35/5.22  tff(c_2316, plain, (![C_309]: (v1_xboole_0(C_309) | ~m1_subset_1(C_309, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2157, c_322])).
% 14.35/5.22  tff(c_2326, plain, (![A_10]: (v1_xboole_0(A_10) | ~r1_tarski(A_10, '#skF_4'))), inference(resolution, [status(thm)], [c_20, c_2316])).
% 14.35/5.22  tff(c_13965, plain, (v1_xboole_0(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_13881, c_2326])).
% 14.35/5.22  tff(c_2096, plain, (![A_52]: (A_52='#skF_3' | ~v1_xboole_0(A_52))), inference(demodulation, [status(thm), theory('equality')], [c_2078, c_106])).
% 14.35/5.22  tff(c_2277, plain, (![A_52]: (A_52='#skF_4' | ~v1_xboole_0(A_52))), inference(demodulation, [status(thm), theory('equality')], [c_2147, c_2096])).
% 14.35/5.22  tff(c_14000, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_13965, c_2277])).
% 14.35/5.22  tff(c_2115, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_4', k2_funct_2('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2106, c_2106, c_2106, c_62])).
% 14.35/5.22  tff(c_2991, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', k2_funct_2('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2147, c_2147, c_2147, c_2147, c_2115])).
% 14.35/5.22  tff(c_13808, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_13806, c_2991])).
% 14.35/5.22  tff(c_14020, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3292, c_14000, c_13808])).
% 14.35/5.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.35/5.22  
% 14.35/5.22  Inference rules
% 14.35/5.22  ----------------------
% 14.35/5.22  #Ref     : 0
% 14.35/5.22  #Sup     : 3548
% 14.35/5.22  #Fact    : 0
% 14.35/5.22  #Define  : 0
% 14.35/5.22  #Split   : 40
% 14.35/5.22  #Chain   : 0
% 14.35/5.22  #Close   : 0
% 14.35/5.22  
% 14.35/5.22  Ordering : KBO
% 14.35/5.22  
% 14.35/5.22  Simplification rules
% 14.35/5.22  ----------------------
% 14.35/5.22  #Subsume      : 1311
% 14.35/5.22  #Demod        : 2793
% 14.35/5.22  #Tautology    : 1123
% 14.35/5.22  #SimpNegUnit  : 53
% 14.35/5.22  #BackRed      : 123
% 14.35/5.22  
% 14.35/5.22  #Partial instantiations: 0
% 14.35/5.22  #Strategies tried      : 1
% 14.35/5.22  
% 14.35/5.22  Timing (in seconds)
% 14.35/5.22  ----------------------
% 14.35/5.22  Preprocessing        : 0.62
% 14.35/5.22  Parsing              : 0.32
% 14.35/5.22  CNF conversion       : 0.05
% 14.35/5.22  Main loop            : 3.72
% 14.35/5.22  Inferencing          : 1.16
% 14.35/5.22  Reduction            : 1.22
% 14.35/5.22  Demodulation         : 0.91
% 14.35/5.22  BG Simplification    : 0.12
% 14.35/5.22  Subsumption          : 0.94
% 14.35/5.22  Abstraction          : 0.15
% 14.35/5.22  MUC search           : 0.00
% 14.35/5.22  Cooper               : 0.00
% 14.35/5.22  Total                : 4.41
% 14.35/5.22  Index Insertion      : 0.00
% 14.35/5.22  Index Deletion       : 0.00
% 14.35/5.22  Index Matching       : 0.00
% 14.35/5.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
