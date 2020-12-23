%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:26 EST 2020

% Result     : Theorem 6.33s
% Output     : CNFRefutation 6.66s
% Verified   : 
% Statistics : Number of formulae       :  243 (2099 expanded)
%              Number of leaves         :   43 ( 666 expanded)
%              Depth                    :   13
%              Number of atoms          :  406 (5539 expanded)
%              Number of equality atoms :  131 (1282 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_185,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_128,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_108,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_90,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ( v1_xboole_0(k4_relat_1(A))
        & v1_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_98,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_124,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_146,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_168,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_156,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_66,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_92,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_237,plain,(
    ! [C_51,A_52,B_53] :
      ( v1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_249,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_237])).

tff(c_96,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_90,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_88,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_3985,plain,(
    ! [A_201,B_202,C_203] :
      ( k2_relset_1(A_201,B_202,C_203) = k2_relat_1(C_203)
      | ~ m1_subset_1(C_203,k1_zfmisc_1(k2_zfmisc_1(A_201,B_202))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_3991,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_3985])).

tff(c_4004,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_3991])).

tff(c_46,plain,(
    ! [A_18] :
      ( k1_relat_1(k2_funct_1(A_18)) = k2_relat_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_314,plain,(
    ! [A_67] :
      ( k4_relat_1(A_67) = k2_funct_1(A_67)
      | ~ v2_funct_1(A_67)
      | ~ v1_funct_1(A_67)
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_320,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_314])).

tff(c_324,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_96,c_320])).

tff(c_24,plain,(
    ! [A_13] :
      ( v1_xboole_0(k4_relat_1(A_13))
      | ~ v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_334,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_24])).

tff(c_342,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_334])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_40,plain,(
    ! [A_17] :
      ( v1_funct_1(k2_funct_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_86,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_252,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_255,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_252])).

tff(c_259,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_96,c_255])).

tff(c_260,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_280,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_260])).

tff(c_474,plain,(
    ! [A_81,B_82,C_83] :
      ( k2_relset_1(A_81,B_82,C_83) = k2_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_480,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_474])).

tff(c_493,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_480])).

tff(c_42,plain,(
    ! [A_17] :
      ( v1_relat_1(k2_funct_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_261,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_94,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_402,plain,(
    ! [A_71,B_72,C_73] :
      ( k1_relset_1(A_71,B_72,C_73) = k1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_416,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_402])).

tff(c_966,plain,(
    ! [B_117,A_118,C_119] :
      ( k1_xboole_0 = B_117
      | k1_relset_1(A_118,B_117,C_119) = A_118
      | ~ v1_funct_2(C_119,A_118,B_117)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_118,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_978,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_92,c_966])).

tff(c_996,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_416,c_978])).

tff(c_1000,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_996])).

tff(c_44,plain,(
    ! [A_18] :
      ( k2_relat_1(k2_funct_1(A_18)) = k1_relat_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_745,plain,(
    ! [B_105,A_106] :
      ( m1_subset_1(B_105,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_105),A_106)))
      | ~ r1_tarski(k2_relat_1(B_105),A_106)
      | ~ v1_funct_1(B_105)
      | ~ v1_relat_1(B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_16,plain,(
    ! [B_8,A_6] :
      ( v1_xboole_0(B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_6))
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1133,plain,(
    ! [B_124,A_125] :
      ( v1_xboole_0(B_124)
      | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(B_124),A_125))
      | ~ r1_tarski(k2_relat_1(B_124),A_125)
      | ~ v1_funct_1(B_124)
      | ~ v1_relat_1(B_124) ) ),
    inference(resolution,[status(thm)],[c_745,c_16])).

tff(c_1143,plain,(
    ! [B_124] :
      ( v1_xboole_0(B_124)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ r1_tarski(k2_relat_1(B_124),k1_xboole_0)
      | ~ v1_funct_1(B_124)
      | ~ v1_relat_1(B_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1133])).

tff(c_1284,plain,(
    ! [B_137] :
      ( v1_xboole_0(B_137)
      | ~ r1_tarski(k2_relat_1(B_137),k1_xboole_0)
      | ~ v1_funct_1(B_137)
      | ~ v1_relat_1(B_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1143])).

tff(c_2481,plain,(
    ! [A_162] :
      ( v1_xboole_0(k2_funct_1(A_162))
      | ~ r1_tarski(k1_relat_1(A_162),k1_xboole_0)
      | ~ v1_funct_1(k2_funct_1(A_162))
      | ~ v1_relat_1(k2_funct_1(A_162))
      | ~ v2_funct_1(A_162)
      | ~ v1_funct_1(A_162)
      | ~ v1_relat_1(A_162) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1284])).

tff(c_2484,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ r1_tarski('#skF_1',k1_xboole_0)
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1000,c_2481])).

tff(c_2492,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ r1_tarski('#skF_1',k1_xboole_0)
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_96,c_90,c_261,c_2484])).

tff(c_2495,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2492])).

tff(c_2498,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_2495])).

tff(c_2502,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_96,c_2498])).

tff(c_2504,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2492])).

tff(c_442,plain,(
    ! [A_80] :
      ( m1_subset_1(A_80,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_80),k2_relat_1(A_80))))
      | ~ v1_funct_1(A_80)
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_3305,plain,(
    ! [A_172] :
      ( m1_subset_1(k2_funct_1(A_172),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_172)),k1_relat_1(A_172))))
      | ~ v1_funct_1(k2_funct_1(A_172))
      | ~ v1_relat_1(k2_funct_1(A_172))
      | ~ v2_funct_1(A_172)
      | ~ v1_funct_1(A_172)
      | ~ v1_relat_1(A_172) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_442])).

tff(c_3358,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1000,c_3305])).

tff(c_3398,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_96,c_90,c_2504,c_261,c_3358])).

tff(c_3429,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_3398])).

tff(c_3442,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_96,c_90,c_493,c_3429])).

tff(c_3444,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_280,c_3442])).

tff(c_3445,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_996])).

tff(c_6,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3476,plain,(
    ! [A_2] : r1_tarski('#skF_2',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3445,c_6])).

tff(c_777,plain,(
    ! [B_107] :
      ( m1_subset_1(B_107,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(B_107),k1_xboole_0)
      | ~ v1_funct_1(B_107)
      | ~ v1_relat_1(B_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_745])).

tff(c_780,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_2',k1_xboole_0)
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_777])).

tff(c_788,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_96,c_780])).

tff(c_791,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_788])).

tff(c_3451,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3445,c_791])).

tff(c_3582,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3476,c_3451])).

tff(c_3583,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_788])).

tff(c_3599,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3583,c_16])).

tff(c_3613,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3599])).

tff(c_3615,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_342,c_3613])).

tff(c_3617,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_334])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_3633,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3617,c_4])).

tff(c_14,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3646,plain,(
    ! [A_5] : m1_subset_1('#skF_3',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3633,c_14])).

tff(c_154,plain,(
    ! [A_44] :
      ( v1_xboole_0(k4_relat_1(A_44))
      | ~ v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_165,plain,(
    ! [A_44] :
      ( k4_relat_1(A_44) = k1_xboole_0
      | ~ v1_xboole_0(A_44) ) ),
    inference(resolution,[status(thm)],[c_154,c_4])).

tff(c_3630,plain,(
    k4_relat_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3617,c_165])).

tff(c_3684,plain,(
    k4_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3633,c_3630])).

tff(c_3685,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3684,c_324])).

tff(c_3707,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3685,c_280])).

tff(c_3847,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3646,c_3707])).

tff(c_3848,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_3849,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_4016,plain,(
    ! [A_204,B_205,C_206] :
      ( k1_relset_1(A_204,B_205,C_206) = k1_relat_1(C_206)
      | ~ m1_subset_1(C_206,k1_zfmisc_1(k2_zfmisc_1(A_204,B_205))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_4033,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3849,c_4016])).

tff(c_4396,plain,(
    ! [B_238,C_239,A_240] :
      ( k1_xboole_0 = B_238
      | v1_funct_2(C_239,A_240,B_238)
      | k1_relset_1(A_240,B_238,C_239) != A_240
      | ~ m1_subset_1(C_239,k1_zfmisc_1(k2_zfmisc_1(A_240,B_238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_4408,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_3849,c_4396])).

tff(c_4428,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4033,c_4408])).

tff(c_4429,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_3848,c_4428])).

tff(c_4435,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4429])).

tff(c_4438,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_4435])).

tff(c_4441,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_96,c_90,c_4004,c_4438])).

tff(c_4442,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4429])).

tff(c_4473,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4442,c_2])).

tff(c_4466,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4442,c_4442,c_10])).

tff(c_3856,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_3849,c_16])).

tff(c_3858,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_3856])).

tff(c_4788,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4466,c_3858])).

tff(c_4792,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4473,c_4788])).

tff(c_4794,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_3856])).

tff(c_4827,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4794,c_4])).

tff(c_4867,plain,(
    ! [B_248,A_249] :
      ( k1_xboole_0 = B_248
      | k1_xboole_0 = A_249
      | k2_zfmisc_1(A_249,B_248) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4877,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_4827,c_4867])).

tff(c_4882,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4877])).

tff(c_4900,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4882,c_2])).

tff(c_4893,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4882,c_4882,c_10])).

tff(c_269,plain,(
    ! [B_55,A_56] :
      ( v1_xboole_0(B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_56))
      | ~ v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_276,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_92,c_269])).

tff(c_279,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_276])).

tff(c_5043,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4893,c_279])).

tff(c_5047,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4900,c_5043])).

tff(c_5048,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4877])).

tff(c_5067,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5048,c_2])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_5062,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5048,c_5048,c_12])).

tff(c_5228,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5062,c_279])).

tff(c_5232,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5067,c_5228])).

tff(c_5233,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_276])).

tff(c_5250,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_5233,c_4])).

tff(c_5738,plain,(
    ! [A_2] : r1_tarski('#skF_3',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5250,c_6])).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_5737,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5250,c_5250,c_26])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_5740,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5250,c_5250,c_28])).

tff(c_6512,plain,(
    ! [B_362,A_363] :
      ( v1_funct_2(B_362,k1_relat_1(B_362),A_363)
      | ~ r1_tarski(k2_relat_1(B_362),A_363)
      | ~ v1_funct_1(B_362)
      | ~ v1_relat_1(B_362) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_6521,plain,(
    ! [A_363] :
      ( v1_funct_2('#skF_3','#skF_3',A_363)
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_363)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5740,c_6512])).

tff(c_6524,plain,(
    ! [A_363] : v1_funct_2('#skF_3','#skF_3',A_363) ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_96,c_5738,c_5737,c_6521])).

tff(c_5736,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_3',B_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5250,c_5250,c_12])).

tff(c_5234,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_276])).

tff(c_5800,plain,(
    ! [A_303] :
      ( A_303 = '#skF_3'
      | ~ v1_xboole_0(A_303) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5250,c_4])).

tff(c_5810,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_5234,c_5800])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_5919,plain,(
    ! [B_311,A_312] :
      ( B_311 = '#skF_3'
      | A_312 = '#skF_3'
      | k2_zfmisc_1(A_312,B_311) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5250,c_5250,c_5250,c_8])).

tff(c_5929,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_5810,c_5919])).

tff(c_5934,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_5929])).

tff(c_5955,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5934,c_5233])).

tff(c_5734,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5250,c_5250,c_10])).

tff(c_5946,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5934,c_5934,c_5734])).

tff(c_5261,plain,(
    ! [A_5] : m1_subset_1('#skF_3',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5250,c_14])).

tff(c_5247,plain,(
    k4_relat_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5233,c_165])).

tff(c_5278,plain,(
    k4_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5250,c_5247])).

tff(c_5710,plain,(
    ! [A_299] :
      ( k4_relat_1(A_299) = k2_funct_1(A_299)
      | ~ v2_funct_1(A_299)
      | ~ v1_funct_1(A_299)
      | ~ v1_relat_1(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_5716,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_5710])).

tff(c_5720,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_96,c_5278,c_5716])).

tff(c_5262,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_3',B_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5250,c_5250,c_12])).

tff(c_5343,plain,(
    ! [A_275] :
      ( A_275 = '#skF_3'
      | ~ v1_xboole_0(A_275) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5250,c_4])).

tff(c_5353,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_5234,c_5343])).

tff(c_5436,plain,(
    ! [B_282,A_283] :
      ( B_282 = '#skF_3'
      | A_283 = '#skF_3'
      | k2_zfmisc_1(A_283,B_282) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5250,c_5250,c_5250,c_8])).

tff(c_5446,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_5353,c_5436])).

tff(c_5451,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_5446])).

tff(c_5458,plain,(
    ! [A_5] : m1_subset_1('#skF_1',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5451,c_5261])).

tff(c_5467,plain,(
    k4_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5451,c_5451,c_5278])).

tff(c_5472,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5451,c_249])).

tff(c_5476,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5451,c_96])).

tff(c_5475,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5451,c_90])).

tff(c_5495,plain,(
    ! [A_284] :
      ( k4_relat_1(A_284) = k2_funct_1(A_284)
      | ~ v2_funct_1(A_284)
      | ~ v1_funct_1(A_284)
      | ~ v1_relat_1(A_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_5498,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_5475,c_5495])).

tff(c_5504,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5472,c_5476,c_5498])).

tff(c_5594,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5467,c_5504])).

tff(c_5260,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5250,c_5250,c_10])).

tff(c_5461,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5451,c_5451,c_5260])).

tff(c_5253,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_260])).

tff(c_5464,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5451,c_5253])).

tff(c_5681,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5458,c_5594,c_5461,c_5464])).

tff(c_5682,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5446])).

tff(c_5685,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5682,c_5253])).

tff(c_5689,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5262,c_5685])).

tff(c_5721,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5720,c_5689])).

tff(c_5725,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5261,c_5721])).

tff(c_5727,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_5850,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_5727,c_16])).

tff(c_5917,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_5850])).

tff(c_6071,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5946,c_5917])).

tff(c_6074,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5955,c_6071])).

tff(c_6075,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5929])).

tff(c_6077,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6075,c_5917])).

tff(c_6085,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5233,c_5736,c_6077])).

tff(c_6087,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_5850])).

tff(c_5733,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5250,c_4])).

tff(c_6142,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6087,c_5733])).

tff(c_6158,plain,(
    ! [B_323,A_324] :
      ( B_323 = '#skF_3'
      | A_324 = '#skF_3'
      | k2_zfmisc_1(A_324,B_323) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5250,c_5250,c_5250,c_8])).

tff(c_6171,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_6142,c_6158])).

tff(c_6178,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_6171])).

tff(c_6086,plain,(
    v1_xboole_0(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_5850])).

tff(c_6101,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6086,c_5733])).

tff(c_5726,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_6109,plain,(
    ~ v1_funct_2('#skF_3','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6101,c_5726])).

tff(c_6300,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6178,c_6109])).

tff(c_6528,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6524,c_6300])).

tff(c_6529,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_6171])).

tff(c_6530,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6171])).

tff(c_6561,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6529,c_6530])).

tff(c_62,plain,(
    ! [A_29] :
      ( v1_funct_2(k1_xboole_0,A_29,k1_xboole_0)
      | k1_xboole_0 = A_29
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_29,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_98,plain,(
    ! [A_29] :
      ( v1_funct_2(k1_xboole_0,A_29,k1_xboole_0)
      | k1_xboole_0 = A_29 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_62])).

tff(c_5730,plain,(
    ! [A_29] :
      ( v1_funct_2('#skF_3',A_29,'#skF_3')
      | A_29 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5250,c_5250,c_5250,c_98])).

tff(c_6746,plain,(
    ! [A_378] :
      ( v1_funct_2('#skF_1',A_378,'#skF_1')
      | A_378 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6529,c_6529,c_6529,c_5730])).

tff(c_6531,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6529,c_6109])).

tff(c_6749,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6746,c_6531])).

tff(c_6753,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6561,c_6749])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:47:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.33/2.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.33/2.29  
% 6.33/2.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.33/2.29  %$ v1_funct_2 > v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.33/2.29  
% 6.33/2.29  %Foreground sorts:
% 6.33/2.29  
% 6.33/2.29  
% 6.33/2.29  %Background operators:
% 6.33/2.29  
% 6.33/2.29  
% 6.33/2.29  %Foreground operators:
% 6.33/2.29  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.33/2.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.33/2.29  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.33/2.29  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.33/2.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.33/2.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.33/2.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.33/2.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.33/2.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.33/2.29  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 6.33/2.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.33/2.29  tff('#skF_2', type, '#skF_2': $i).
% 6.33/2.29  tff('#skF_3', type, '#skF_3': $i).
% 6.33/2.29  tff('#skF_1', type, '#skF_1': $i).
% 6.33/2.29  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.33/2.29  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.33/2.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.33/2.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.33/2.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.33/2.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.33/2.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.33/2.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.33/2.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.33/2.29  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 6.33/2.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.33/2.29  
% 6.66/2.32  tff(f_185, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 6.66/2.32  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.66/2.32  tff(f_128, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.66/2.32  tff(f_108, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 6.66/2.32  tff(f_90, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 6.66/2.32  tff(f_63, axiom, (![A]: (v1_xboole_0(A) => (v1_xboole_0(k4_relat_1(A)) & v1_relat_1(k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_relat_1)).
% 6.66/2.32  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.66/2.32  tff(f_98, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 6.66/2.32  tff(f_124, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.66/2.32  tff(f_146, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.66/2.32  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.66/2.32  tff(f_168, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 6.66/2.32  tff(f_47, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 6.66/2.32  tff(f_156, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 6.66/2.32  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.66/2.32  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 6.66/2.32  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 6.66/2.32  tff(f_66, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 6.66/2.32  tff(c_92, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_185])).
% 6.66/2.32  tff(c_237, plain, (![C_51, A_52, B_53]: (v1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.66/2.32  tff(c_249, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_237])).
% 6.66/2.32  tff(c_96, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_185])).
% 6.66/2.32  tff(c_90, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_185])).
% 6.66/2.32  tff(c_88, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_185])).
% 6.66/2.32  tff(c_3985, plain, (![A_201, B_202, C_203]: (k2_relset_1(A_201, B_202, C_203)=k2_relat_1(C_203) | ~m1_subset_1(C_203, k1_zfmisc_1(k2_zfmisc_1(A_201, B_202))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.66/2.32  tff(c_3991, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_3985])).
% 6.66/2.32  tff(c_4004, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_3991])).
% 6.66/2.32  tff(c_46, plain, (![A_18]: (k1_relat_1(k2_funct_1(A_18))=k2_relat_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.66/2.32  tff(c_314, plain, (![A_67]: (k4_relat_1(A_67)=k2_funct_1(A_67) | ~v2_funct_1(A_67) | ~v1_funct_1(A_67) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.66/2.32  tff(c_320, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_90, c_314])).
% 6.66/2.32  tff(c_324, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_249, c_96, c_320])).
% 6.66/2.32  tff(c_24, plain, (![A_13]: (v1_xboole_0(k4_relat_1(A_13)) | ~v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.66/2.32  tff(c_334, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_324, c_24])).
% 6.66/2.32  tff(c_342, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_334])).
% 6.66/2.32  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.66/2.32  tff(c_40, plain, (![A_17]: (v1_funct_1(k2_funct_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.66/2.32  tff(c_86, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_185])).
% 6.66/2.32  tff(c_252, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_86])).
% 6.66/2.32  tff(c_255, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_252])).
% 6.66/2.32  tff(c_259, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_249, c_96, c_255])).
% 6.66/2.32  tff(c_260, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_86])).
% 6.66/2.32  tff(c_280, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_260])).
% 6.66/2.32  tff(c_474, plain, (![A_81, B_82, C_83]: (k2_relset_1(A_81, B_82, C_83)=k2_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.66/2.32  tff(c_480, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_474])).
% 6.66/2.32  tff(c_493, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_480])).
% 6.66/2.32  tff(c_42, plain, (![A_17]: (v1_relat_1(k2_funct_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.66/2.32  tff(c_261, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_86])).
% 6.66/2.32  tff(c_94, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_185])).
% 6.66/2.32  tff(c_402, plain, (![A_71, B_72, C_73]: (k1_relset_1(A_71, B_72, C_73)=k1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.66/2.32  tff(c_416, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_402])).
% 6.66/2.32  tff(c_966, plain, (![B_117, A_118, C_119]: (k1_xboole_0=B_117 | k1_relset_1(A_118, B_117, C_119)=A_118 | ~v1_funct_2(C_119, A_118, B_117) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_118, B_117))))), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.66/2.32  tff(c_978, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_92, c_966])).
% 6.66/2.32  tff(c_996, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_416, c_978])).
% 6.66/2.32  tff(c_1000, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_996])).
% 6.66/2.32  tff(c_44, plain, (![A_18]: (k2_relat_1(k2_funct_1(A_18))=k1_relat_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.66/2.32  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.66/2.32  tff(c_745, plain, (![B_105, A_106]: (m1_subset_1(B_105, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_105), A_106))) | ~r1_tarski(k2_relat_1(B_105), A_106) | ~v1_funct_1(B_105) | ~v1_relat_1(B_105))), inference(cnfTransformation, [status(thm)], [f_168])).
% 6.66/2.32  tff(c_16, plain, (![B_8, A_6]: (v1_xboole_0(B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_6)) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.66/2.32  tff(c_1133, plain, (![B_124, A_125]: (v1_xboole_0(B_124) | ~v1_xboole_0(k2_zfmisc_1(k1_relat_1(B_124), A_125)) | ~r1_tarski(k2_relat_1(B_124), A_125) | ~v1_funct_1(B_124) | ~v1_relat_1(B_124))), inference(resolution, [status(thm)], [c_745, c_16])).
% 6.66/2.32  tff(c_1143, plain, (![B_124]: (v1_xboole_0(B_124) | ~v1_xboole_0(k1_xboole_0) | ~r1_tarski(k2_relat_1(B_124), k1_xboole_0) | ~v1_funct_1(B_124) | ~v1_relat_1(B_124))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1133])).
% 6.66/2.32  tff(c_1284, plain, (![B_137]: (v1_xboole_0(B_137) | ~r1_tarski(k2_relat_1(B_137), k1_xboole_0) | ~v1_funct_1(B_137) | ~v1_relat_1(B_137))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1143])).
% 6.66/2.32  tff(c_2481, plain, (![A_162]: (v1_xboole_0(k2_funct_1(A_162)) | ~r1_tarski(k1_relat_1(A_162), k1_xboole_0) | ~v1_funct_1(k2_funct_1(A_162)) | ~v1_relat_1(k2_funct_1(A_162)) | ~v2_funct_1(A_162) | ~v1_funct_1(A_162) | ~v1_relat_1(A_162))), inference(superposition, [status(thm), theory('equality')], [c_44, c_1284])).
% 6.66/2.32  tff(c_2484, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~r1_tarski('#skF_1', k1_xboole_0) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1000, c_2481])).
% 6.66/2.32  tff(c_2492, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~r1_tarski('#skF_1', k1_xboole_0) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_249, c_96, c_90, c_261, c_2484])).
% 6.66/2.32  tff(c_2495, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2492])).
% 6.66/2.32  tff(c_2498, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_2495])).
% 6.66/2.32  tff(c_2502, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_249, c_96, c_2498])).
% 6.66/2.32  tff(c_2504, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2492])).
% 6.66/2.32  tff(c_442, plain, (![A_80]: (m1_subset_1(A_80, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_80), k2_relat_1(A_80)))) | ~v1_funct_1(A_80) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.66/2.32  tff(c_3305, plain, (![A_172]: (m1_subset_1(k2_funct_1(A_172), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_172)), k1_relat_1(A_172)))) | ~v1_funct_1(k2_funct_1(A_172)) | ~v1_relat_1(k2_funct_1(A_172)) | ~v2_funct_1(A_172) | ~v1_funct_1(A_172) | ~v1_relat_1(A_172))), inference(superposition, [status(thm), theory('equality')], [c_44, c_442])).
% 6.66/2.32  tff(c_3358, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1000, c_3305])).
% 6.66/2.32  tff(c_3398, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_249, c_96, c_90, c_2504, c_261, c_3358])).
% 6.66/2.32  tff(c_3429, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_46, c_3398])).
% 6.66/2.32  tff(c_3442, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_249, c_96, c_90, c_493, c_3429])).
% 6.66/2.32  tff(c_3444, plain, $false, inference(negUnitSimplification, [status(thm)], [c_280, c_3442])).
% 6.66/2.32  tff(c_3445, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_996])).
% 6.66/2.32  tff(c_6, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.66/2.32  tff(c_3476, plain, (![A_2]: (r1_tarski('#skF_2', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_3445, c_6])).
% 6.66/2.32  tff(c_777, plain, (![B_107]: (m1_subset_1(B_107, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(B_107), k1_xboole_0) | ~v1_funct_1(B_107) | ~v1_relat_1(B_107))), inference(superposition, [status(thm), theory('equality')], [c_10, c_745])).
% 6.66/2.32  tff(c_780, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_2', k1_xboole_0) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_493, c_777])).
% 6.66/2.32  tff(c_788, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_249, c_96, c_780])).
% 6.66/2.32  tff(c_791, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_788])).
% 6.66/2.32  tff(c_3451, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3445, c_791])).
% 6.66/2.32  tff(c_3582, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3476, c_3451])).
% 6.66/2.32  tff(c_3583, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_788])).
% 6.66/2.32  tff(c_3599, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_3583, c_16])).
% 6.66/2.32  tff(c_3613, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_3599])).
% 6.66/2.32  tff(c_3615, plain, $false, inference(negUnitSimplification, [status(thm)], [c_342, c_3613])).
% 6.66/2.32  tff(c_3617, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_334])).
% 6.66/2.32  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 6.66/2.32  tff(c_3633, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3617, c_4])).
% 6.66/2.32  tff(c_14, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.66/2.32  tff(c_3646, plain, (![A_5]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_3633, c_14])).
% 6.66/2.32  tff(c_154, plain, (![A_44]: (v1_xboole_0(k4_relat_1(A_44)) | ~v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.66/2.32  tff(c_165, plain, (![A_44]: (k4_relat_1(A_44)=k1_xboole_0 | ~v1_xboole_0(A_44))), inference(resolution, [status(thm)], [c_154, c_4])).
% 6.66/2.32  tff(c_3630, plain, (k4_relat_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_3617, c_165])).
% 6.66/2.32  tff(c_3684, plain, (k4_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3633, c_3630])).
% 6.66/2.32  tff(c_3685, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3684, c_324])).
% 6.66/2.32  tff(c_3707, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3685, c_280])).
% 6.66/2.32  tff(c_3847, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3646, c_3707])).
% 6.66/2.32  tff(c_3848, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_260])).
% 6.66/2.32  tff(c_3849, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_260])).
% 6.66/2.32  tff(c_4016, plain, (![A_204, B_205, C_206]: (k1_relset_1(A_204, B_205, C_206)=k1_relat_1(C_206) | ~m1_subset_1(C_206, k1_zfmisc_1(k2_zfmisc_1(A_204, B_205))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.66/2.32  tff(c_4033, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_3849, c_4016])).
% 6.66/2.32  tff(c_4396, plain, (![B_238, C_239, A_240]: (k1_xboole_0=B_238 | v1_funct_2(C_239, A_240, B_238) | k1_relset_1(A_240, B_238, C_239)!=A_240 | ~m1_subset_1(C_239, k1_zfmisc_1(k2_zfmisc_1(A_240, B_238))))), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.66/2.32  tff(c_4408, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_3849, c_4396])).
% 6.66/2.32  tff(c_4428, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4033, c_4408])).
% 6.66/2.32  tff(c_4429, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_3848, c_4428])).
% 6.66/2.32  tff(c_4435, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_4429])).
% 6.66/2.32  tff(c_4438, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_46, c_4435])).
% 6.66/2.32  tff(c_4441, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_249, c_96, c_90, c_4004, c_4438])).
% 6.66/2.32  tff(c_4442, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_4429])).
% 6.66/2.32  tff(c_4473, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4442, c_2])).
% 6.66/2.32  tff(c_4466, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4442, c_4442, c_10])).
% 6.66/2.32  tff(c_3856, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_3849, c_16])).
% 6.66/2.32  tff(c_3858, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_3856])).
% 6.66/2.32  tff(c_4788, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4466, c_3858])).
% 6.66/2.32  tff(c_4792, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4473, c_4788])).
% 6.66/2.32  tff(c_4794, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_3856])).
% 6.66/2.32  tff(c_4827, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_4794, c_4])).
% 6.66/2.32  tff(c_4867, plain, (![B_248, A_249]: (k1_xboole_0=B_248 | k1_xboole_0=A_249 | k2_zfmisc_1(A_249, B_248)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.66/2.32  tff(c_4877, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_4827, c_4867])).
% 6.66/2.32  tff(c_4882, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_4877])).
% 6.66/2.32  tff(c_4900, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4882, c_2])).
% 6.66/2.32  tff(c_4893, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4882, c_4882, c_10])).
% 6.66/2.32  tff(c_269, plain, (![B_55, A_56]: (v1_xboole_0(B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(A_56)) | ~v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.66/2.32  tff(c_276, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_92, c_269])).
% 6.66/2.32  tff(c_279, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_276])).
% 6.66/2.32  tff(c_5043, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4893, c_279])).
% 6.66/2.32  tff(c_5047, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4900, c_5043])).
% 6.66/2.32  tff(c_5048, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_4877])).
% 6.66/2.32  tff(c_5067, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5048, c_2])).
% 6.66/2.32  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.66/2.32  tff(c_5062, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5048, c_5048, c_12])).
% 6.66/2.32  tff(c_5228, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5062, c_279])).
% 6.66/2.32  tff(c_5232, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5067, c_5228])).
% 6.66/2.32  tff(c_5233, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_276])).
% 6.66/2.32  tff(c_5250, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_5233, c_4])).
% 6.66/2.32  tff(c_5738, plain, (![A_2]: (r1_tarski('#skF_3', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_5250, c_6])).
% 6.66/2.32  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.66/2.32  tff(c_5737, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5250, c_5250, c_26])).
% 6.66/2.32  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.66/2.32  tff(c_5740, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5250, c_5250, c_28])).
% 6.66/2.32  tff(c_6512, plain, (![B_362, A_363]: (v1_funct_2(B_362, k1_relat_1(B_362), A_363) | ~r1_tarski(k2_relat_1(B_362), A_363) | ~v1_funct_1(B_362) | ~v1_relat_1(B_362))), inference(cnfTransformation, [status(thm)], [f_168])).
% 6.66/2.32  tff(c_6521, plain, (![A_363]: (v1_funct_2('#skF_3', '#skF_3', A_363) | ~r1_tarski(k2_relat_1('#skF_3'), A_363) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_5740, c_6512])).
% 6.66/2.32  tff(c_6524, plain, (![A_363]: (v1_funct_2('#skF_3', '#skF_3', A_363))), inference(demodulation, [status(thm), theory('equality')], [c_249, c_96, c_5738, c_5737, c_6521])).
% 6.66/2.32  tff(c_5736, plain, (![B_4]: (k2_zfmisc_1('#skF_3', B_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5250, c_5250, c_12])).
% 6.66/2.32  tff(c_5234, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_276])).
% 6.66/2.32  tff(c_5800, plain, (![A_303]: (A_303='#skF_3' | ~v1_xboole_0(A_303))), inference(demodulation, [status(thm), theory('equality')], [c_5250, c_4])).
% 6.66/2.32  tff(c_5810, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_5234, c_5800])).
% 6.66/2.32  tff(c_8, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.66/2.32  tff(c_5919, plain, (![B_311, A_312]: (B_311='#skF_3' | A_312='#skF_3' | k2_zfmisc_1(A_312, B_311)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5250, c_5250, c_5250, c_8])).
% 6.66/2.32  tff(c_5929, plain, ('#skF_2'='#skF_3' | '#skF_3'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_5810, c_5919])).
% 6.66/2.32  tff(c_5934, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_5929])).
% 6.66/2.32  tff(c_5955, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5934, c_5233])).
% 6.66/2.32  tff(c_5734, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5250, c_5250, c_10])).
% 6.66/2.32  tff(c_5946, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5934, c_5934, c_5734])).
% 6.66/2.32  tff(c_5261, plain, (![A_5]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_5250, c_14])).
% 6.66/2.32  tff(c_5247, plain, (k4_relat_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_5233, c_165])).
% 6.66/2.32  tff(c_5278, plain, (k4_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5250, c_5247])).
% 6.66/2.32  tff(c_5710, plain, (![A_299]: (k4_relat_1(A_299)=k2_funct_1(A_299) | ~v2_funct_1(A_299) | ~v1_funct_1(A_299) | ~v1_relat_1(A_299))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.66/2.32  tff(c_5716, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_90, c_5710])).
% 6.66/2.32  tff(c_5720, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_249, c_96, c_5278, c_5716])).
% 6.66/2.32  tff(c_5262, plain, (![B_4]: (k2_zfmisc_1('#skF_3', B_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5250, c_5250, c_12])).
% 6.66/2.32  tff(c_5343, plain, (![A_275]: (A_275='#skF_3' | ~v1_xboole_0(A_275))), inference(demodulation, [status(thm), theory('equality')], [c_5250, c_4])).
% 6.66/2.32  tff(c_5353, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_5234, c_5343])).
% 6.66/2.32  tff(c_5436, plain, (![B_282, A_283]: (B_282='#skF_3' | A_283='#skF_3' | k2_zfmisc_1(A_283, B_282)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5250, c_5250, c_5250, c_8])).
% 6.66/2.32  tff(c_5446, plain, ('#skF_2'='#skF_3' | '#skF_3'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_5353, c_5436])).
% 6.66/2.32  tff(c_5451, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_5446])).
% 6.66/2.32  tff(c_5458, plain, (![A_5]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_5451, c_5261])).
% 6.66/2.32  tff(c_5467, plain, (k4_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5451, c_5451, c_5278])).
% 6.66/2.32  tff(c_5472, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5451, c_249])).
% 6.66/2.32  tff(c_5476, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5451, c_96])).
% 6.66/2.32  tff(c_5475, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5451, c_90])).
% 6.66/2.32  tff(c_5495, plain, (![A_284]: (k4_relat_1(A_284)=k2_funct_1(A_284) | ~v2_funct_1(A_284) | ~v1_funct_1(A_284) | ~v1_relat_1(A_284))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.66/2.32  tff(c_5498, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_5475, c_5495])).
% 6.66/2.32  tff(c_5504, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5472, c_5476, c_5498])).
% 6.66/2.32  tff(c_5594, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5467, c_5504])).
% 6.66/2.32  tff(c_5260, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5250, c_5250, c_10])).
% 6.66/2.32  tff(c_5461, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5451, c_5451, c_5260])).
% 6.66/2.32  tff(c_5253, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_260])).
% 6.66/2.32  tff(c_5464, plain, (~m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_5451, c_5253])).
% 6.66/2.32  tff(c_5681, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5458, c_5594, c_5461, c_5464])).
% 6.66/2.32  tff(c_5682, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_5446])).
% 6.66/2.32  tff(c_5685, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_5682, c_5253])).
% 6.66/2.32  tff(c_5689, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5262, c_5685])).
% 6.66/2.32  tff(c_5721, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5720, c_5689])).
% 6.66/2.32  tff(c_5725, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5261, c_5721])).
% 6.66/2.32  tff(c_5727, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_260])).
% 6.66/2.32  tff(c_5850, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_5727, c_16])).
% 6.66/2.32  tff(c_5917, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_5850])).
% 6.66/2.32  tff(c_6071, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5946, c_5917])).
% 6.66/2.32  tff(c_6074, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5955, c_6071])).
% 6.66/2.32  tff(c_6075, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_5929])).
% 6.66/2.32  tff(c_6077, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6075, c_5917])).
% 6.66/2.32  tff(c_6085, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5233, c_5736, c_6077])).
% 6.66/2.32  tff(c_6087, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_5850])).
% 6.66/2.32  tff(c_5733, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_5250, c_4])).
% 6.66/2.32  tff(c_6142, plain, (k2_zfmisc_1('#skF_2', '#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_6087, c_5733])).
% 6.66/2.32  tff(c_6158, plain, (![B_323, A_324]: (B_323='#skF_3' | A_324='#skF_3' | k2_zfmisc_1(A_324, B_323)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5250, c_5250, c_5250, c_8])).
% 6.66/2.32  tff(c_6171, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_6142, c_6158])).
% 6.66/2.32  tff(c_6178, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_6171])).
% 6.66/2.32  tff(c_6086, plain, (v1_xboole_0(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_5850])).
% 6.66/2.32  tff(c_6101, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_6086, c_5733])).
% 6.66/2.32  tff(c_5726, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_260])).
% 6.66/2.32  tff(c_6109, plain, (~v1_funct_2('#skF_3', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6101, c_5726])).
% 6.66/2.32  tff(c_6300, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6178, c_6109])).
% 6.66/2.32  tff(c_6528, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6524, c_6300])).
% 6.66/2.32  tff(c_6529, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_6171])).
% 6.66/2.32  tff(c_6530, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_6171])).
% 6.66/2.32  tff(c_6561, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6529, c_6530])).
% 6.66/2.32  tff(c_62, plain, (![A_29]: (v1_funct_2(k1_xboole_0, A_29, k1_xboole_0) | k1_xboole_0=A_29 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_29, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.66/2.32  tff(c_98, plain, (![A_29]: (v1_funct_2(k1_xboole_0, A_29, k1_xboole_0) | k1_xboole_0=A_29)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_62])).
% 6.66/2.32  tff(c_5730, plain, (![A_29]: (v1_funct_2('#skF_3', A_29, '#skF_3') | A_29='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5250, c_5250, c_5250, c_98])).
% 6.66/2.32  tff(c_6746, plain, (![A_378]: (v1_funct_2('#skF_1', A_378, '#skF_1') | A_378='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6529, c_6529, c_6529, c_5730])).
% 6.66/2.32  tff(c_6531, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6529, c_6109])).
% 6.66/2.32  tff(c_6749, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_6746, c_6531])).
% 6.66/2.32  tff(c_6753, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6561, c_6749])).
% 6.66/2.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.66/2.32  
% 6.66/2.32  Inference rules
% 6.66/2.32  ----------------------
% 6.66/2.32  #Ref     : 0
% 6.66/2.32  #Sup     : 1507
% 6.66/2.32  #Fact    : 0
% 6.66/2.32  #Define  : 0
% 6.66/2.32  #Split   : 20
% 6.66/2.32  #Chain   : 0
% 6.66/2.32  #Close   : 0
% 6.66/2.32  
% 6.66/2.32  Ordering : KBO
% 6.66/2.32  
% 6.66/2.32  Simplification rules
% 6.66/2.32  ----------------------
% 6.66/2.32  #Subsume      : 138
% 6.66/2.32  #Demod        : 2480
% 6.66/2.32  #Tautology    : 997
% 6.66/2.32  #SimpNegUnit  : 15
% 6.66/2.32  #BackRed      : 343
% 6.66/2.32  
% 6.66/2.32  #Partial instantiations: 0
% 6.66/2.32  #Strategies tried      : 1
% 6.66/2.32  
% 6.66/2.32  Timing (in seconds)
% 6.66/2.32  ----------------------
% 6.66/2.32  Preprocessing        : 0.36
% 6.66/2.32  Parsing              : 0.19
% 6.66/2.32  CNF conversion       : 0.02
% 6.66/2.32  Main loop            : 1.17
% 6.66/2.32  Inferencing          : 0.37
% 6.66/2.32  Reduction            : 0.43
% 6.66/2.32  Demodulation         : 0.31
% 6.66/2.32  BG Simplification    : 0.05
% 6.66/2.32  Subsumption          : 0.22
% 6.66/2.32  Abstraction          : 0.05
% 6.66/2.32  MUC search           : 0.00
% 6.66/2.32  Cooper               : 0.00
% 6.66/2.32  Total                : 1.59
% 6.66/2.32  Index Insertion      : 0.00
% 6.66/2.32  Index Deletion       : 0.00
% 6.66/2.32  Index Matching       : 0.00
% 6.66/2.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
