%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:27 EST 2020

% Result     : Theorem 6.23s
% Output     : CNFRefutation 6.52s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 724 expanded)
%              Number of leaves         :   41 ( 260 expanded)
%              Depth                    :   12
%              Number of atoms          :  319 (2134 expanded)
%              Number of equality atoms :   83 ( 420 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_176,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ( v1_xboole_0(k4_relat_1(A))
        & v1_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_relat_1)).

tff(f_119,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_89,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_99,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_137,axiom,(
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

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_147,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_57,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_159,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(c_86,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_240,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_249,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_240])).

tff(c_90,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_84,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_3500,plain,(
    ! [A_169] :
      ( k4_relat_1(A_169) = k2_funct_1(A_169)
      | ~ v2_funct_1(A_169)
      | ~ v1_funct_1(A_169)
      | ~ v1_relat_1(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3506,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_3500])).

tff(c_3510,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_90,c_3506])).

tff(c_16,plain,(
    ! [A_6] :
      ( v1_xboole_0(k4_relat_1(A_6))
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3523,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3510,c_16])).

tff(c_3529,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3523])).

tff(c_82,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_3592,plain,(
    ! [A_173,B_174,C_175] :
      ( k2_relset_1(A_173,B_174,C_175) = k2_relat_1(C_175)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_3602,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_3592])).

tff(c_3606,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_3602])).

tff(c_18,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(k2_relat_1(A_7))
      | ~ v1_relat_1(A_7)
      | v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3613,plain,
    ( ~ v1_xboole_0('#skF_2')
    | ~ v1_relat_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3606,c_18])).

tff(c_3619,plain,
    ( ~ v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_3613])).

tff(c_3620,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_3529,c_3619])).

tff(c_280,plain,(
    ! [A_57] :
      ( k4_relat_1(A_57) = k2_funct_1(A_57)
      | ~ v2_funct_1(A_57)
      | ~ v1_funct_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_286,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_280])).

tff(c_290,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_90,c_286])).

tff(c_14,plain,(
    ! [A_6] :
      ( v1_relat_1(k4_relat_1(A_6))
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_315,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_14])).

tff(c_323,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_315])).

tff(c_482,plain,(
    ! [A_73,B_74,C_75] :
      ( k2_relset_1(A_73,B_74,C_75) = k2_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_495,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_482])).

tff(c_501,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_495])).

tff(c_523,plain,
    ( ~ v1_xboole_0('#skF_2')
    | ~ v1_relat_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_18])).

tff(c_533,plain,
    ( ~ v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_523])).

tff(c_534,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_323,c_533])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_34,plain,(
    ! [A_11] :
      ( v1_funct_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_80,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_218,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_221,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_218])).

tff(c_224,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_221])).

tff(c_225,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_232,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_225])).

tff(c_237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_232])).

tff(c_238,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_274,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_238])).

tff(c_279,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_274])).

tff(c_40,plain,(
    ! [A_12] :
      ( k1_relat_1(k2_funct_1(A_12)) = k2_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_36,plain,(
    ! [A_11] :
      ( v1_relat_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_88,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_371,plain,(
    ! [A_61,B_62,C_63] :
      ( k1_relset_1(A_61,B_62,C_63) = k1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_380,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_371])).

tff(c_1064,plain,(
    ! [B_111,A_112,C_113] :
      ( k1_xboole_0 = B_111
      | k1_relset_1(A_112,B_111,C_113) = A_112
      | ~ v1_funct_2(C_113,A_112,B_111)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_112,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1083,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_86,c_1064])).

tff(c_1095,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_380,c_1083])).

tff(c_1096,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1095])).

tff(c_291,plain,(
    ! [A_58] :
      ( k2_relat_1(k2_funct_1(A_58)) = k1_relat_1(A_58)
      | ~ v2_funct_1(A_58)
      | ~ v1_funct_1(A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1436,plain,(
    ! [A_124] :
      ( ~ v1_xboole_0(k1_relat_1(A_124))
      | ~ v1_relat_1(k2_funct_1(A_124))
      | v1_xboole_0(k2_funct_1(A_124))
      | ~ v2_funct_1(A_124)
      | ~ v1_funct_1(A_124)
      | ~ v1_relat_1(A_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_18])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_2138,plain,(
    ! [A_145] :
      ( k2_funct_1(A_145) = k1_xboole_0
      | ~ v1_xboole_0(k1_relat_1(A_145))
      | ~ v1_relat_1(k2_funct_1(A_145))
      | ~ v2_funct_1(A_145)
      | ~ v1_funct_1(A_145)
      | ~ v1_relat_1(A_145) ) ),
    inference(resolution,[status(thm)],[c_1436,c_4])).

tff(c_2141,plain,
    ( k2_funct_1('#skF_3') = k1_xboole_0
    | ~ v1_xboole_0('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1096,c_2138])).

tff(c_2149,plain,
    ( k2_funct_1('#skF_3') = k1_xboole_0
    | ~ v1_xboole_0('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_90,c_84,c_2141])).

tff(c_2152,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2149])).

tff(c_2155,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_2152])).

tff(c_2159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_90,c_2155])).

tff(c_2161,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2149])).

tff(c_239,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_38,plain,(
    ! [A_12] :
      ( k2_relat_1(k2_funct_1(A_12)) = k1_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_405,plain,(
    ! [A_69] :
      ( m1_subset_1(A_69,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_69),k2_relat_1(A_69))))
      | ~ v1_funct_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_457,plain,(
    ! [A_72] :
      ( r1_tarski(A_72,k2_zfmisc_1(k1_relat_1(A_72),k2_relat_1(A_72)))
      | ~ v1_funct_1(A_72)
      | ~ v1_relat_1(A_72) ) ),
    inference(resolution,[status(thm)],[c_405,c_8])).

tff(c_3139,plain,(
    ! [A_162] :
      ( r1_tarski(k2_funct_1(A_162),k2_zfmisc_1(k1_relat_1(k2_funct_1(A_162)),k1_relat_1(A_162)))
      | ~ v1_funct_1(k2_funct_1(A_162))
      | ~ v1_relat_1(k2_funct_1(A_162))
      | ~ v2_funct_1(A_162)
      | ~ v1_funct_1(A_162)
      | ~ v1_relat_1(A_162) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_457])).

tff(c_3187,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1096,c_3139])).

tff(c_3225,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_90,c_84,c_2161,c_239,c_3187])).

tff(c_3251,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_3225])).

tff(c_3262,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_90,c_84,c_501,c_3251])).

tff(c_3264,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_279,c_3262])).

tff(c_3265,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1095])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_3291,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3265,c_2])).

tff(c_3295,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_534,c_3291])).

tff(c_3297,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_315])).

tff(c_3313,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3297,c_4])).

tff(c_6,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3322,plain,(
    ! [A_2] : r1_tarski('#skF_3',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3313,c_6])).

tff(c_119,plain,(
    ! [A_34] :
      ( v1_xboole_0(k4_relat_1(A_34))
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_130,plain,(
    ! [A_34] :
      ( k4_relat_1(A_34) = k1_xboole_0
      | ~ v1_xboole_0(A_34) ) ),
    inference(resolution,[status(thm)],[c_119,c_4])).

tff(c_3310,plain,(
    k4_relat_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3297,c_130])).

tff(c_3357,plain,(
    k4_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3313,c_3310])).

tff(c_3358,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3357,c_290])).

tff(c_3379,plain,(
    ~ r1_tarski('#skF_3',k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3358,c_279])).

tff(c_3483,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3322,c_3379])).

tff(c_3484,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_238])).

tff(c_3759,plain,(
    ! [A_183,B_184,C_185] :
      ( k1_relset_1(A_183,B_184,C_185) = k1_relat_1(C_185)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_3785,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_3759])).

tff(c_4306,plain,(
    ! [B_219,A_220,C_221] :
      ( k1_xboole_0 = B_219
      | k1_relset_1(A_220,B_219,C_221) = A_220
      | ~ v1_funct_2(C_221,A_220,B_219)
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(A_220,B_219))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_4328,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_86,c_4306])).

tff(c_4342,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_3785,c_4328])).

tff(c_4343,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4342])).

tff(c_3485,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_238])).

tff(c_50,plain,(
    ! [C_16,A_14,B_15] :
      ( v1_relat_1(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_3493,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3485,c_50])).

tff(c_3783,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3485,c_3759])).

tff(c_4448,plain,(
    ! [B_226,C_227,A_228] :
      ( k1_xboole_0 = B_226
      | v1_funct_2(C_227,A_228,B_226)
      | k1_relset_1(A_228,B_226,C_227) != A_228
      | ~ m1_subset_1(C_227,k1_zfmisc_1(k2_zfmisc_1(A_228,B_226))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_4460,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_3485,c_4448])).

tff(c_4474,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3783,c_4460])).

tff(c_4475,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_3484,c_4474])).

tff(c_4480,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4475])).

tff(c_4483,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_4480])).

tff(c_4486,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_90,c_84,c_3606,c_4483])).

tff(c_4488,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4475])).

tff(c_70,plain,(
    ! [A_26] :
      ( v1_funct_2(A_26,k1_relat_1(A_26),k2_relat_1(A_26))
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_4547,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4488,c_70])).

tff(c_4570,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3493,c_239,c_4547])).

tff(c_4879,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_4570])).

tff(c_4881,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_90,c_84,c_4343,c_4879])).

tff(c_4883,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3484,c_4881])).

tff(c_4884,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4342])).

tff(c_4908,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4884,c_2])).

tff(c_4912,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3620,c_4908])).

tff(c_4914,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_3523])).

tff(c_4930,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4914,c_4])).

tff(c_4939,plain,(
    ! [A_2] : r1_tarski('#skF_3',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4930,c_6])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4938,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4930,c_4930,c_20])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4941,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4930,c_4930,c_22])).

tff(c_5340,plain,(
    ! [B_259,A_260] :
      ( v1_funct_2(B_259,k1_relat_1(B_259),A_260)
      | ~ r1_tarski(k2_relat_1(B_259),A_260)
      | ~ v1_funct_1(B_259)
      | ~ v1_relat_1(B_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_5346,plain,(
    ! [A_260] :
      ( v1_funct_2('#skF_3','#skF_3',A_260)
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_260)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4941,c_5340])).

tff(c_5348,plain,(
    ! [A_260] : v1_funct_2('#skF_3','#skF_3',A_260) ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_90,c_4939,c_4938,c_5346])).

tff(c_5230,plain,(
    ! [A_253,B_254,C_255] :
      ( k2_relset_1(A_253,B_254,C_255) = k2_relat_1(C_255)
      | ~ m1_subset_1(C_255,k1_zfmisc_1(k2_zfmisc_1(A_253,B_254))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_5246,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_5230])).

tff(c_5254,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4938,c_82,c_5246])).

tff(c_4927,plain,(
    k4_relat_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4914,c_130])).

tff(c_4978,plain,(
    k4_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4930,c_4927])).

tff(c_4979,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4978,c_3510])).

tff(c_5012,plain,(
    ~ v1_funct_2('#skF_3','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4979,c_3484])).

tff(c_5256,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5254,c_5012])).

tff(c_5352,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5348,c_5256])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:12:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.23/2.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.23/2.24  
% 6.23/2.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.23/2.24  %$ v1_funct_2 > v5_relat_1 > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.23/2.24  
% 6.23/2.24  %Foreground sorts:
% 6.23/2.24  
% 6.23/2.24  
% 6.23/2.24  %Background operators:
% 6.23/2.24  
% 6.23/2.24  
% 6.23/2.24  %Foreground operators:
% 6.23/2.24  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.23/2.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.23/2.24  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.23/2.24  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.23/2.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.23/2.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.23/2.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.23/2.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.23/2.24  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 6.23/2.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.23/2.24  tff('#skF_2', type, '#skF_2': $i).
% 6.23/2.24  tff('#skF_3', type, '#skF_3': $i).
% 6.23/2.24  tff('#skF_1', type, '#skF_1': $i).
% 6.23/2.24  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.23/2.24  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.23/2.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.23/2.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.23/2.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.23/2.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.23/2.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.23/2.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.23/2.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.23/2.24  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 6.23/2.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.23/2.24  
% 6.52/2.28  tff(f_176, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 6.52/2.28  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.52/2.28  tff(f_81, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 6.52/2.28  tff(f_46, axiom, (![A]: (v1_xboole_0(A) => (v1_xboole_0(k4_relat_1(A)) & v1_relat_1(k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_relat_1)).
% 6.52/2.28  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.52/2.28  tff(f_54, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 6.52/2.28  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.52/2.28  tff(f_89, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 6.52/2.28  tff(f_99, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 6.52/2.28  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.52/2.28  tff(f_137, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 6.52/2.28  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 6.52/2.28  tff(f_147, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 6.52/2.28  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.52/2.28  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.52/2.28  tff(f_57, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 6.52/2.28  tff(f_159, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 6.52/2.28  tff(c_86, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_176])).
% 6.52/2.28  tff(c_240, plain, (![C_49, A_50, B_51]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.52/2.28  tff(c_249, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_240])).
% 6.52/2.28  tff(c_90, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_176])).
% 6.52/2.28  tff(c_84, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_176])).
% 6.52/2.28  tff(c_3500, plain, (![A_169]: (k4_relat_1(A_169)=k2_funct_1(A_169) | ~v2_funct_1(A_169) | ~v1_funct_1(A_169) | ~v1_relat_1(A_169))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.52/2.28  tff(c_3506, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_3500])).
% 6.52/2.28  tff(c_3510, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_249, c_90, c_3506])).
% 6.52/2.28  tff(c_16, plain, (![A_6]: (v1_xboole_0(k4_relat_1(A_6)) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.52/2.28  tff(c_3523, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3510, c_16])).
% 6.52/2.28  tff(c_3529, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_3523])).
% 6.52/2.28  tff(c_82, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_176])).
% 6.52/2.28  tff(c_3592, plain, (![A_173, B_174, C_175]: (k2_relset_1(A_173, B_174, C_175)=k2_relat_1(C_175) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.52/2.28  tff(c_3602, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_3592])).
% 6.52/2.28  tff(c_3606, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_3602])).
% 6.52/2.28  tff(c_18, plain, (![A_7]: (~v1_xboole_0(k2_relat_1(A_7)) | ~v1_relat_1(A_7) | v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.52/2.28  tff(c_3613, plain, (~v1_xboole_0('#skF_2') | ~v1_relat_1('#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3606, c_18])).
% 6.52/2.28  tff(c_3619, plain, (~v1_xboole_0('#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_249, c_3613])).
% 6.52/2.28  tff(c_3620, plain, (~v1_xboole_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_3529, c_3619])).
% 6.52/2.28  tff(c_280, plain, (![A_57]: (k4_relat_1(A_57)=k2_funct_1(A_57) | ~v2_funct_1(A_57) | ~v1_funct_1(A_57) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.52/2.28  tff(c_286, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_280])).
% 6.52/2.28  tff(c_290, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_249, c_90, c_286])).
% 6.52/2.28  tff(c_14, plain, (![A_6]: (v1_relat_1(k4_relat_1(A_6)) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.52/2.28  tff(c_315, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_290, c_14])).
% 6.52/2.28  tff(c_323, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_315])).
% 6.52/2.28  tff(c_482, plain, (![A_73, B_74, C_75]: (k2_relset_1(A_73, B_74, C_75)=k2_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.52/2.28  tff(c_495, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_482])).
% 6.52/2.28  tff(c_501, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_495])).
% 6.52/2.28  tff(c_523, plain, (~v1_xboole_0('#skF_2') | ~v1_relat_1('#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_501, c_18])).
% 6.52/2.28  tff(c_533, plain, (~v1_xboole_0('#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_249, c_523])).
% 6.52/2.28  tff(c_534, plain, (~v1_xboole_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_323, c_533])).
% 6.52/2.28  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.52/2.28  tff(c_34, plain, (![A_11]: (v1_funct_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.52/2.28  tff(c_80, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_176])).
% 6.52/2.28  tff(c_218, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_80])).
% 6.52/2.28  tff(c_221, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_218])).
% 6.52/2.28  tff(c_224, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_221])).
% 6.52/2.28  tff(c_225, plain, (![C_46, A_47, B_48]: (v1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.52/2.28  tff(c_232, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_225])).
% 6.52/2.28  tff(c_237, plain, $false, inference(negUnitSimplification, [status(thm)], [c_224, c_232])).
% 6.52/2.28  tff(c_238, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_80])).
% 6.52/2.28  tff(c_274, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_238])).
% 6.52/2.28  tff(c_279, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_10, c_274])).
% 6.52/2.28  tff(c_40, plain, (![A_12]: (k1_relat_1(k2_funct_1(A_12))=k2_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.52/2.28  tff(c_36, plain, (![A_11]: (v1_relat_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.52/2.28  tff(c_88, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 6.52/2.28  tff(c_371, plain, (![A_61, B_62, C_63]: (k1_relset_1(A_61, B_62, C_63)=k1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.52/2.28  tff(c_380, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_371])).
% 6.52/2.28  tff(c_1064, plain, (![B_111, A_112, C_113]: (k1_xboole_0=B_111 | k1_relset_1(A_112, B_111, C_113)=A_112 | ~v1_funct_2(C_113, A_112, B_111) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_112, B_111))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.52/2.28  tff(c_1083, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_86, c_1064])).
% 6.52/2.28  tff(c_1095, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_380, c_1083])).
% 6.52/2.28  tff(c_1096, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_1095])).
% 6.52/2.28  tff(c_291, plain, (![A_58]: (k2_relat_1(k2_funct_1(A_58))=k1_relat_1(A_58) | ~v2_funct_1(A_58) | ~v1_funct_1(A_58) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.52/2.28  tff(c_1436, plain, (![A_124]: (~v1_xboole_0(k1_relat_1(A_124)) | ~v1_relat_1(k2_funct_1(A_124)) | v1_xboole_0(k2_funct_1(A_124)) | ~v2_funct_1(A_124) | ~v1_funct_1(A_124) | ~v1_relat_1(A_124))), inference(superposition, [status(thm), theory('equality')], [c_291, c_18])).
% 6.52/2.28  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 6.52/2.28  tff(c_2138, plain, (![A_145]: (k2_funct_1(A_145)=k1_xboole_0 | ~v1_xboole_0(k1_relat_1(A_145)) | ~v1_relat_1(k2_funct_1(A_145)) | ~v2_funct_1(A_145) | ~v1_funct_1(A_145) | ~v1_relat_1(A_145))), inference(resolution, [status(thm)], [c_1436, c_4])).
% 6.52/2.28  tff(c_2141, plain, (k2_funct_1('#skF_3')=k1_xboole_0 | ~v1_xboole_0('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1096, c_2138])).
% 6.52/2.28  tff(c_2149, plain, (k2_funct_1('#skF_3')=k1_xboole_0 | ~v1_xboole_0('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_249, c_90, c_84, c_2141])).
% 6.52/2.28  tff(c_2152, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2149])).
% 6.52/2.28  tff(c_2155, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_2152])).
% 6.52/2.28  tff(c_2159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_249, c_90, c_2155])).
% 6.52/2.28  tff(c_2161, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2149])).
% 6.52/2.28  tff(c_239, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_80])).
% 6.52/2.28  tff(c_38, plain, (![A_12]: (k2_relat_1(k2_funct_1(A_12))=k1_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.52/2.28  tff(c_405, plain, (![A_69]: (m1_subset_1(A_69, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_69), k2_relat_1(A_69)))) | ~v1_funct_1(A_69) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_147])).
% 6.52/2.28  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.52/2.28  tff(c_457, plain, (![A_72]: (r1_tarski(A_72, k2_zfmisc_1(k1_relat_1(A_72), k2_relat_1(A_72))) | ~v1_funct_1(A_72) | ~v1_relat_1(A_72))), inference(resolution, [status(thm)], [c_405, c_8])).
% 6.52/2.28  tff(c_3139, plain, (![A_162]: (r1_tarski(k2_funct_1(A_162), k2_zfmisc_1(k1_relat_1(k2_funct_1(A_162)), k1_relat_1(A_162))) | ~v1_funct_1(k2_funct_1(A_162)) | ~v1_relat_1(k2_funct_1(A_162)) | ~v2_funct_1(A_162) | ~v1_funct_1(A_162) | ~v1_relat_1(A_162))), inference(superposition, [status(thm), theory('equality')], [c_38, c_457])).
% 6.52/2.28  tff(c_3187, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1096, c_3139])).
% 6.52/2.28  tff(c_3225, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_249, c_90, c_84, c_2161, c_239, c_3187])).
% 6.52/2.28  tff(c_3251, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_40, c_3225])).
% 6.52/2.28  tff(c_3262, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_249, c_90, c_84, c_501, c_3251])).
% 6.52/2.28  tff(c_3264, plain, $false, inference(negUnitSimplification, [status(thm)], [c_279, c_3262])).
% 6.52/2.28  tff(c_3265, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1095])).
% 6.52/2.28  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.52/2.28  tff(c_3291, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3265, c_2])).
% 6.52/2.28  tff(c_3295, plain, $false, inference(negUnitSimplification, [status(thm)], [c_534, c_3291])).
% 6.52/2.28  tff(c_3297, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_315])).
% 6.52/2.28  tff(c_3313, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3297, c_4])).
% 6.52/2.28  tff(c_6, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.52/2.28  tff(c_3322, plain, (![A_2]: (r1_tarski('#skF_3', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_3313, c_6])).
% 6.52/2.28  tff(c_119, plain, (![A_34]: (v1_xboole_0(k4_relat_1(A_34)) | ~v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.52/2.28  tff(c_130, plain, (![A_34]: (k4_relat_1(A_34)=k1_xboole_0 | ~v1_xboole_0(A_34))), inference(resolution, [status(thm)], [c_119, c_4])).
% 6.52/2.28  tff(c_3310, plain, (k4_relat_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_3297, c_130])).
% 6.52/2.28  tff(c_3357, plain, (k4_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3313, c_3310])).
% 6.52/2.28  tff(c_3358, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3357, c_290])).
% 6.52/2.28  tff(c_3379, plain, (~r1_tarski('#skF_3', k2_zfmisc_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3358, c_279])).
% 6.52/2.28  tff(c_3483, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3322, c_3379])).
% 6.52/2.28  tff(c_3484, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_238])).
% 6.52/2.28  tff(c_3759, plain, (![A_183, B_184, C_185]: (k1_relset_1(A_183, B_184, C_185)=k1_relat_1(C_185) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.52/2.28  tff(c_3785, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_3759])).
% 6.52/2.28  tff(c_4306, plain, (![B_219, A_220, C_221]: (k1_xboole_0=B_219 | k1_relset_1(A_220, B_219, C_221)=A_220 | ~v1_funct_2(C_221, A_220, B_219) | ~m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(A_220, B_219))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.52/2.28  tff(c_4328, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_86, c_4306])).
% 6.52/2.28  tff(c_4342, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_3785, c_4328])).
% 6.52/2.28  tff(c_4343, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_4342])).
% 6.52/2.28  tff(c_3485, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_238])).
% 6.52/2.28  tff(c_50, plain, (![C_16, A_14, B_15]: (v1_relat_1(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.52/2.28  tff(c_3493, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_3485, c_50])).
% 6.52/2.28  tff(c_3783, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_3485, c_3759])).
% 6.52/2.28  tff(c_4448, plain, (![B_226, C_227, A_228]: (k1_xboole_0=B_226 | v1_funct_2(C_227, A_228, B_226) | k1_relset_1(A_228, B_226, C_227)!=A_228 | ~m1_subset_1(C_227, k1_zfmisc_1(k2_zfmisc_1(A_228, B_226))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.52/2.28  tff(c_4460, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_3485, c_4448])).
% 6.52/2.28  tff(c_4474, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3783, c_4460])).
% 6.52/2.28  tff(c_4475, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_3484, c_4474])).
% 6.52/2.28  tff(c_4480, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_4475])).
% 6.52/2.28  tff(c_4483, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_40, c_4480])).
% 6.52/2.28  tff(c_4486, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_249, c_90, c_84, c_3606, c_4483])).
% 6.52/2.28  tff(c_4488, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_4475])).
% 6.52/2.28  tff(c_70, plain, (![A_26]: (v1_funct_2(A_26, k1_relat_1(A_26), k2_relat_1(A_26)) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_147])).
% 6.52/2.28  tff(c_4547, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4488, c_70])).
% 6.52/2.28  tff(c_4570, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_3493, c_239, c_4547])).
% 6.52/2.28  tff(c_4879, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_38, c_4570])).
% 6.52/2.28  tff(c_4881, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_249, c_90, c_84, c_4343, c_4879])).
% 6.52/2.28  tff(c_4883, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3484, c_4881])).
% 6.52/2.28  tff(c_4884, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_4342])).
% 6.52/2.28  tff(c_4908, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4884, c_2])).
% 6.52/2.28  tff(c_4912, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3620, c_4908])).
% 6.52/2.28  tff(c_4914, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_3523])).
% 6.52/2.28  tff(c_4930, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_4914, c_4])).
% 6.52/2.28  tff(c_4939, plain, (![A_2]: (r1_tarski('#skF_3', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_4930, c_6])).
% 6.52/2.28  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.52/2.28  tff(c_4938, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4930, c_4930, c_20])).
% 6.52/2.28  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.52/2.28  tff(c_4941, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4930, c_4930, c_22])).
% 6.52/2.28  tff(c_5340, plain, (![B_259, A_260]: (v1_funct_2(B_259, k1_relat_1(B_259), A_260) | ~r1_tarski(k2_relat_1(B_259), A_260) | ~v1_funct_1(B_259) | ~v1_relat_1(B_259))), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.52/2.28  tff(c_5346, plain, (![A_260]: (v1_funct_2('#skF_3', '#skF_3', A_260) | ~r1_tarski(k2_relat_1('#skF_3'), A_260) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4941, c_5340])).
% 6.52/2.28  tff(c_5348, plain, (![A_260]: (v1_funct_2('#skF_3', '#skF_3', A_260))), inference(demodulation, [status(thm), theory('equality')], [c_249, c_90, c_4939, c_4938, c_5346])).
% 6.52/2.28  tff(c_5230, plain, (![A_253, B_254, C_255]: (k2_relset_1(A_253, B_254, C_255)=k2_relat_1(C_255) | ~m1_subset_1(C_255, k1_zfmisc_1(k2_zfmisc_1(A_253, B_254))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.52/2.28  tff(c_5246, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_5230])).
% 6.52/2.28  tff(c_5254, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4938, c_82, c_5246])).
% 6.52/2.28  tff(c_4927, plain, (k4_relat_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_4914, c_130])).
% 6.52/2.28  tff(c_4978, plain, (k4_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4930, c_4927])).
% 6.52/2.28  tff(c_4979, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4978, c_3510])).
% 6.52/2.28  tff(c_5012, plain, (~v1_funct_2('#skF_3', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4979, c_3484])).
% 6.52/2.28  tff(c_5256, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5254, c_5012])).
% 6.52/2.28  tff(c_5352, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5348, c_5256])).
% 6.52/2.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.52/2.28  
% 6.52/2.28  Inference rules
% 6.52/2.28  ----------------------
% 6.52/2.28  #Ref     : 0
% 6.52/2.28  #Sup     : 1182
% 6.52/2.28  #Fact    : 0
% 6.52/2.28  #Define  : 0
% 6.52/2.28  #Split   : 12
% 6.52/2.28  #Chain   : 0
% 6.52/2.28  #Close   : 0
% 6.52/2.28  
% 6.52/2.28  Ordering : KBO
% 6.52/2.28  
% 6.52/2.28  Simplification rules
% 6.52/2.28  ----------------------
% 6.52/2.28  #Subsume      : 130
% 6.52/2.28  #Demod        : 1885
% 6.52/2.28  #Tautology    : 724
% 6.52/2.28  #SimpNegUnit  : 8
% 6.52/2.28  #BackRed      : 135
% 6.52/2.28  
% 6.52/2.28  #Partial instantiations: 0
% 6.52/2.28  #Strategies tried      : 1
% 6.52/2.28  
% 6.52/2.28  Timing (in seconds)
% 6.52/2.28  ----------------------
% 6.52/2.29  Preprocessing        : 0.37
% 6.52/2.29  Parsing              : 0.20
% 6.52/2.29  CNF conversion       : 0.02
% 6.52/2.29  Main loop            : 1.06
% 6.52/2.29  Inferencing          : 0.35
% 6.52/2.29  Reduction            : 0.37
% 6.52/2.29  Demodulation         : 0.28
% 6.52/2.29  BG Simplification    : 0.05
% 6.52/2.29  Subsumption          : 0.20
% 6.52/2.29  Abstraction          : 0.05
% 6.52/2.29  MUC search           : 0.00
% 6.52/2.29  Cooper               : 0.00
% 6.52/2.29  Total                : 1.51
% 6.52/2.29  Index Insertion      : 0.00
% 6.52/2.29  Index Deletion       : 0.00
% 6.52/2.29  Index Matching       : 0.00
% 6.52/2.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
