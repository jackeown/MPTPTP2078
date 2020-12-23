%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:46 EST 2020

% Result     : Theorem 10.25s
% Output     : CNFRefutation 10.64s
% Verified   : 
% Statistics : Number of formulae       :  354 (4130 expanded)
%              Number of leaves         :   35 (1245 expanded)
%              Depth                    :   16
%              Number of atoms          :  622 (10941 expanded)
%              Number of equality atoms :  241 (4023 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_129,negated_conjecture,(
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

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_102,axiom,(
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

tff(f_112,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_54,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_188,plain,(
    ! [C_45,A_46,B_47] :
      ( v1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_205,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_188])).

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_64,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_62,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_6426,plain,(
    ! [A_537,B_538,C_539] :
      ( k2_relset_1(A_537,B_538,C_539) = k2_relat_1(C_539)
      | ~ m1_subset_1(C_539,k1_zfmisc_1(k2_zfmisc_1(A_537,B_538))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_6439,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_6426])).

tff(c_6453,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_6439])).

tff(c_34,plain,(
    ! [A_13] :
      ( k1_relat_1(k2_funct_1(A_13)) = k2_relat_1(A_13)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28,plain,(
    ! [A_12] :
      ( v1_funct_1(k2_funct_1(A_12))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_60,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_145,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_148,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_145])).

tff(c_151,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_148])).

tff(c_165,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_172,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_165])).

tff(c_185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_172])).

tff(c_186,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_220,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_249,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_20,c_220])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_339,plain,(
    ! [A_70,B_71,C_72] :
      ( k1_relset_1(A_70,B_71,C_72) = k1_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_358,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_339])).

tff(c_1598,plain,(
    ! [B_158,A_159,C_160] :
      ( k1_xboole_0 = B_158
      | k1_relset_1(A_159,B_158,C_160) = A_159
      | ~ v1_funct_2(C_160,A_159,B_158)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_159,B_158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1611,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_1598])).

tff(c_1626,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_358,c_1611])).

tff(c_1630,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1626])).

tff(c_521,plain,(
    ! [A_92,B_93,C_94] :
      ( k2_relset_1(A_92,B_93,C_94) = k2_relat_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_531,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_521])).

tff(c_545,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_531])).

tff(c_30,plain,(
    ! [A_12] :
      ( v1_relat_1(k2_funct_1(A_12))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_187,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_327,plain,(
    ! [A_69] :
      ( k1_relat_1(k2_funct_1(A_69)) = k2_relat_1(A_69)
      | ~ v2_funct_1(A_69)
      | ~ v1_funct_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_56,plain,(
    ! [A_26] :
      ( v1_funct_2(A_26,k1_relat_1(A_26),k2_relat_1(A_26))
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1182,plain,(
    ! [A_145] :
      ( v1_funct_2(k2_funct_1(A_145),k2_relat_1(A_145),k2_relat_1(k2_funct_1(A_145)))
      | ~ v1_funct_1(k2_funct_1(A_145))
      | ~ v1_relat_1(k2_funct_1(A_145))
      | ~ v2_funct_1(A_145)
      | ~ v1_funct_1(A_145)
      | ~ v1_relat_1(A_145) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_56])).

tff(c_1185,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_545,c_1182])).

tff(c_1196,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_70,c_64,c_187,c_1185])).

tff(c_1216,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1196])).

tff(c_1219,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_1216])).

tff(c_1223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_70,c_1219])).

tff(c_1225,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1196])).

tff(c_792,plain,(
    ! [B_119,A_120,C_121] :
      ( k1_xboole_0 = B_119
      | k1_relset_1(A_120,B_119,C_121) = A_120
      | ~ v1_funct_2(C_121,A_120,B_119)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_120,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_805,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_792])).

tff(c_823,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_358,c_805])).

tff(c_827,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_823])).

tff(c_32,plain,(
    ! [A_13] :
      ( k2_relat_1(k2_funct_1(A_13)) = k1_relat_1(A_13)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_444,plain,(
    ! [A_88] :
      ( m1_subset_1(A_88,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_88),k2_relat_1(A_88))))
      | ~ v1_funct_1(A_88)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_493,plain,(
    ! [A_91] :
      ( r1_tarski(A_91,k2_zfmisc_1(k1_relat_1(A_91),k2_relat_1(A_91)))
      | ~ v1_funct_1(A_91)
      | ~ v1_relat_1(A_91) ) ),
    inference(resolution,[status(thm)],[c_444,c_18])).

tff(c_1238,plain,(
    ! [A_147] :
      ( r1_tarski(k2_funct_1(A_147),k2_zfmisc_1(k1_relat_1(k2_funct_1(A_147)),k1_relat_1(A_147)))
      | ~ v1_funct_1(k2_funct_1(A_147))
      | ~ v1_relat_1(k2_funct_1(A_147))
      | ~ v2_funct_1(A_147)
      | ~ v1_funct_1(A_147)
      | ~ v1_relat_1(A_147) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_493])).

tff(c_1258,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_827,c_1238])).

tff(c_1275,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_70,c_64,c_1225,c_187,c_1258])).

tff(c_1297,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1275])).

tff(c_1309,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_70,c_64,c_545,c_1297])).

tff(c_1311,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_1309])).

tff(c_1312,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_823])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1341,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1312,c_8])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1340,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1312,c_1312,c_12])).

tff(c_471,plain,(
    ! [A_88] :
      ( r1_tarski(A_88,k2_zfmisc_1(k1_relat_1(A_88),k2_relat_1(A_88)))
      | ~ v1_funct_1(A_88)
      | ~ v1_relat_1(A_88) ) ),
    inference(resolution,[status(thm)],[c_444,c_18])).

tff(c_551,plain,
    ( r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_545,c_471])).

tff(c_561,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_70,c_551])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_593,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_561,c_2])).

tff(c_692,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_593])).

tff(c_1513,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1340,c_692])).

tff(c_1523,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1341,c_1513])).

tff(c_1524,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_593])).

tff(c_1631,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1630,c_1524])).

tff(c_118,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,B_38)
      | ~ m1_subset_1(A_37,k1_zfmisc_1(B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_129,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_118])).

tff(c_132,plain,(
    ! [B_39,A_40] :
      ( B_39 = A_40
      | ~ r1_tarski(B_39,A_40)
      | ~ r1_tarski(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_139,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_129,c_132])).

tff(c_289,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_1658,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1631,c_289])).

tff(c_1663,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1658])).

tff(c_1664,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1626])).

tff(c_1693,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1664,c_8])).

tff(c_1692,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1664,c_1664,c_12])).

tff(c_1814,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1692,c_289])).

tff(c_1819,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1693,c_1814])).

tff(c_1820,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_1823,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1820,c_66])).

tff(c_2037,plain,(
    ! [A_194,B_195,C_196] :
      ( k2_relset_1(A_194,B_195,C_196) = k2_relat_1(C_196)
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(A_194,B_195))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2090,plain,(
    ! [C_203] :
      ( k2_relset_1('#skF_1','#skF_2',C_203) = k2_relat_1(C_203)
      | ~ m1_subset_1(C_203,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1820,c_2037])).

tff(c_2093,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1823,c_2090])).

tff(c_2103,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2093])).

tff(c_1984,plain,(
    ! [A_185,B_186,C_187] :
      ( k1_relset_1(A_185,B_186,C_187) = k1_relat_1(C_187)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2186,plain,(
    ! [C_208] :
      ( k1_relset_1('#skF_1','#skF_2',C_208) = k1_relat_1(C_208)
      | ~ m1_subset_1(C_208,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1820,c_1984])).

tff(c_2198,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1823,c_2186])).

tff(c_2954,plain,(
    ! [B_255,C_256,A_257] :
      ( k1_xboole_0 = B_255
      | v1_funct_2(C_256,A_257,B_255)
      | k1_relset_1(A_257,B_255,C_256) != A_257
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(A_257,B_255))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2963,plain,(
    ! [C_256] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_2(C_256,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',C_256) != '#skF_1'
      | ~ m1_subset_1(C_256,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1820,c_2954])).

tff(c_3051,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2963])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1832,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1820,c_10])).

tff(c_1869,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1832])).

tff(c_3069,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3051,c_1869])).

tff(c_3180,plain,(
    ! [A_269] : k2_zfmisc_1(A_269,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3051,c_3051,c_12])).

tff(c_2396,plain,(
    ! [B_233,C_234,A_235] :
      ( k1_xboole_0 = B_233
      | v1_funct_2(C_234,A_235,B_233)
      | k1_relset_1(A_235,B_233,C_234) != A_235
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1(A_235,B_233))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2405,plain,(
    ! [C_234] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_2(C_234,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',C_234) != '#skF_1'
      | ~ m1_subset_1(C_234,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1820,c_2396])).

tff(c_2527,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2405])).

tff(c_2557,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2527,c_8])).

tff(c_2556,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2527,c_2527,c_12])).

tff(c_1932,plain,(
    ! [A_183] :
      ( m1_subset_1(A_183,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_183),k2_relat_1(A_183))))
      | ~ v1_funct_1(A_183)
      | ~ v1_relat_1(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1955,plain,(
    ! [A_183] :
      ( r1_tarski(A_183,k2_zfmisc_1(k1_relat_1(A_183),k2_relat_1(A_183)))
      | ~ v1_funct_1(A_183)
      | ~ v1_relat_1(A_183) ) ),
    inference(resolution,[status(thm)],[c_1932,c_18])).

tff(c_2110,plain,
    ( r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2103,c_1955])).

tff(c_2120,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_70,c_2110])).

tff(c_2133,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_2120,c_2])).

tff(c_2315,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2133])).

tff(c_2734,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2556,c_2315])).

tff(c_2740,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2557,c_2734])).

tff(c_2742,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2405])).

tff(c_2760,plain,(
    ! [B_246,A_247,C_248] :
      ( k1_xboole_0 = B_246
      | k1_relset_1(A_247,B_246,C_248) = A_247
      | ~ v1_funct_2(C_248,A_247,B_246)
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(A_247,B_246))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2769,plain,(
    ! [C_248] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_248) = '#skF_1'
      | ~ v1_funct_2(C_248,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_248,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1820,c_2760])).

tff(c_2825,plain,(
    ! [C_251] :
      ( k1_relset_1('#skF_1','#skF_2',C_251) = '#skF_1'
      | ~ v1_funct_2(C_251,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_251,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2742,c_2769])).

tff(c_2828,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_1823,c_2825])).

tff(c_2839,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2198,c_2828])).

tff(c_2844,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2839,c_2315])).

tff(c_2854,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1820,c_2844])).

tff(c_2855,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2133])).

tff(c_3196,plain,(
    '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_3180,c_2855])).

tff(c_3225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3069,c_3196])).

tff(c_3227,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2963])).

tff(c_3357,plain,(
    ! [B_276,A_277,C_278] :
      ( k1_xboole_0 = B_276
      | k1_relset_1(A_277,B_276,C_278) = A_277
      | ~ v1_funct_2(C_278,A_277,B_276)
      | ~ m1_subset_1(C_278,k1_zfmisc_1(k2_zfmisc_1(A_277,B_276))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_3366,plain,(
    ! [C_278] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_278) = '#skF_1'
      | ~ v1_funct_2(C_278,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_278,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1820,c_3357])).

tff(c_3460,plain,(
    ! [C_282] :
      ( k1_relset_1('#skF_1','#skF_2',C_282) = '#skF_1'
      | ~ v1_funct_2(C_282,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_282,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3227,c_3366])).

tff(c_3463,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_1823,c_3460])).

tff(c_3474,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2198,c_3463])).

tff(c_1913,plain,(
    ! [A_180] :
      ( k2_relat_1(k2_funct_1(A_180)) = k1_relat_1(A_180)
      | ~ v2_funct_1(A_180)
      | ~ v1_funct_1(A_180)
      | ~ v1_relat_1(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3705,plain,(
    ! [A_296] :
      ( v1_funct_2(k2_funct_1(A_296),k1_relat_1(k2_funct_1(A_296)),k1_relat_1(A_296))
      | ~ v1_funct_1(k2_funct_1(A_296))
      | ~ v1_relat_1(k2_funct_1(A_296))
      | ~ v2_funct_1(A_296)
      | ~ v1_funct_1(A_296)
      | ~ v1_relat_1(A_296) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1913,c_56])).

tff(c_3708,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3474,c_3705])).

tff(c_3719,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_70,c_64,c_187,c_3708])).

tff(c_3722,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3719])).

tff(c_3725,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_3722])).

tff(c_3729,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_70,c_3725])).

tff(c_3731,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3719])).

tff(c_1960,plain,(
    ! [A_184] :
      ( r1_tarski(A_184,k2_zfmisc_1(k1_relat_1(A_184),k2_relat_1(A_184)))
      | ~ v1_funct_1(A_184)
      | ~ v1_relat_1(A_184) ) ),
    inference(resolution,[status(thm)],[c_1932,c_18])).

tff(c_3857,plain,(
    ! [A_303] :
      ( r1_tarski(k2_funct_1(A_303),k2_zfmisc_1(k1_relat_1(k2_funct_1(A_303)),k1_relat_1(A_303)))
      | ~ v1_funct_1(k2_funct_1(A_303))
      | ~ v1_relat_1(k2_funct_1(A_303))
      | ~ v2_funct_1(A_303)
      | ~ v1_funct_1(A_303)
      | ~ v1_relat_1(A_303) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1960])).

tff(c_3877,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3474,c_3857])).

tff(c_3894,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_70,c_64,c_3731,c_187,c_3877])).

tff(c_3916,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_3894])).

tff(c_3930,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_70,c_64,c_2103,c_3916])).

tff(c_3932,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_3930])).

tff(c_3934,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1832])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3942,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3934,c_3934,c_14])).

tff(c_3933,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1832])).

tff(c_4018,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3934,c_3934,c_3933])).

tff(c_4019,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4018])).

tff(c_4021,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4019,c_249])).

tff(c_4025,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3942,c_4021])).

tff(c_24,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3946,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3934,c_3934,c_24])).

tff(c_4103,plain,(
    ! [A_316] :
      ( k1_relat_1(k2_funct_1(A_316)) = k2_relat_1(A_316)
      | ~ v2_funct_1(A_316)
      | ~ v1_funct_1(A_316)
      | ~ v1_relat_1(A_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4681,plain,(
    ! [A_386] :
      ( v1_funct_2(k2_funct_1(A_386),k2_relat_1(A_386),k2_relat_1(k2_funct_1(A_386)))
      | ~ v1_funct_1(k2_funct_1(A_386))
      | ~ v1_relat_1(k2_funct_1(A_386))
      | ~ v2_funct_1(A_386)
      | ~ v1_funct_1(A_386)
      | ~ v1_relat_1(A_386) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4103,c_56])).

tff(c_4690,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3946,c_4681])).

tff(c_4692,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_70,c_64,c_187,c_4690])).

tff(c_4693,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_4692])).

tff(c_4696,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_4693])).

tff(c_4700,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_70,c_4696])).

tff(c_4702,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_4692])).

tff(c_4173,plain,(
    ! [A_331] :
      ( m1_subset_1(A_331,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_331),k2_relat_1(A_331))))
      | ~ v1_funct_1(A_331)
      | ~ v1_relat_1(A_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_4421,plain,(
    ! [A_366] :
      ( r1_tarski(A_366,k2_zfmisc_1(k1_relat_1(A_366),k2_relat_1(A_366)))
      | ~ v1_funct_1(A_366)
      | ~ v1_relat_1(A_366) ) ),
    inference(resolution,[status(thm)],[c_4173,c_18])).

tff(c_4863,plain,(
    ! [A_398] :
      ( r1_tarski(k2_funct_1(A_398),k2_zfmisc_1(k2_relat_1(A_398),k2_relat_1(k2_funct_1(A_398))))
      | ~ v1_funct_1(k2_funct_1(A_398))
      | ~ v1_relat_1(k2_funct_1(A_398))
      | ~ v2_funct_1(A_398)
      | ~ v1_funct_1(A_398)
      | ~ v1_relat_1(A_398) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_4421])).

tff(c_4889,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3946,c_4863])).

tff(c_4897,plain,(
    r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_70,c_64,c_4702,c_187,c_3942,c_4889])).

tff(c_4899,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4025,c_4897])).

tff(c_4900,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4018])).

tff(c_4901,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4018])).

tff(c_4924,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4900,c_4901])).

tff(c_4907,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4900,c_4900,c_3946])).

tff(c_16,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3943,plain,(
    ! [A_6] : m1_subset_1('#skF_3',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3934,c_16])).

tff(c_4904,plain,(
    ! [A_6] : m1_subset_1('#skF_1',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4900,c_3943])).

tff(c_5104,plain,(
    ! [A_415,B_416,C_417] :
      ( k2_relset_1(A_415,B_416,C_417) = k2_relat_1(C_417)
      | ~ m1_subset_1(C_417,k1_zfmisc_1(k2_zfmisc_1(A_415,B_416))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_5108,plain,(
    ! [A_415,B_416] : k2_relset_1(A_415,B_416,'#skF_1') = k2_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4904,c_5104])).

tff(c_5120,plain,(
    ! [A_415,B_416] : k2_relset_1(A_415,B_416,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4907,c_5108])).

tff(c_4916,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4900,c_62])).

tff(c_5122,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5120,c_4916])).

tff(c_5124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4924,c_5122])).

tff(c_5125,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_5302,plain,(
    ! [A_447,B_448,C_449] :
      ( k2_relset_1(A_447,B_448,C_449) = k2_relat_1(C_449)
      | ~ m1_subset_1(C_449,k1_zfmisc_1(k2_zfmisc_1(A_447,B_448))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_5312,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_5302])).

tff(c_5326,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_5312])).

tff(c_5126,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_5269,plain,(
    ! [A_442,B_443,C_444] :
      ( k1_relset_1(A_442,B_443,C_444) = k1_relat_1(C_444)
      | ~ m1_subset_1(C_444,k1_zfmisc_1(k2_zfmisc_1(A_442,B_443))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_5290,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_5126,c_5269])).

tff(c_5782,plain,(
    ! [B_490,C_491,A_492] :
      ( k1_xboole_0 = B_490
      | v1_funct_2(C_491,A_492,B_490)
      | k1_relset_1(A_492,B_490,C_491) != A_492
      | ~ m1_subset_1(C_491,k1_zfmisc_1(k2_zfmisc_1(A_492,B_490))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_5791,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_5126,c_5782])).

tff(c_5814,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5290,c_5791])).

tff(c_5815,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_5125,c_5814])).

tff(c_5822,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_5815])).

tff(c_5825,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_5822])).

tff(c_5828,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_70,c_64,c_5326,c_5825])).

tff(c_5829,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5815])).

tff(c_5858,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5829,c_8])).

tff(c_5857,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5829,c_5829,c_12])).

tff(c_5146,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_5126,c_18])).

tff(c_5162,plain,
    ( k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3')
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_5146,c_2])).

tff(c_5208,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_5162])).

tff(c_6086,plain,(
    ~ r1_tarski('#skF_1',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5857,c_5208])).

tff(c_6091,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5858,c_6086])).

tff(c_6092,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_5162])).

tff(c_6095,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6092,c_5126])).

tff(c_6201,plain,(
    ! [A_513,B_514,C_515] :
      ( k1_relset_1(A_513,B_514,C_515) = k1_relat_1(C_515)
      | ~ m1_subset_1(C_515,k1_zfmisc_1(k2_zfmisc_1(A_513,B_514))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6300,plain,(
    ! [C_525] :
      ( k1_relset_1('#skF_2','#skF_1',C_525) = k1_relat_1(C_525)
      | ~ m1_subset_1(C_525,k1_zfmisc_1(k2_funct_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6092,c_6201])).

tff(c_6312,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6095,c_6300])).

tff(c_6783,plain,(
    ! [B_567,C_568,A_569] :
      ( k1_xboole_0 = B_567
      | v1_funct_2(C_568,A_569,B_567)
      | k1_relset_1(A_569,B_567,C_568) != A_569
      | ~ m1_subset_1(C_568,k1_zfmisc_1(k2_zfmisc_1(A_569,B_567))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_6792,plain,(
    ! [C_568] :
      ( k1_xboole_0 = '#skF_1'
      | v1_funct_2(C_568,'#skF_2','#skF_1')
      | k1_relset_1('#skF_2','#skF_1',C_568) != '#skF_2'
      | ~ m1_subset_1(C_568,k1_zfmisc_1(k2_funct_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6092,c_6783])).

tff(c_6857,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_6792])).

tff(c_6102,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k2_funct_1('#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6092,c_10])).

tff(c_6145,plain,(
    k2_funct_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_6102])).

tff(c_6876,plain,(
    k2_funct_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6857,c_6145])).

tff(c_6886,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6857,c_6857,c_12])).

tff(c_7025,plain,(
    k2_funct_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6886,c_6092])).

tff(c_7027,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6876,c_7025])).

tff(c_7030,plain,(
    ! [C_578] :
      ( v1_funct_2(C_578,'#skF_2','#skF_1')
      | k1_relset_1('#skF_2','#skF_1',C_578) != '#skF_2'
      | ~ m1_subset_1(C_578,k1_zfmisc_1(k2_funct_1('#skF_3'))) ) ),
    inference(splitRight,[status(thm)],[c_6792])).

tff(c_7033,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_6095,c_7030])).

tff(c_7043,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6312,c_7033])).

tff(c_7044,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_5125,c_7043])).

tff(c_7050,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_7044])).

tff(c_7053,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_70,c_64,c_6453,c_7050])).

tff(c_7054,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_6102])).

tff(c_7090,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_7054])).

tff(c_7104,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7090,c_8])).

tff(c_7101,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7090,c_7090,c_14])).

tff(c_5207,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_7209,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7101,c_5207])).

tff(c_7214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7104,c_7209])).

tff(c_7215,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_7054])).

tff(c_7230,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7215,c_8])).

tff(c_7229,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7215,c_7215,c_12])).

tff(c_7364,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7229,c_5207])).

tff(c_7369,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7230,c_7364])).

tff(c_7370,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_7373,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7370,c_66])).

tff(c_7480,plain,(
    ! [A_603,B_604,C_605] :
      ( k2_relset_1(A_603,B_604,C_605) = k2_relat_1(C_605)
      | ~ m1_subset_1(C_605,k1_zfmisc_1(k2_zfmisc_1(A_603,B_604))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_7554,plain,(
    ! [C_616] :
      ( k2_relset_1('#skF_1','#skF_2',C_616) = k2_relat_1(C_616)
      | ~ m1_subset_1(C_616,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7370,c_7480])).

tff(c_7557,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_7373,c_7554])).

tff(c_7567,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_7557])).

tff(c_7757,plain,(
    ! [A_628,B_629,C_630] :
      ( k1_relset_1(A_628,B_629,C_630) = k1_relat_1(C_630)
      | ~ m1_subset_1(C_630,k1_zfmisc_1(k2_zfmisc_1(A_628,B_629))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_7786,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_5126,c_7757])).

tff(c_7947,plain,(
    ! [B_651,C_652,A_653] :
      ( k1_xboole_0 = B_651
      | v1_funct_2(C_652,A_653,B_651)
      | k1_relset_1(A_653,B_651,C_652) != A_653
      | ~ m1_subset_1(C_652,k1_zfmisc_1(k2_zfmisc_1(A_653,B_651))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_7959,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_5126,c_7947])).

tff(c_7979,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7786,c_7959])).

tff(c_7980,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_5125,c_7979])).

tff(c_7985,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_7980])).

tff(c_7988,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_7985])).

tff(c_7991,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_70,c_64,c_7567,c_7988])).

tff(c_7992,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_7980])).

tff(c_7380,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_7370,c_10])).

tff(c_7441,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_7380])).

tff(c_8010,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7992,c_7441])).

tff(c_8018,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7992,c_7992,c_14])).

tff(c_8157,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8018,c_7370])).

tff(c_8159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8010,c_8157])).

tff(c_8161,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_7380])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8174,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8161,c_8161,c_26])).

tff(c_8170,plain,(
    ! [A_6] : m1_subset_1('#skF_3',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8161,c_16])).

tff(c_8736,plain,(
    ! [A_694,B_695,C_696] :
      ( k1_relset_1(A_694,B_695,C_696) = k1_relat_1(C_696)
      | ~ m1_subset_1(C_696,k1_zfmisc_1(k2_zfmisc_1(A_694,B_695))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_8740,plain,(
    ! [A_694,B_695] : k1_relset_1(A_694,B_695,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8170,c_8736])).

tff(c_8752,plain,(
    ! [A_694,B_695] : k1_relset_1(A_694,B_695,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8174,c_8740])).

tff(c_48,plain,(
    ! [B_24,C_25,A_23] :
      ( k1_xboole_0 = B_24
      | v1_funct_2(C_25,A_23,B_24)
      | k1_relset_1(A_23,B_24,C_25) != A_23
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_8928,plain,(
    ! [B_723,C_724,A_725] :
      ( B_723 = '#skF_3'
      | v1_funct_2(C_724,A_725,B_723)
      | k1_relset_1(A_725,B_723,C_724) != A_725
      | ~ m1_subset_1(C_724,k1_zfmisc_1(k2_zfmisc_1(A_725,B_723))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8161,c_48])).

tff(c_8935,plain,(
    ! [B_723,A_725] :
      ( B_723 = '#skF_3'
      | v1_funct_2('#skF_3',A_725,B_723)
      | k1_relset_1(A_725,B_723,'#skF_3') != A_725 ) ),
    inference(resolution,[status(thm)],[c_8170,c_8928])).

tff(c_8952,plain,(
    ! [B_726,A_727] :
      ( B_726 = '#skF_3'
      | v1_funct_2('#skF_3',A_727,B_726)
      | A_727 != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8752,c_8935])).

tff(c_8172,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8161,c_8])).

tff(c_8169,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8161,c_8161,c_14])).

tff(c_8160,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_7380])).

tff(c_8578,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8161,c_8161,c_8160])).

tff(c_8579,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_8578])).

tff(c_8582,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8579,c_5146])).

tff(c_8589,plain,(
    r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8169,c_8582])).

tff(c_8621,plain,
    ( k2_funct_1('#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_8589,c_2])).

tff(c_8626,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8172,c_8621])).

tff(c_8584,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8579,c_5125])).

tff(c_8682,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8626,c_8584])).

tff(c_8963,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_8952,c_8682])).

tff(c_8586,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8579,c_68])).

tff(c_8983,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8963,c_8963,c_8586])).

tff(c_8980,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8963,c_8963,c_8682])).

tff(c_9116,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8983,c_8980])).

tff(c_9117,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_8578])).

tff(c_9118,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8578])).

tff(c_9158,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9117,c_9118])).

tff(c_42,plain,(
    ! [A_23] :
      ( v1_funct_2(k1_xboole_0,A_23,k1_xboole_0)
      | k1_xboole_0 = A_23
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_23,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_72,plain,(
    ! [A_23] :
      ( v1_funct_2(k1_xboole_0,A_23,k1_xboole_0)
      | k1_xboole_0 = A_23 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_42])).

tff(c_8168,plain,(
    ! [A_23] :
      ( v1_funct_2('#skF_3',A_23,'#skF_3')
      | A_23 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8161,c_8161,c_8161,c_72])).

tff(c_9410,plain,(
    ! [A_752] :
      ( v1_funct_2('#skF_1',A_752,'#skF_1')
      | A_752 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9117,c_9117,c_9117,c_8168])).

tff(c_8171,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8161,c_8161,c_12])).

tff(c_9135,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9117,c_9117,c_8171])).

tff(c_8252,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8161,c_8161,c_8160])).

tff(c_8253,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_8252])).

tff(c_8251,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_5162])).

tff(c_8359,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8172,c_8169,c_8253,c_8251])).

tff(c_8360,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_8252])).

tff(c_8361,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8252])).

tff(c_8400,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8360,c_8361])).

tff(c_8173,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8161,c_8161,c_24])).

tff(c_8377,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8360,c_8360,c_8173])).

tff(c_8445,plain,(
    ! [A_6] : m1_subset_1('#skF_1',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8360,c_8170])).

tff(c_8553,plain,(
    ! [A_675,B_676,C_677] :
      ( k2_relset_1(A_675,B_676,C_677) = k2_relat_1(C_677)
      | ~ m1_subset_1(C_677,k1_zfmisc_1(k2_zfmisc_1(A_675,B_676))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_8563,plain,(
    ! [A_675,B_676] : k2_relset_1(A_675,B_676,'#skF_1') = k2_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8445,c_8553])).

tff(c_8569,plain,(
    ! [A_675,B_676] : k2_relset_1(A_675,B_676,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8377,c_8563])).

tff(c_8392,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8360,c_62])).

tff(c_8573,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8569,c_8392])).

tff(c_8575,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8400,c_8573])).

tff(c_8576,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_5162])).

tff(c_9134,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9117,c_8576])).

tff(c_9274,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9135,c_9134])).

tff(c_9147,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9117,c_5125])).

tff(c_9358,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9274,c_9147])).

tff(c_9413,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_9410,c_9358])).

tff(c_9417,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9158,c_9413])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:49:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.25/3.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.50/3.75  
% 10.50/3.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.50/3.76  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 10.50/3.76  
% 10.50/3.76  %Foreground sorts:
% 10.50/3.76  
% 10.50/3.76  
% 10.50/3.76  %Background operators:
% 10.50/3.76  
% 10.50/3.76  
% 10.50/3.76  %Foreground operators:
% 10.50/3.76  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.50/3.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.50/3.76  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 10.50/3.76  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.50/3.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.50/3.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.50/3.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.50/3.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.50/3.76  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.50/3.76  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.50/3.76  tff('#skF_2', type, '#skF_2': $i).
% 10.50/3.76  tff('#skF_3', type, '#skF_3': $i).
% 10.50/3.76  tff('#skF_1', type, '#skF_1': $i).
% 10.50/3.76  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.50/3.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.50/3.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.50/3.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.50/3.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.50/3.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.50/3.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.50/3.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.50/3.76  
% 10.64/3.81  tff(f_129, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 10.64/3.81  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.64/3.81  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.64/3.81  tff(f_72, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 10.64/3.81  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.64/3.81  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 10.64/3.81  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.64/3.81  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.64/3.81  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 10.64/3.81  tff(f_112, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 10.64/3.81  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 10.64/3.81  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 10.64/3.81  tff(f_54, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 10.64/3.81  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 10.64/3.81  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 10.64/3.81  tff(c_188, plain, (![C_45, A_46, B_47]: (v1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.64/3.81  tff(c_205, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_188])).
% 10.64/3.81  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 10.64/3.81  tff(c_64, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 10.64/3.81  tff(c_62, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_129])).
% 10.64/3.81  tff(c_6426, plain, (![A_537, B_538, C_539]: (k2_relset_1(A_537, B_538, C_539)=k2_relat_1(C_539) | ~m1_subset_1(C_539, k1_zfmisc_1(k2_zfmisc_1(A_537, B_538))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.64/3.81  tff(c_6439, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_6426])).
% 10.64/3.81  tff(c_6453, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_6439])).
% 10.64/3.81  tff(c_34, plain, (![A_13]: (k1_relat_1(k2_funct_1(A_13))=k2_relat_1(A_13) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.64/3.81  tff(c_20, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.64/3.81  tff(c_28, plain, (![A_12]: (v1_funct_1(k2_funct_1(A_12)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.64/3.81  tff(c_60, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 10.64/3.81  tff(c_145, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_60])).
% 10.64/3.81  tff(c_148, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_145])).
% 10.64/3.81  tff(c_151, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_148])).
% 10.64/3.81  tff(c_165, plain, (![C_42, A_43, B_44]: (v1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.64/3.81  tff(c_172, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_165])).
% 10.64/3.81  tff(c_185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_151, c_172])).
% 10.64/3.81  tff(c_186, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_60])).
% 10.64/3.81  tff(c_220, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_186])).
% 10.64/3.81  tff(c_249, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_20, c_220])).
% 10.64/3.81  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.64/3.81  tff(c_68, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 10.64/3.81  tff(c_339, plain, (![A_70, B_71, C_72]: (k1_relset_1(A_70, B_71, C_72)=k1_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.64/3.81  tff(c_358, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_339])).
% 10.64/3.81  tff(c_1598, plain, (![B_158, A_159, C_160]: (k1_xboole_0=B_158 | k1_relset_1(A_159, B_158, C_160)=A_159 | ~v1_funct_2(C_160, A_159, B_158) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_159, B_158))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.64/3.81  tff(c_1611, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_1598])).
% 10.64/3.81  tff(c_1626, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_358, c_1611])).
% 10.64/3.81  tff(c_1630, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_1626])).
% 10.64/3.81  tff(c_521, plain, (![A_92, B_93, C_94]: (k2_relset_1(A_92, B_93, C_94)=k2_relat_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.64/3.81  tff(c_531, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_521])).
% 10.64/3.81  tff(c_545, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_531])).
% 10.64/3.81  tff(c_30, plain, (![A_12]: (v1_relat_1(k2_funct_1(A_12)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.64/3.81  tff(c_187, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_60])).
% 10.64/3.81  tff(c_327, plain, (![A_69]: (k1_relat_1(k2_funct_1(A_69))=k2_relat_1(A_69) | ~v2_funct_1(A_69) | ~v1_funct_1(A_69) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.64/3.81  tff(c_56, plain, (![A_26]: (v1_funct_2(A_26, k1_relat_1(A_26), k2_relat_1(A_26)) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_112])).
% 10.64/3.81  tff(c_1182, plain, (![A_145]: (v1_funct_2(k2_funct_1(A_145), k2_relat_1(A_145), k2_relat_1(k2_funct_1(A_145))) | ~v1_funct_1(k2_funct_1(A_145)) | ~v1_relat_1(k2_funct_1(A_145)) | ~v2_funct_1(A_145) | ~v1_funct_1(A_145) | ~v1_relat_1(A_145))), inference(superposition, [status(thm), theory('equality')], [c_327, c_56])).
% 10.64/3.81  tff(c_1185, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_545, c_1182])).
% 10.64/3.81  tff(c_1196, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_70, c_64, c_187, c_1185])).
% 10.64/3.81  tff(c_1216, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1196])).
% 10.64/3.81  tff(c_1219, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_1216])).
% 10.64/3.81  tff(c_1223, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_205, c_70, c_1219])).
% 10.64/3.81  tff(c_1225, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1196])).
% 10.64/3.81  tff(c_792, plain, (![B_119, A_120, C_121]: (k1_xboole_0=B_119 | k1_relset_1(A_120, B_119, C_121)=A_120 | ~v1_funct_2(C_121, A_120, B_119) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_120, B_119))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.64/3.81  tff(c_805, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_792])).
% 10.64/3.81  tff(c_823, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_358, c_805])).
% 10.64/3.81  tff(c_827, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_823])).
% 10.64/3.81  tff(c_32, plain, (![A_13]: (k2_relat_1(k2_funct_1(A_13))=k1_relat_1(A_13) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.64/3.81  tff(c_444, plain, (![A_88]: (m1_subset_1(A_88, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_88), k2_relat_1(A_88)))) | ~v1_funct_1(A_88) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_112])).
% 10.64/3.81  tff(c_18, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.64/3.81  tff(c_493, plain, (![A_91]: (r1_tarski(A_91, k2_zfmisc_1(k1_relat_1(A_91), k2_relat_1(A_91))) | ~v1_funct_1(A_91) | ~v1_relat_1(A_91))), inference(resolution, [status(thm)], [c_444, c_18])).
% 10.64/3.81  tff(c_1238, plain, (![A_147]: (r1_tarski(k2_funct_1(A_147), k2_zfmisc_1(k1_relat_1(k2_funct_1(A_147)), k1_relat_1(A_147))) | ~v1_funct_1(k2_funct_1(A_147)) | ~v1_relat_1(k2_funct_1(A_147)) | ~v2_funct_1(A_147) | ~v1_funct_1(A_147) | ~v1_relat_1(A_147))), inference(superposition, [status(thm), theory('equality')], [c_32, c_493])).
% 10.64/3.81  tff(c_1258, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_827, c_1238])).
% 10.64/3.81  tff(c_1275, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_70, c_64, c_1225, c_187, c_1258])).
% 10.64/3.81  tff(c_1297, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34, c_1275])).
% 10.64/3.81  tff(c_1309, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_70, c_64, c_545, c_1297])).
% 10.64/3.81  tff(c_1311, plain, $false, inference(negUnitSimplification, [status(thm)], [c_249, c_1309])).
% 10.64/3.81  tff(c_1312, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_823])).
% 10.64/3.81  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.64/3.81  tff(c_1341, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1312, c_8])).
% 10.64/3.81  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.64/3.81  tff(c_1340, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1312, c_1312, c_12])).
% 10.64/3.81  tff(c_471, plain, (![A_88]: (r1_tarski(A_88, k2_zfmisc_1(k1_relat_1(A_88), k2_relat_1(A_88))) | ~v1_funct_1(A_88) | ~v1_relat_1(A_88))), inference(resolution, [status(thm)], [c_444, c_18])).
% 10.64/3.81  tff(c_551, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_545, c_471])).
% 10.64/3.81  tff(c_561, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_70, c_551])).
% 10.64/3.81  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.64/3.81  tff(c_593, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_561, c_2])).
% 10.64/3.81  tff(c_692, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_593])).
% 10.64/3.81  tff(c_1513, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1340, c_692])).
% 10.64/3.81  tff(c_1523, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1341, c_1513])).
% 10.64/3.81  tff(c_1524, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_593])).
% 10.64/3.81  tff(c_1631, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1630, c_1524])).
% 10.64/3.81  tff(c_118, plain, (![A_37, B_38]: (r1_tarski(A_37, B_38) | ~m1_subset_1(A_37, k1_zfmisc_1(B_38)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.64/3.81  tff(c_129, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_118])).
% 10.64/3.81  tff(c_132, plain, (![B_39, A_40]: (B_39=A_40 | ~r1_tarski(B_39, A_40) | ~r1_tarski(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.64/3.81  tff(c_139, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_129, c_132])).
% 10.64/3.81  tff(c_289, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_139])).
% 10.64/3.81  tff(c_1658, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1631, c_289])).
% 10.64/3.81  tff(c_1663, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1658])).
% 10.64/3.81  tff(c_1664, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1626])).
% 10.64/3.81  tff(c_1693, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1664, c_8])).
% 10.64/3.81  tff(c_1692, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1664, c_1664, c_12])).
% 10.64/3.81  tff(c_1814, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1692, c_289])).
% 10.64/3.81  tff(c_1819, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1693, c_1814])).
% 10.64/3.81  tff(c_1820, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_139])).
% 10.64/3.81  tff(c_1823, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1820, c_66])).
% 10.64/3.81  tff(c_2037, plain, (![A_194, B_195, C_196]: (k2_relset_1(A_194, B_195, C_196)=k2_relat_1(C_196) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(A_194, B_195))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.64/3.81  tff(c_2090, plain, (![C_203]: (k2_relset_1('#skF_1', '#skF_2', C_203)=k2_relat_1(C_203) | ~m1_subset_1(C_203, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1820, c_2037])).
% 10.64/3.81  tff(c_2093, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1823, c_2090])).
% 10.64/3.81  tff(c_2103, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2093])).
% 10.64/3.81  tff(c_1984, plain, (![A_185, B_186, C_187]: (k1_relset_1(A_185, B_186, C_187)=k1_relat_1(C_187) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.64/3.81  tff(c_2186, plain, (![C_208]: (k1_relset_1('#skF_1', '#skF_2', C_208)=k1_relat_1(C_208) | ~m1_subset_1(C_208, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1820, c_1984])).
% 10.64/3.81  tff(c_2198, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1823, c_2186])).
% 10.64/3.81  tff(c_2954, plain, (![B_255, C_256, A_257]: (k1_xboole_0=B_255 | v1_funct_2(C_256, A_257, B_255) | k1_relset_1(A_257, B_255, C_256)!=A_257 | ~m1_subset_1(C_256, k1_zfmisc_1(k2_zfmisc_1(A_257, B_255))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.64/3.81  tff(c_2963, plain, (![C_256]: (k1_xboole_0='#skF_2' | v1_funct_2(C_256, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', C_256)!='#skF_1' | ~m1_subset_1(C_256, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1820, c_2954])).
% 10.64/3.81  tff(c_3051, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_2963])).
% 10.64/3.81  tff(c_10, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.64/3.81  tff(c_1832, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1820, c_10])).
% 10.64/3.81  tff(c_1869, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_1832])).
% 10.64/3.81  tff(c_3069, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3051, c_1869])).
% 10.64/3.81  tff(c_3180, plain, (![A_269]: (k2_zfmisc_1(A_269, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3051, c_3051, c_12])).
% 10.64/3.81  tff(c_2396, plain, (![B_233, C_234, A_235]: (k1_xboole_0=B_233 | v1_funct_2(C_234, A_235, B_233) | k1_relset_1(A_235, B_233, C_234)!=A_235 | ~m1_subset_1(C_234, k1_zfmisc_1(k2_zfmisc_1(A_235, B_233))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.64/3.81  tff(c_2405, plain, (![C_234]: (k1_xboole_0='#skF_2' | v1_funct_2(C_234, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', C_234)!='#skF_1' | ~m1_subset_1(C_234, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1820, c_2396])).
% 10.64/3.81  tff(c_2527, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_2405])).
% 10.64/3.81  tff(c_2557, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2527, c_8])).
% 10.64/3.81  tff(c_2556, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2527, c_2527, c_12])).
% 10.64/3.81  tff(c_1932, plain, (![A_183]: (m1_subset_1(A_183, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_183), k2_relat_1(A_183)))) | ~v1_funct_1(A_183) | ~v1_relat_1(A_183))), inference(cnfTransformation, [status(thm)], [f_112])).
% 10.64/3.81  tff(c_1955, plain, (![A_183]: (r1_tarski(A_183, k2_zfmisc_1(k1_relat_1(A_183), k2_relat_1(A_183))) | ~v1_funct_1(A_183) | ~v1_relat_1(A_183))), inference(resolution, [status(thm)], [c_1932, c_18])).
% 10.64/3.81  tff(c_2110, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2103, c_1955])).
% 10.64/3.81  tff(c_2120, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_70, c_2110])).
% 10.64/3.81  tff(c_2133, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_2120, c_2])).
% 10.64/3.81  tff(c_2315, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_2133])).
% 10.64/3.81  tff(c_2734, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2556, c_2315])).
% 10.64/3.81  tff(c_2740, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2557, c_2734])).
% 10.64/3.81  tff(c_2742, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_2405])).
% 10.64/3.81  tff(c_2760, plain, (![B_246, A_247, C_248]: (k1_xboole_0=B_246 | k1_relset_1(A_247, B_246, C_248)=A_247 | ~v1_funct_2(C_248, A_247, B_246) | ~m1_subset_1(C_248, k1_zfmisc_1(k2_zfmisc_1(A_247, B_246))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.64/3.81  tff(c_2769, plain, (![C_248]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_248)='#skF_1' | ~v1_funct_2(C_248, '#skF_1', '#skF_2') | ~m1_subset_1(C_248, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1820, c_2760])).
% 10.64/3.81  tff(c_2825, plain, (![C_251]: (k1_relset_1('#skF_1', '#skF_2', C_251)='#skF_1' | ~v1_funct_2(C_251, '#skF_1', '#skF_2') | ~m1_subset_1(C_251, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_2742, c_2769])).
% 10.64/3.81  tff(c_2828, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_1823, c_2825])).
% 10.64/3.81  tff(c_2839, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2198, c_2828])).
% 10.64/3.81  tff(c_2844, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2839, c_2315])).
% 10.64/3.81  tff(c_2854, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1820, c_2844])).
% 10.64/3.81  tff(c_2855, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_2133])).
% 10.64/3.81  tff(c_3196, plain, ('#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_3180, c_2855])).
% 10.64/3.81  tff(c_3225, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3069, c_3196])).
% 10.64/3.81  tff(c_3227, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_2963])).
% 10.64/3.81  tff(c_3357, plain, (![B_276, A_277, C_278]: (k1_xboole_0=B_276 | k1_relset_1(A_277, B_276, C_278)=A_277 | ~v1_funct_2(C_278, A_277, B_276) | ~m1_subset_1(C_278, k1_zfmisc_1(k2_zfmisc_1(A_277, B_276))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.64/3.81  tff(c_3366, plain, (![C_278]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_278)='#skF_1' | ~v1_funct_2(C_278, '#skF_1', '#skF_2') | ~m1_subset_1(C_278, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1820, c_3357])).
% 10.64/3.81  tff(c_3460, plain, (![C_282]: (k1_relset_1('#skF_1', '#skF_2', C_282)='#skF_1' | ~v1_funct_2(C_282, '#skF_1', '#skF_2') | ~m1_subset_1(C_282, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_3227, c_3366])).
% 10.64/3.81  tff(c_3463, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_1823, c_3460])).
% 10.64/3.81  tff(c_3474, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2198, c_3463])).
% 10.64/3.81  tff(c_1913, plain, (![A_180]: (k2_relat_1(k2_funct_1(A_180))=k1_relat_1(A_180) | ~v2_funct_1(A_180) | ~v1_funct_1(A_180) | ~v1_relat_1(A_180))), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.64/3.81  tff(c_3705, plain, (![A_296]: (v1_funct_2(k2_funct_1(A_296), k1_relat_1(k2_funct_1(A_296)), k1_relat_1(A_296)) | ~v1_funct_1(k2_funct_1(A_296)) | ~v1_relat_1(k2_funct_1(A_296)) | ~v2_funct_1(A_296) | ~v1_funct_1(A_296) | ~v1_relat_1(A_296))), inference(superposition, [status(thm), theory('equality')], [c_1913, c_56])).
% 10.64/3.81  tff(c_3708, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3474, c_3705])).
% 10.64/3.81  tff(c_3719, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_70, c_64, c_187, c_3708])).
% 10.64/3.81  tff(c_3722, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_3719])).
% 10.64/3.81  tff(c_3725, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_3722])).
% 10.64/3.81  tff(c_3729, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_205, c_70, c_3725])).
% 10.64/3.81  tff(c_3731, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_3719])).
% 10.64/3.81  tff(c_1960, plain, (![A_184]: (r1_tarski(A_184, k2_zfmisc_1(k1_relat_1(A_184), k2_relat_1(A_184))) | ~v1_funct_1(A_184) | ~v1_relat_1(A_184))), inference(resolution, [status(thm)], [c_1932, c_18])).
% 10.64/3.81  tff(c_3857, plain, (![A_303]: (r1_tarski(k2_funct_1(A_303), k2_zfmisc_1(k1_relat_1(k2_funct_1(A_303)), k1_relat_1(A_303))) | ~v1_funct_1(k2_funct_1(A_303)) | ~v1_relat_1(k2_funct_1(A_303)) | ~v2_funct_1(A_303) | ~v1_funct_1(A_303) | ~v1_relat_1(A_303))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1960])).
% 10.64/3.81  tff(c_3877, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3474, c_3857])).
% 10.64/3.81  tff(c_3894, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_70, c_64, c_3731, c_187, c_3877])).
% 10.64/3.81  tff(c_3916, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34, c_3894])).
% 10.64/3.81  tff(c_3930, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_70, c_64, c_2103, c_3916])).
% 10.64/3.81  tff(c_3932, plain, $false, inference(negUnitSimplification, [status(thm)], [c_249, c_3930])).
% 10.64/3.81  tff(c_3934, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1832])).
% 10.64/3.81  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.64/3.81  tff(c_3942, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3934, c_3934, c_14])).
% 10.64/3.81  tff(c_3933, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1832])).
% 10.64/3.81  tff(c_4018, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3934, c_3934, c_3933])).
% 10.64/3.81  tff(c_4019, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_4018])).
% 10.64/3.81  tff(c_4021, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4019, c_249])).
% 10.64/3.81  tff(c_4025, plain, (~r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3942, c_4021])).
% 10.64/3.81  tff(c_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.64/3.81  tff(c_3946, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3934, c_3934, c_24])).
% 10.64/3.81  tff(c_4103, plain, (![A_316]: (k1_relat_1(k2_funct_1(A_316))=k2_relat_1(A_316) | ~v2_funct_1(A_316) | ~v1_funct_1(A_316) | ~v1_relat_1(A_316))), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.64/3.81  tff(c_4681, plain, (![A_386]: (v1_funct_2(k2_funct_1(A_386), k2_relat_1(A_386), k2_relat_1(k2_funct_1(A_386))) | ~v1_funct_1(k2_funct_1(A_386)) | ~v1_relat_1(k2_funct_1(A_386)) | ~v2_funct_1(A_386) | ~v1_funct_1(A_386) | ~v1_relat_1(A_386))), inference(superposition, [status(thm), theory('equality')], [c_4103, c_56])).
% 10.64/3.81  tff(c_4690, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3946, c_4681])).
% 10.64/3.81  tff(c_4692, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_70, c_64, c_187, c_4690])).
% 10.64/3.81  tff(c_4693, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_4692])).
% 10.64/3.81  tff(c_4696, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_4693])).
% 10.64/3.81  tff(c_4700, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_205, c_70, c_4696])).
% 10.64/3.81  tff(c_4702, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_4692])).
% 10.64/3.81  tff(c_4173, plain, (![A_331]: (m1_subset_1(A_331, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_331), k2_relat_1(A_331)))) | ~v1_funct_1(A_331) | ~v1_relat_1(A_331))), inference(cnfTransformation, [status(thm)], [f_112])).
% 10.64/3.81  tff(c_4421, plain, (![A_366]: (r1_tarski(A_366, k2_zfmisc_1(k1_relat_1(A_366), k2_relat_1(A_366))) | ~v1_funct_1(A_366) | ~v1_relat_1(A_366))), inference(resolution, [status(thm)], [c_4173, c_18])).
% 10.64/3.81  tff(c_4863, plain, (![A_398]: (r1_tarski(k2_funct_1(A_398), k2_zfmisc_1(k2_relat_1(A_398), k2_relat_1(k2_funct_1(A_398)))) | ~v1_funct_1(k2_funct_1(A_398)) | ~v1_relat_1(k2_funct_1(A_398)) | ~v2_funct_1(A_398) | ~v1_funct_1(A_398) | ~v1_relat_1(A_398))), inference(superposition, [status(thm), theory('equality')], [c_34, c_4421])).
% 10.64/3.81  tff(c_4889, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_3')))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3946, c_4863])).
% 10.64/3.81  tff(c_4897, plain, (r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_205, c_70, c_64, c_4702, c_187, c_3942, c_4889])).
% 10.64/3.81  tff(c_4899, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4025, c_4897])).
% 10.64/3.81  tff(c_4900, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_4018])).
% 10.64/3.81  tff(c_4901, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_4018])).
% 10.64/3.81  tff(c_4924, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4900, c_4901])).
% 10.64/3.81  tff(c_4907, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4900, c_4900, c_3946])).
% 10.64/3.81  tff(c_16, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.64/3.81  tff(c_3943, plain, (![A_6]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_3934, c_16])).
% 10.64/3.81  tff(c_4904, plain, (![A_6]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_4900, c_3943])).
% 10.64/3.81  tff(c_5104, plain, (![A_415, B_416, C_417]: (k2_relset_1(A_415, B_416, C_417)=k2_relat_1(C_417) | ~m1_subset_1(C_417, k1_zfmisc_1(k2_zfmisc_1(A_415, B_416))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.64/3.81  tff(c_5108, plain, (![A_415, B_416]: (k2_relset_1(A_415, B_416, '#skF_1')=k2_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_4904, c_5104])).
% 10.64/3.81  tff(c_5120, plain, (![A_415, B_416]: (k2_relset_1(A_415, B_416, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4907, c_5108])).
% 10.64/3.81  tff(c_4916, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4900, c_62])).
% 10.64/3.81  tff(c_5122, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5120, c_4916])).
% 10.64/3.81  tff(c_5124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4924, c_5122])).
% 10.64/3.81  tff(c_5125, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_186])).
% 10.64/3.81  tff(c_5302, plain, (![A_447, B_448, C_449]: (k2_relset_1(A_447, B_448, C_449)=k2_relat_1(C_449) | ~m1_subset_1(C_449, k1_zfmisc_1(k2_zfmisc_1(A_447, B_448))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.64/3.81  tff(c_5312, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_5302])).
% 10.64/3.81  tff(c_5326, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_5312])).
% 10.64/3.81  tff(c_5126, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_186])).
% 10.64/3.81  tff(c_5269, plain, (![A_442, B_443, C_444]: (k1_relset_1(A_442, B_443, C_444)=k1_relat_1(C_444) | ~m1_subset_1(C_444, k1_zfmisc_1(k2_zfmisc_1(A_442, B_443))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.64/3.81  tff(c_5290, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_5126, c_5269])).
% 10.64/3.81  tff(c_5782, plain, (![B_490, C_491, A_492]: (k1_xboole_0=B_490 | v1_funct_2(C_491, A_492, B_490) | k1_relset_1(A_492, B_490, C_491)!=A_492 | ~m1_subset_1(C_491, k1_zfmisc_1(k2_zfmisc_1(A_492, B_490))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.64/3.81  tff(c_5791, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_5126, c_5782])).
% 10.64/3.81  tff(c_5814, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5290, c_5791])).
% 10.64/3.81  tff(c_5815, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_5125, c_5814])).
% 10.64/3.81  tff(c_5822, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_5815])).
% 10.64/3.81  tff(c_5825, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34, c_5822])).
% 10.64/3.81  tff(c_5828, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_205, c_70, c_64, c_5326, c_5825])).
% 10.64/3.81  tff(c_5829, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_5815])).
% 10.64/3.81  tff(c_5858, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_5829, c_8])).
% 10.64/3.81  tff(c_5857, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5829, c_5829, c_12])).
% 10.64/3.81  tff(c_5146, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_5126, c_18])).
% 10.64/3.81  tff(c_5162, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3') | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_5146, c_2])).
% 10.64/3.81  tff(c_5208, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_5162])).
% 10.64/3.81  tff(c_6086, plain, (~r1_tarski('#skF_1', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5857, c_5208])).
% 10.64/3.81  tff(c_6091, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5858, c_6086])).
% 10.64/3.81  tff(c_6092, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_5162])).
% 10.64/3.81  tff(c_6095, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_6092, c_5126])).
% 10.64/3.81  tff(c_6201, plain, (![A_513, B_514, C_515]: (k1_relset_1(A_513, B_514, C_515)=k1_relat_1(C_515) | ~m1_subset_1(C_515, k1_zfmisc_1(k2_zfmisc_1(A_513, B_514))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.64/3.81  tff(c_6300, plain, (![C_525]: (k1_relset_1('#skF_2', '#skF_1', C_525)=k1_relat_1(C_525) | ~m1_subset_1(C_525, k1_zfmisc_1(k2_funct_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_6092, c_6201])).
% 10.64/3.81  tff(c_6312, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_6095, c_6300])).
% 10.64/3.81  tff(c_6783, plain, (![B_567, C_568, A_569]: (k1_xboole_0=B_567 | v1_funct_2(C_568, A_569, B_567) | k1_relset_1(A_569, B_567, C_568)!=A_569 | ~m1_subset_1(C_568, k1_zfmisc_1(k2_zfmisc_1(A_569, B_567))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.64/3.81  tff(c_6792, plain, (![C_568]: (k1_xboole_0='#skF_1' | v1_funct_2(C_568, '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', C_568)!='#skF_2' | ~m1_subset_1(C_568, k1_zfmisc_1(k2_funct_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_6092, c_6783])).
% 10.64/3.81  tff(c_6857, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_6792])).
% 10.64/3.81  tff(c_6102, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2' | k2_funct_1('#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6092, c_10])).
% 10.64/3.81  tff(c_6145, plain, (k2_funct_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_6102])).
% 10.64/3.81  tff(c_6876, plain, (k2_funct_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6857, c_6145])).
% 10.64/3.81  tff(c_6886, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6857, c_6857, c_12])).
% 10.64/3.81  tff(c_7025, plain, (k2_funct_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6886, c_6092])).
% 10.64/3.81  tff(c_7027, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6876, c_7025])).
% 10.64/3.81  tff(c_7030, plain, (![C_578]: (v1_funct_2(C_578, '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', C_578)!='#skF_2' | ~m1_subset_1(C_578, k1_zfmisc_1(k2_funct_1('#skF_3'))))), inference(splitRight, [status(thm)], [c_6792])).
% 10.64/3.81  tff(c_7033, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_6095, c_7030])).
% 10.64/3.81  tff(c_7043, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6312, c_7033])).
% 10.64/3.81  tff(c_7044, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_5125, c_7043])).
% 10.64/3.81  tff(c_7050, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34, c_7044])).
% 10.64/3.81  tff(c_7053, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_205, c_70, c_64, c_6453, c_7050])).
% 10.64/3.81  tff(c_7054, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_6102])).
% 10.64/3.81  tff(c_7090, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_7054])).
% 10.64/3.81  tff(c_7104, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_7090, c_8])).
% 10.64/3.81  tff(c_7101, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7090, c_7090, c_14])).
% 10.64/3.81  tff(c_5207, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_139])).
% 10.64/3.81  tff(c_7209, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7101, c_5207])).
% 10.64/3.81  tff(c_7214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7104, c_7209])).
% 10.64/3.81  tff(c_7215, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_7054])).
% 10.64/3.81  tff(c_7230, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_7215, c_8])).
% 10.64/3.81  tff(c_7229, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7215, c_7215, c_12])).
% 10.64/3.81  tff(c_7364, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7229, c_5207])).
% 10.64/3.81  tff(c_7369, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7230, c_7364])).
% 10.64/3.81  tff(c_7370, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_139])).
% 10.64/3.81  tff(c_7373, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7370, c_66])).
% 10.64/3.81  tff(c_7480, plain, (![A_603, B_604, C_605]: (k2_relset_1(A_603, B_604, C_605)=k2_relat_1(C_605) | ~m1_subset_1(C_605, k1_zfmisc_1(k2_zfmisc_1(A_603, B_604))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.64/3.81  tff(c_7554, plain, (![C_616]: (k2_relset_1('#skF_1', '#skF_2', C_616)=k2_relat_1(C_616) | ~m1_subset_1(C_616, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_7370, c_7480])).
% 10.64/3.81  tff(c_7557, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_7373, c_7554])).
% 10.64/3.81  tff(c_7567, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_7557])).
% 10.64/3.81  tff(c_7757, plain, (![A_628, B_629, C_630]: (k1_relset_1(A_628, B_629, C_630)=k1_relat_1(C_630) | ~m1_subset_1(C_630, k1_zfmisc_1(k2_zfmisc_1(A_628, B_629))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.64/3.81  tff(c_7786, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_5126, c_7757])).
% 10.64/3.81  tff(c_7947, plain, (![B_651, C_652, A_653]: (k1_xboole_0=B_651 | v1_funct_2(C_652, A_653, B_651) | k1_relset_1(A_653, B_651, C_652)!=A_653 | ~m1_subset_1(C_652, k1_zfmisc_1(k2_zfmisc_1(A_653, B_651))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.64/3.81  tff(c_7959, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_5126, c_7947])).
% 10.64/3.81  tff(c_7979, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_7786, c_7959])).
% 10.64/3.81  tff(c_7980, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_5125, c_7979])).
% 10.64/3.81  tff(c_7985, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_7980])).
% 10.64/3.81  tff(c_7988, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34, c_7985])).
% 10.64/3.81  tff(c_7991, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_205, c_70, c_64, c_7567, c_7988])).
% 10.64/3.81  tff(c_7992, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_7980])).
% 10.64/3.81  tff(c_7380, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_7370, c_10])).
% 10.64/3.81  tff(c_7441, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_7380])).
% 10.64/3.81  tff(c_8010, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_7992, c_7441])).
% 10.64/3.81  tff(c_8018, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7992, c_7992, c_14])).
% 10.64/3.81  tff(c_8157, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8018, c_7370])).
% 10.64/3.81  tff(c_8159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8010, c_8157])).
% 10.64/3.81  tff(c_8161, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_7380])).
% 10.64/3.81  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.64/3.81  tff(c_8174, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8161, c_8161, c_26])).
% 10.64/3.81  tff(c_8170, plain, (![A_6]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_8161, c_16])).
% 10.64/3.81  tff(c_8736, plain, (![A_694, B_695, C_696]: (k1_relset_1(A_694, B_695, C_696)=k1_relat_1(C_696) | ~m1_subset_1(C_696, k1_zfmisc_1(k2_zfmisc_1(A_694, B_695))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.64/3.81  tff(c_8740, plain, (![A_694, B_695]: (k1_relset_1(A_694, B_695, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_8170, c_8736])).
% 10.64/3.81  tff(c_8752, plain, (![A_694, B_695]: (k1_relset_1(A_694, B_695, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8174, c_8740])).
% 10.64/3.81  tff(c_48, plain, (![B_24, C_25, A_23]: (k1_xboole_0=B_24 | v1_funct_2(C_25, A_23, B_24) | k1_relset_1(A_23, B_24, C_25)!=A_23 | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.64/3.81  tff(c_8928, plain, (![B_723, C_724, A_725]: (B_723='#skF_3' | v1_funct_2(C_724, A_725, B_723) | k1_relset_1(A_725, B_723, C_724)!=A_725 | ~m1_subset_1(C_724, k1_zfmisc_1(k2_zfmisc_1(A_725, B_723))))), inference(demodulation, [status(thm), theory('equality')], [c_8161, c_48])).
% 10.64/3.81  tff(c_8935, plain, (![B_723, A_725]: (B_723='#skF_3' | v1_funct_2('#skF_3', A_725, B_723) | k1_relset_1(A_725, B_723, '#skF_3')!=A_725)), inference(resolution, [status(thm)], [c_8170, c_8928])).
% 10.64/3.81  tff(c_8952, plain, (![B_726, A_727]: (B_726='#skF_3' | v1_funct_2('#skF_3', A_727, B_726) | A_727!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8752, c_8935])).
% 10.64/3.81  tff(c_8172, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_8161, c_8])).
% 10.64/3.81  tff(c_8169, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8161, c_8161, c_14])).
% 10.64/3.81  tff(c_8160, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_7380])).
% 10.64/3.81  tff(c_8578, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8161, c_8161, c_8160])).
% 10.64/3.81  tff(c_8579, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_8578])).
% 10.64/3.81  tff(c_8582, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_8579, c_5146])).
% 10.64/3.81  tff(c_8589, plain, (r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8169, c_8582])).
% 10.64/3.81  tff(c_8621, plain, (k2_funct_1('#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_8589, c_2])).
% 10.64/3.81  tff(c_8626, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8172, c_8621])).
% 10.64/3.81  tff(c_8584, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8579, c_5125])).
% 10.64/3.81  tff(c_8682, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8626, c_8584])).
% 10.64/3.81  tff(c_8963, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_8952, c_8682])).
% 10.64/3.81  tff(c_8586, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8579, c_68])).
% 10.64/3.81  tff(c_8983, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8963, c_8963, c_8586])).
% 10.64/3.81  tff(c_8980, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8963, c_8963, c_8682])).
% 10.64/3.81  tff(c_9116, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8983, c_8980])).
% 10.64/3.81  tff(c_9117, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_8578])).
% 10.64/3.81  tff(c_9118, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_8578])).
% 10.64/3.81  tff(c_9158, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9117, c_9118])).
% 10.64/3.81  tff(c_42, plain, (![A_23]: (v1_funct_2(k1_xboole_0, A_23, k1_xboole_0) | k1_xboole_0=A_23 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_23, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.64/3.81  tff(c_72, plain, (![A_23]: (v1_funct_2(k1_xboole_0, A_23, k1_xboole_0) | k1_xboole_0=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_42])).
% 10.64/3.81  tff(c_8168, plain, (![A_23]: (v1_funct_2('#skF_3', A_23, '#skF_3') | A_23='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8161, c_8161, c_8161, c_72])).
% 10.64/3.81  tff(c_9410, plain, (![A_752]: (v1_funct_2('#skF_1', A_752, '#skF_1') | A_752='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9117, c_9117, c_9117, c_8168])).
% 10.64/3.81  tff(c_8171, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8161, c_8161, c_12])).
% 10.64/3.81  tff(c_9135, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9117, c_9117, c_8171])).
% 10.64/3.81  tff(c_8252, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8161, c_8161, c_8160])).
% 10.64/3.81  tff(c_8253, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_8252])).
% 10.64/3.81  tff(c_8251, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_5162])).
% 10.64/3.81  tff(c_8359, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8172, c_8169, c_8253, c_8251])).
% 10.64/3.81  tff(c_8360, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_8252])).
% 10.64/3.81  tff(c_8361, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_8252])).
% 10.64/3.81  tff(c_8400, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8360, c_8361])).
% 10.64/3.81  tff(c_8173, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8161, c_8161, c_24])).
% 10.64/3.81  tff(c_8377, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8360, c_8360, c_8173])).
% 10.64/3.81  tff(c_8445, plain, (![A_6]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_8360, c_8170])).
% 10.64/3.81  tff(c_8553, plain, (![A_675, B_676, C_677]: (k2_relset_1(A_675, B_676, C_677)=k2_relat_1(C_677) | ~m1_subset_1(C_677, k1_zfmisc_1(k2_zfmisc_1(A_675, B_676))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.64/3.81  tff(c_8563, plain, (![A_675, B_676]: (k2_relset_1(A_675, B_676, '#skF_1')=k2_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_8445, c_8553])).
% 10.64/3.81  tff(c_8569, plain, (![A_675, B_676]: (k2_relset_1(A_675, B_676, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8377, c_8563])).
% 10.64/3.81  tff(c_8392, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8360, c_62])).
% 10.64/3.81  tff(c_8573, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8569, c_8392])).
% 10.64/3.81  tff(c_8575, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8400, c_8573])).
% 10.64/3.81  tff(c_8576, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_5162])).
% 10.64/3.81  tff(c_9134, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9117, c_8576])).
% 10.64/3.81  tff(c_9274, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9135, c_9134])).
% 10.64/3.81  tff(c_9147, plain, (~v1_funct_2(k2_funct_1('#skF_1'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9117, c_5125])).
% 10.64/3.81  tff(c_9358, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9274, c_9147])).
% 10.64/3.81  tff(c_9413, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_9410, c_9358])).
% 10.64/3.81  tff(c_9417, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9158, c_9413])).
% 10.64/3.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.64/3.81  
% 10.64/3.81  Inference rules
% 10.64/3.81  ----------------------
% 10.64/3.81  #Ref     : 0
% 10.64/3.81  #Sup     : 1962
% 10.64/3.81  #Fact    : 0
% 10.64/3.81  #Define  : 0
% 10.64/3.81  #Split   : 38
% 10.64/3.81  #Chain   : 0
% 10.64/3.81  #Close   : 0
% 10.64/3.81  
% 10.64/3.81  Ordering : KBO
% 10.64/3.81  
% 10.64/3.81  Simplification rules
% 10.64/3.81  ----------------------
% 10.64/3.81  #Subsume      : 343
% 10.64/3.81  #Demod        : 2856
% 10.64/3.81  #Tautology    : 1080
% 10.64/3.81  #SimpNegUnit  : 31
% 10.64/3.81  #BackRed      : 492
% 10.64/3.81  
% 10.64/3.81  #Partial instantiations: 0
% 10.64/3.81  #Strategies tried      : 1
% 10.64/3.81  
% 10.64/3.81  Timing (in seconds)
% 10.64/3.81  ----------------------
% 10.64/3.82  Preprocessing        : 0.49
% 10.64/3.82  Parsing              : 0.25
% 10.64/3.82  CNF conversion       : 0.03
% 10.64/3.82  Main loop            : 2.41
% 10.64/3.82  Inferencing          : 0.85
% 10.64/3.82  Reduction            : 0.86
% 10.64/3.82  Demodulation         : 0.62
% 10.64/3.82  BG Simplification    : 0.09
% 10.64/3.82  Subsumption          : 0.39
% 10.64/3.82  Abstraction          : 0.10
% 10.64/3.82  MUC search           : 0.00
% 10.64/3.82  Cooper               : 0.00
% 10.64/3.82  Total                : 3.06
% 10.64/3.82  Index Insertion      : 0.00
% 10.64/3.82  Index Deletion       : 0.00
% 10.64/3.82  Index Matching       : 0.00
% 10.64/3.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
