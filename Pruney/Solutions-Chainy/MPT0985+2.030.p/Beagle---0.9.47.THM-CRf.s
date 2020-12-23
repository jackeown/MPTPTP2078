%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:30 EST 2020

% Result     : Theorem 4.22s
% Output     : CNFRefutation 4.59s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 915 expanded)
%              Number of leaves         :   36 ( 306 expanded)
%              Depth                    :   12
%              Number of atoms          :  312 (2462 expanded)
%              Number of equality atoms :  116 ( 633 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_45,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_143,negated_conjecture,(
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

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_114,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_104,axiom,(
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

tff(f_48,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_126,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_30,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_12,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_114,plain,(
    ! [B_37,A_38] :
      ( v1_relat_1(B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38))
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_117,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_114])).

tff(c_123,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_117])).

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_64,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_62,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1108,plain,(
    ! [A_129,B_130,C_131] :
      ( k2_relset_1(A_129,B_130,C_131) = k2_relat_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1114,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1108])).

tff(c_1121,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1114])).

tff(c_30,plain,(
    ! [A_14] :
      ( k1_relat_1(k2_funct_1(A_14)) = k2_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_24,plain,(
    ! [A_13] :
      ( v1_funct_1(k2_funct_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_60,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_125,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_136,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_125])).

tff(c_140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_70,c_136])).

tff(c_141,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_184,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_141])).

tff(c_237,plain,(
    ! [A_54,B_55,C_56] :
      ( k2_relset_1(A_54,B_55,C_56) = k2_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_240,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_237])).

tff(c_246,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_240])).

tff(c_26,plain,(
    ! [A_13] :
      ( v1_relat_1(k2_funct_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_142,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_221,plain,(
    ! [A_52] :
      ( k1_relat_1(k2_funct_1(A_52)) = k2_relat_1(A_52)
      | ~ v2_funct_1(A_52)
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_50,plain,(
    ! [A_24] :
      ( v1_funct_2(A_24,k1_relat_1(A_24),k2_relat_1(A_24))
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_877,plain,(
    ! [A_111] :
      ( v1_funct_2(k2_funct_1(A_111),k2_relat_1(A_111),k2_relat_1(k2_funct_1(A_111)))
      | ~ v1_funct_1(k2_funct_1(A_111))
      | ~ v1_relat_1(k2_funct_1(A_111))
      | ~ v2_funct_1(A_111)
      | ~ v1_funct_1(A_111)
      | ~ v1_relat_1(A_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_50])).

tff(c_880,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_877])).

tff(c_891,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_70,c_64,c_142,c_880])).

tff(c_911,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_891])).

tff(c_914,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_911])).

tff(c_918,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_70,c_914])).

tff(c_920,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_891])).

tff(c_18,plain,(
    ! [A_11] :
      ( k2_relat_1(A_11) != k1_xboole_0
      | k1_xboole_0 = A_11
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_149,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_123,c_18])).

tff(c_183,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_149])).

tff(c_249,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_183])).

tff(c_68,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_270,plain,(
    ! [A_60,B_61,C_62] :
      ( k1_relset_1(A_60,B_61,C_62) = k1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_278,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_270])).

tff(c_653,plain,(
    ! [B_93,A_94,C_95] :
      ( k1_xboole_0 = B_93
      | k1_relset_1(A_94,B_93,C_95) = A_94
      | ~ v1_funct_2(C_95,A_94,B_93)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_94,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_665,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_653])).

tff(c_678,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_278,c_665])).

tff(c_679,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_678])).

tff(c_28,plain,(
    ! [A_14] :
      ( k2_relat_1(k2_funct_1(A_14)) = k1_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_292,plain,(
    ! [A_65] :
      ( m1_subset_1(A_65,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_65),k2_relat_1(A_65))))
      | ~ v1_funct_1(A_65)
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_946,plain,(
    ! [A_113] :
      ( m1_subset_1(k2_funct_1(A_113),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_113)),k1_relat_1(A_113))))
      | ~ v1_funct_1(k2_funct_1(A_113))
      | ~ v1_relat_1(k2_funct_1(A_113))
      | ~ v2_funct_1(A_113)
      | ~ v1_funct_1(A_113)
      | ~ v1_relat_1(A_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_292])).

tff(c_966,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_679,c_946])).

tff(c_985,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_70,c_64,c_920,c_142,c_966])).

tff(c_1007,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_985])).

tff(c_1021,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_70,c_64,c_246,c_1007])).

tff(c_1023,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_184,c_1021])).

tff(c_1024,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_1025,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_1199,plain,(
    ! [A_136,B_137,C_138] :
      ( k1_relset_1(A_136,B_137,C_138) = k1_relat_1(C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1218,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1025,c_1199])).

tff(c_1427,plain,(
    ! [B_159,C_160,A_161] :
      ( k1_xboole_0 = B_159
      | v1_funct_2(C_160,A_161,B_159)
      | k1_relset_1(A_161,B_159,C_160) != A_161
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_161,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1439,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_1025,c_1427])).

tff(c_1454,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1218,c_1439])).

tff(c_1455,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_1024,c_1454])).

tff(c_1461,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1455])).

tff(c_1464,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1461])).

tff(c_1467,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_70,c_64,c_1121,c_1464])).

tff(c_1468,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1455])).

tff(c_1124,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1121,c_183])).

tff(c_1478,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1468,c_1124])).

tff(c_1219,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1199])).

tff(c_46,plain,(
    ! [B_22,A_21,C_23] :
      ( k1_xboole_0 = B_22
      | k1_relset_1(A_21,B_22,C_23) = A_21
      | ~ v1_funct_2(C_23,A_21,B_22)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1556,plain,(
    ! [B_162,A_163,C_164] :
      ( B_162 = '#skF_1'
      | k1_relset_1(A_163,B_162,C_164) = A_163
      | ~ v1_funct_2(C_164,A_163,B_162)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_163,B_162))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1468,c_46])).

tff(c_1571,plain,
    ( '#skF_2' = '#skF_1'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_1556])).

tff(c_1581,plain,
    ( '#skF_2' = '#skF_1'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1219,c_1571])).

tff(c_1582,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_1478,c_1581])).

tff(c_20,plain,(
    ! [A_11] :
      ( k1_relat_1(A_11) != k1_xboole_0
      | k1_xboole_0 = A_11
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_150,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_123,c_20])).

tff(c_1040,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_1485,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1468,c_1040])).

tff(c_1705,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1582,c_1485])).

tff(c_1706,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_1708,plain,(
    k2_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1706,c_183])).

tff(c_14,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1715,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1706,c_1706,c_14])).

tff(c_1741,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1708,c_1715])).

tff(c_1742,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_149])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_1752,plain,(
    ! [A_1] : r1_tarski('#skF_3',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1742,c_4])).

tff(c_1743,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_149])).

tff(c_2146,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1742,c_1743])).

tff(c_16,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1751,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1742,c_1742,c_16])).

tff(c_2516,plain,(
    ! [B_265,A_266] :
      ( v1_funct_2(B_265,k1_relat_1(B_265),A_266)
      | ~ r1_tarski(k2_relat_1(B_265),A_266)
      | ~ v1_funct_1(B_265)
      | ~ v1_relat_1(B_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2522,plain,(
    ! [A_266] :
      ( v1_funct_2('#skF_3','#skF_3',A_266)
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_266)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1751,c_2516])).

tff(c_2524,plain,(
    ! [A_266] : v1_funct_2('#skF_3','#skF_3',A_266) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_70,c_1752,c_2146,c_2522])).

tff(c_6,plain,(
    ! [A_2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_1749,plain,(
    ! [A_2] : m1_subset_1('#skF_3',k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1742,c_6])).

tff(c_2373,plain,(
    ! [A_252,B_253,C_254] :
      ( k2_relset_1(A_252,B_253,C_254) = k2_relat_1(C_254)
      | ~ m1_subset_1(C_254,k1_zfmisc_1(k2_zfmisc_1(A_252,B_253))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2377,plain,(
    ! [A_252,B_253] : k2_relset_1(A_252,B_253,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1749,c_2373])).

tff(c_2379,plain,(
    ! [A_252,B_253] : k2_relset_1(A_252,B_253,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2146,c_2377])).

tff(c_2380,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2379,c_62])).

tff(c_2240,plain,(
    ! [A_236] :
      ( k1_relat_1(k2_funct_1(A_236)) = k2_relat_1(A_236)
      | ~ v2_funct_1(A_236)
      | ~ v1_funct_1(A_236)
      | ~ v1_relat_1(A_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_105,plain,(
    ! [A_36] :
      ( k2_relat_1(A_36) != k1_xboole_0
      | k1_xboole_0 = A_36
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_112,plain,(
    ! [A_13] :
      ( k2_relat_1(k2_funct_1(A_13)) != k1_xboole_0
      | k2_funct_1(A_13) = k1_xboole_0
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(resolution,[status(thm)],[c_26,c_105])).

tff(c_1870,plain,(
    ! [A_185] :
      ( k2_relat_1(k2_funct_1(A_185)) != '#skF_3'
      | k2_funct_1(A_185) = '#skF_3'
      | ~ v1_funct_1(A_185)
      | ~ v1_relat_1(A_185) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1742,c_1742,c_112])).

tff(c_2116,plain,(
    ! [A_216] :
      ( k1_relat_1(A_216) != '#skF_3'
      | k2_funct_1(A_216) = '#skF_3'
      | ~ v1_funct_1(A_216)
      | ~ v1_relat_1(A_216)
      | ~ v2_funct_1(A_216)
      | ~ v1_funct_1(A_216)
      | ~ v1_relat_1(A_216) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1870])).

tff(c_2119,plain,
    ( k1_relat_1('#skF_3') != '#skF_3'
    | k2_funct_1('#skF_3') = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_2116])).

tff(c_2122,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_70,c_1751,c_2119])).

tff(c_1766,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1742,c_1743])).

tff(c_1918,plain,(
    ! [A_192,B_193,C_194] :
      ( k2_relset_1(A_192,B_193,C_194) = k2_relat_1(C_194)
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(A_192,B_193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1925,plain,(
    ! [A_192,B_193] : k2_relset_1(A_192,B_193,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1749,c_1918])).

tff(c_1928,plain,(
    ! [A_192,B_193] : k2_relset_1(A_192,B_193,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1766,c_1925])).

tff(c_1940,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1928,c_62])).

tff(c_1765,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_141])).

tff(c_1948,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1940,c_1765])).

tff(c_2139,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2122,c_1948])).

tff(c_2143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1749,c_2139])).

tff(c_2145,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_10,plain,(
    ! [B_8,A_6] :
      ( v1_relat_1(B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_6))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2169,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_2145,c_10])).

tff(c_2172,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2169])).

tff(c_2193,plain,(
    ! [A_224] :
      ( k1_relat_1(A_224) != '#skF_3'
      | A_224 = '#skF_3'
      | ~ v1_relat_1(A_224) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1742,c_1742,c_20])).

tff(c_2206,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) != '#skF_3'
    | k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2172,c_2193])).

tff(c_2214,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2206])).

tff(c_2249,plain,
    ( k2_relat_1('#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2240,c_2214])).

tff(c_2256,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_70,c_64,c_2146,c_2249])).

tff(c_2257,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2206])).

tff(c_2173,plain,(
    ! [A_223] :
      ( k2_relat_1(A_223) != '#skF_3'
      | A_223 = '#skF_3'
      | ~ v1_relat_1(A_223) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1742,c_1742,c_18])).

tff(c_2186,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) != '#skF_3'
    | k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2172,c_2173])).

tff(c_2213,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2186])).

tff(c_2259,plain,(
    k2_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2257,c_2213])).

tff(c_2266,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2146,c_2259])).

tff(c_2267,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2186])).

tff(c_2144,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_2278,plain,(
    ~ v1_funct_2('#skF_3','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2267,c_2144])).

tff(c_2388,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2380,c_2278])).

tff(c_2528,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2524,c_2388])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:45:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.22/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.22/1.75  
% 4.22/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.22/1.76  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.22/1.76  
% 4.22/1.76  %Foreground sorts:
% 4.22/1.76  
% 4.22/1.76  
% 4.22/1.76  %Background operators:
% 4.22/1.76  
% 4.22/1.76  
% 4.22/1.76  %Foreground operators:
% 4.22/1.76  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.22/1.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.22/1.76  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.22/1.76  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.22/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.22/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.22/1.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.22/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.22/1.76  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.22/1.76  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.22/1.76  tff('#skF_2', type, '#skF_2': $i).
% 4.22/1.76  tff('#skF_3', type, '#skF_3': $i).
% 4.22/1.76  tff('#skF_1', type, '#skF_1': $i).
% 4.22/1.76  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.22/1.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.22/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.22/1.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.22/1.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.22/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.22/1.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.22/1.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.22/1.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.22/1.76  
% 4.59/1.78  tff(f_45, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.59/1.78  tff(f_143, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 4.59/1.78  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.59/1.78  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.59/1.78  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 4.59/1.78  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 4.59/1.78  tff(f_114, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 4.59/1.78  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 4.59/1.78  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.59/1.78  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.59/1.78  tff(f_48, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 4.59/1.78  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.59/1.78  tff(f_126, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 4.59/1.78  tff(f_30, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.59/1.78  tff(c_12, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.59/1.78  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.59/1.78  tff(c_114, plain, (![B_37, A_38]: (v1_relat_1(B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.59/1.78  tff(c_117, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_114])).
% 4.59/1.78  tff(c_123, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_117])).
% 4.59/1.78  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.59/1.78  tff(c_64, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.59/1.78  tff(c_62, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.59/1.78  tff(c_1108, plain, (![A_129, B_130, C_131]: (k2_relset_1(A_129, B_130, C_131)=k2_relat_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.59/1.78  tff(c_1114, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_1108])).
% 4.59/1.78  tff(c_1121, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1114])).
% 4.59/1.78  tff(c_30, plain, (![A_14]: (k1_relat_1(k2_funct_1(A_14))=k2_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.59/1.78  tff(c_24, plain, (![A_13]: (v1_funct_1(k2_funct_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.59/1.78  tff(c_60, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.59/1.78  tff(c_125, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_60])).
% 4.59/1.78  tff(c_136, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_125])).
% 4.59/1.78  tff(c_140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_123, c_70, c_136])).
% 4.59/1.78  tff(c_141, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_60])).
% 4.59/1.78  tff(c_184, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_141])).
% 4.59/1.78  tff(c_237, plain, (![A_54, B_55, C_56]: (k2_relset_1(A_54, B_55, C_56)=k2_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.59/1.78  tff(c_240, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_237])).
% 4.59/1.78  tff(c_246, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_240])).
% 4.59/1.78  tff(c_26, plain, (![A_13]: (v1_relat_1(k2_funct_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.59/1.78  tff(c_142, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_60])).
% 4.59/1.78  tff(c_221, plain, (![A_52]: (k1_relat_1(k2_funct_1(A_52))=k2_relat_1(A_52) | ~v2_funct_1(A_52) | ~v1_funct_1(A_52) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.59/1.78  tff(c_50, plain, (![A_24]: (v1_funct_2(A_24, k1_relat_1(A_24), k2_relat_1(A_24)) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.59/1.78  tff(c_877, plain, (![A_111]: (v1_funct_2(k2_funct_1(A_111), k2_relat_1(A_111), k2_relat_1(k2_funct_1(A_111))) | ~v1_funct_1(k2_funct_1(A_111)) | ~v1_relat_1(k2_funct_1(A_111)) | ~v2_funct_1(A_111) | ~v1_funct_1(A_111) | ~v1_relat_1(A_111))), inference(superposition, [status(thm), theory('equality')], [c_221, c_50])).
% 4.59/1.78  tff(c_880, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_246, c_877])).
% 4.59/1.78  tff(c_891, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_70, c_64, c_142, c_880])).
% 4.59/1.78  tff(c_911, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_891])).
% 4.59/1.78  tff(c_914, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_911])).
% 4.59/1.78  tff(c_918, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_123, c_70, c_914])).
% 4.59/1.78  tff(c_920, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_891])).
% 4.59/1.78  tff(c_18, plain, (![A_11]: (k2_relat_1(A_11)!=k1_xboole_0 | k1_xboole_0=A_11 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.59/1.78  tff(c_149, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_123, c_18])).
% 4.59/1.78  tff(c_183, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_149])).
% 4.59/1.78  tff(c_249, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_246, c_183])).
% 4.59/1.78  tff(c_68, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.59/1.78  tff(c_270, plain, (![A_60, B_61, C_62]: (k1_relset_1(A_60, B_61, C_62)=k1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.59/1.78  tff(c_278, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_270])).
% 4.59/1.78  tff(c_653, plain, (![B_93, A_94, C_95]: (k1_xboole_0=B_93 | k1_relset_1(A_94, B_93, C_95)=A_94 | ~v1_funct_2(C_95, A_94, B_93) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_94, B_93))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.59/1.78  tff(c_665, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_653])).
% 4.59/1.78  tff(c_678, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_278, c_665])).
% 4.59/1.78  tff(c_679, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_249, c_678])).
% 4.59/1.78  tff(c_28, plain, (![A_14]: (k2_relat_1(k2_funct_1(A_14))=k1_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.59/1.78  tff(c_292, plain, (![A_65]: (m1_subset_1(A_65, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_65), k2_relat_1(A_65)))) | ~v1_funct_1(A_65) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.59/1.78  tff(c_946, plain, (![A_113]: (m1_subset_1(k2_funct_1(A_113), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_113)), k1_relat_1(A_113)))) | ~v1_funct_1(k2_funct_1(A_113)) | ~v1_relat_1(k2_funct_1(A_113)) | ~v2_funct_1(A_113) | ~v1_funct_1(A_113) | ~v1_relat_1(A_113))), inference(superposition, [status(thm), theory('equality')], [c_28, c_292])).
% 4.59/1.78  tff(c_966, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_679, c_946])).
% 4.59/1.78  tff(c_985, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_70, c_64, c_920, c_142, c_966])).
% 4.59/1.78  tff(c_1007, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_985])).
% 4.59/1.78  tff(c_1021, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_70, c_64, c_246, c_1007])).
% 4.59/1.78  tff(c_1023, plain, $false, inference(negUnitSimplification, [status(thm)], [c_184, c_1021])).
% 4.59/1.78  tff(c_1024, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_141])).
% 4.59/1.78  tff(c_1025, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_141])).
% 4.59/1.78  tff(c_1199, plain, (![A_136, B_137, C_138]: (k1_relset_1(A_136, B_137, C_138)=k1_relat_1(C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.59/1.78  tff(c_1218, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1025, c_1199])).
% 4.59/1.78  tff(c_1427, plain, (![B_159, C_160, A_161]: (k1_xboole_0=B_159 | v1_funct_2(C_160, A_161, B_159) | k1_relset_1(A_161, B_159, C_160)!=A_161 | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_161, B_159))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.59/1.78  tff(c_1439, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_1025, c_1427])).
% 4.59/1.78  tff(c_1454, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1218, c_1439])).
% 4.59/1.78  tff(c_1455, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_1024, c_1454])).
% 4.59/1.78  tff(c_1461, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_1455])).
% 4.59/1.78  tff(c_1464, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_1461])).
% 4.59/1.78  tff(c_1467, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_123, c_70, c_64, c_1121, c_1464])).
% 4.59/1.78  tff(c_1468, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_1455])).
% 4.59/1.78  tff(c_1124, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1121, c_183])).
% 4.59/1.78  tff(c_1478, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1468, c_1124])).
% 4.59/1.78  tff(c_1219, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_1199])).
% 4.59/1.78  tff(c_46, plain, (![B_22, A_21, C_23]: (k1_xboole_0=B_22 | k1_relset_1(A_21, B_22, C_23)=A_21 | ~v1_funct_2(C_23, A_21, B_22) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.59/1.78  tff(c_1556, plain, (![B_162, A_163, C_164]: (B_162='#skF_1' | k1_relset_1(A_163, B_162, C_164)=A_163 | ~v1_funct_2(C_164, A_163, B_162) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_163, B_162))))), inference(demodulation, [status(thm), theory('equality')], [c_1468, c_46])).
% 4.59/1.78  tff(c_1571, plain, ('#skF_2'='#skF_1' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_1556])).
% 4.59/1.78  tff(c_1581, plain, ('#skF_2'='#skF_1' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1219, c_1571])).
% 4.59/1.78  tff(c_1582, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_1478, c_1581])).
% 4.59/1.78  tff(c_20, plain, (![A_11]: (k1_relat_1(A_11)!=k1_xboole_0 | k1_xboole_0=A_11 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.59/1.78  tff(c_150, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_123, c_20])).
% 4.59/1.78  tff(c_1040, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_150])).
% 4.59/1.78  tff(c_1485, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1468, c_1040])).
% 4.59/1.78  tff(c_1705, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1582, c_1485])).
% 4.59/1.78  tff(c_1706, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_150])).
% 4.59/1.78  tff(c_1708, plain, (k2_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1706, c_183])).
% 4.59/1.78  tff(c_14, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.59/1.78  tff(c_1715, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1706, c_1706, c_14])).
% 4.59/1.78  tff(c_1741, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1708, c_1715])).
% 4.59/1.78  tff(c_1742, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_149])).
% 4.59/1.78  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 4.59/1.78  tff(c_1752, plain, (![A_1]: (r1_tarski('#skF_3', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1742, c_4])).
% 4.59/1.78  tff(c_1743, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_149])).
% 4.59/1.78  tff(c_2146, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1742, c_1743])).
% 4.59/1.78  tff(c_16, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.59/1.78  tff(c_1751, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1742, c_1742, c_16])).
% 4.59/1.78  tff(c_2516, plain, (![B_265, A_266]: (v1_funct_2(B_265, k1_relat_1(B_265), A_266) | ~r1_tarski(k2_relat_1(B_265), A_266) | ~v1_funct_1(B_265) | ~v1_relat_1(B_265))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.59/1.78  tff(c_2522, plain, (![A_266]: (v1_funct_2('#skF_3', '#skF_3', A_266) | ~r1_tarski(k2_relat_1('#skF_3'), A_266) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1751, c_2516])).
% 4.59/1.78  tff(c_2524, plain, (![A_266]: (v1_funct_2('#skF_3', '#skF_3', A_266))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_70, c_1752, c_2146, c_2522])).
% 4.59/1.78  tff(c_6, plain, (![A_2]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.59/1.78  tff(c_1749, plain, (![A_2]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_1742, c_6])).
% 4.59/1.78  tff(c_2373, plain, (![A_252, B_253, C_254]: (k2_relset_1(A_252, B_253, C_254)=k2_relat_1(C_254) | ~m1_subset_1(C_254, k1_zfmisc_1(k2_zfmisc_1(A_252, B_253))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.59/1.78  tff(c_2377, plain, (![A_252, B_253]: (k2_relset_1(A_252, B_253, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1749, c_2373])).
% 4.59/1.78  tff(c_2379, plain, (![A_252, B_253]: (k2_relset_1(A_252, B_253, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2146, c_2377])).
% 4.59/1.78  tff(c_2380, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2379, c_62])).
% 4.59/1.78  tff(c_2240, plain, (![A_236]: (k1_relat_1(k2_funct_1(A_236))=k2_relat_1(A_236) | ~v2_funct_1(A_236) | ~v1_funct_1(A_236) | ~v1_relat_1(A_236))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.59/1.78  tff(c_105, plain, (![A_36]: (k2_relat_1(A_36)!=k1_xboole_0 | k1_xboole_0=A_36 | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.59/1.78  tff(c_112, plain, (![A_13]: (k2_relat_1(k2_funct_1(A_13))!=k1_xboole_0 | k2_funct_1(A_13)=k1_xboole_0 | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(resolution, [status(thm)], [c_26, c_105])).
% 4.59/1.78  tff(c_1870, plain, (![A_185]: (k2_relat_1(k2_funct_1(A_185))!='#skF_3' | k2_funct_1(A_185)='#skF_3' | ~v1_funct_1(A_185) | ~v1_relat_1(A_185))), inference(demodulation, [status(thm), theory('equality')], [c_1742, c_1742, c_112])).
% 4.59/1.78  tff(c_2116, plain, (![A_216]: (k1_relat_1(A_216)!='#skF_3' | k2_funct_1(A_216)='#skF_3' | ~v1_funct_1(A_216) | ~v1_relat_1(A_216) | ~v2_funct_1(A_216) | ~v1_funct_1(A_216) | ~v1_relat_1(A_216))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1870])).
% 4.59/1.78  tff(c_2119, plain, (k1_relat_1('#skF_3')!='#skF_3' | k2_funct_1('#skF_3')='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_2116])).
% 4.59/1.78  tff(c_2122, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_123, c_70, c_1751, c_2119])).
% 4.59/1.78  tff(c_1766, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1742, c_1743])).
% 4.59/1.78  tff(c_1918, plain, (![A_192, B_193, C_194]: (k2_relset_1(A_192, B_193, C_194)=k2_relat_1(C_194) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(A_192, B_193))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.59/1.78  tff(c_1925, plain, (![A_192, B_193]: (k2_relset_1(A_192, B_193, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1749, c_1918])).
% 4.59/1.78  tff(c_1928, plain, (![A_192, B_193]: (k2_relset_1(A_192, B_193, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1766, c_1925])).
% 4.59/1.78  tff(c_1940, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1928, c_62])).
% 4.59/1.78  tff(c_1765, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_141])).
% 4.59/1.78  tff(c_1948, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1940, c_1765])).
% 4.59/1.78  tff(c_2139, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2122, c_1948])).
% 4.59/1.78  tff(c_2143, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1749, c_2139])).
% 4.59/1.78  tff(c_2145, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_141])).
% 4.59/1.78  tff(c_10, plain, (![B_8, A_6]: (v1_relat_1(B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_6)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.59/1.78  tff(c_2169, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_2145, c_10])).
% 4.59/1.78  tff(c_2172, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2169])).
% 4.59/1.78  tff(c_2193, plain, (![A_224]: (k1_relat_1(A_224)!='#skF_3' | A_224='#skF_3' | ~v1_relat_1(A_224))), inference(demodulation, [status(thm), theory('equality')], [c_1742, c_1742, c_20])).
% 4.59/1.78  tff(c_2206, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_3' | k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_2172, c_2193])).
% 4.59/1.78  tff(c_2214, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_2206])).
% 4.59/1.78  tff(c_2249, plain, (k2_relat_1('#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2240, c_2214])).
% 4.59/1.78  tff(c_2256, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_123, c_70, c_64, c_2146, c_2249])).
% 4.59/1.78  tff(c_2257, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_2206])).
% 4.59/1.78  tff(c_2173, plain, (![A_223]: (k2_relat_1(A_223)!='#skF_3' | A_223='#skF_3' | ~v1_relat_1(A_223))), inference(demodulation, [status(thm), theory('equality')], [c_1742, c_1742, c_18])).
% 4.59/1.78  tff(c_2186, plain, (k2_relat_1(k2_funct_1('#skF_3'))!='#skF_3' | k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_2172, c_2173])).
% 4.59/1.78  tff(c_2213, plain, (k2_relat_1(k2_funct_1('#skF_3'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_2186])).
% 4.59/1.78  tff(c_2259, plain, (k2_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2257, c_2213])).
% 4.59/1.78  tff(c_2266, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2146, c_2259])).
% 4.59/1.78  tff(c_2267, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_2186])).
% 4.59/1.78  tff(c_2144, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_141])).
% 4.59/1.78  tff(c_2278, plain, (~v1_funct_2('#skF_3', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2267, c_2144])).
% 4.59/1.78  tff(c_2388, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2380, c_2278])).
% 4.59/1.78  tff(c_2528, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2524, c_2388])).
% 4.59/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.59/1.78  
% 4.59/1.78  Inference rules
% 4.59/1.78  ----------------------
% 4.59/1.78  #Ref     : 0
% 4.59/1.78  #Sup     : 502
% 4.59/1.78  #Fact    : 0
% 4.59/1.78  #Define  : 0
% 4.59/1.78  #Split   : 16
% 4.59/1.78  #Chain   : 0
% 4.59/1.78  #Close   : 0
% 4.59/1.78  
% 4.59/1.78  Ordering : KBO
% 4.59/1.78  
% 4.59/1.78  Simplification rules
% 4.59/1.78  ----------------------
% 4.59/1.78  #Subsume      : 57
% 4.59/1.78  #Demod        : 834
% 4.59/1.78  #Tautology    : 267
% 4.59/1.78  #SimpNegUnit  : 20
% 4.59/1.78  #BackRed      : 85
% 4.59/1.78  
% 4.59/1.78  #Partial instantiations: 0
% 4.59/1.78  #Strategies tried      : 1
% 4.59/1.78  
% 4.59/1.78  Timing (in seconds)
% 4.59/1.78  ----------------------
% 4.59/1.79  Preprocessing        : 0.34
% 4.59/1.79  Parsing              : 0.18
% 4.59/1.79  CNF conversion       : 0.02
% 4.59/1.79  Main loop            : 0.66
% 4.59/1.79  Inferencing          : 0.23
% 4.59/1.79  Reduction            : 0.24
% 4.59/1.79  Demodulation         : 0.18
% 4.59/1.79  BG Simplification    : 0.03
% 4.59/1.79  Subsumption          : 0.10
% 4.59/1.79  Abstraction          : 0.03
% 4.59/1.79  MUC search           : 0.00
% 4.59/1.79  Cooper               : 0.00
% 4.59/1.79  Total                : 1.05
% 4.59/1.79  Index Insertion      : 0.00
% 4.59/1.79  Index Deletion       : 0.00
% 4.59/1.79  Index Matching       : 0.00
% 4.59/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
