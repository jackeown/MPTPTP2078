%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:42 EST 2020

% Result     : Theorem 9.82s
% Output     : CNFRefutation 10.34s
% Verified   : 
% Statistics : Number of formulae       :  361 (3505 expanded)
%              Number of leaves         :   39 (1093 expanded)
%              Depth                    :   15
%              Number of atoms          :  643 (9306 expanded)
%              Number of equality atoms :  206 (2884 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

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

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_142,negated_conjecture,(
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

tff(f_89,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_97,axiom,(
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

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_115,axiom,(
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

tff(f_125,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_46,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

tff(c_10,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_70,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_16345,plain,(
    ! [C_1022,A_1023,B_1024] :
      ( v1_xboole_0(C_1022)
      | ~ m1_subset_1(C_1022,k1_zfmisc_1(k2_zfmisc_1(A_1023,B_1024)))
      | ~ v1_xboole_0(A_1023) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_16368,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_16345])).

tff(c_16373,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_16368])).

tff(c_257,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_274,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_257])).

tff(c_74,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_68,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_66,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_16641,plain,(
    ! [A_1046,B_1047,C_1048] :
      ( k2_relset_1(A_1046,B_1047,C_1048) = k2_relat_1(C_1048)
      | ~ m1_subset_1(C_1048,k1_zfmisc_1(k2_zfmisc_1(A_1046,B_1047))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_16657,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_16641])).

tff(c_16671,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_16657])).

tff(c_36,plain,(
    ! [A_15] :
      ( k1_relat_1(k2_funct_1(A_15)) = k2_relat_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_5206,plain,(
    ! [C_336,A_337,B_338] :
      ( v1_xboole_0(C_336)
      | ~ m1_subset_1(C_336,k1_zfmisc_1(k2_zfmisc_1(A_337,B_338)))
      | ~ v1_xboole_0(A_337) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_5225,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_5206])).

tff(c_5230,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_5225])).

tff(c_177,plain,(
    ! [A_45] :
      ( v1_funct_1(k2_funct_1(A_45))
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_64,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_176,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_180,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_177,c_176])).

tff(c_183,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_180])).

tff(c_227,plain,(
    ! [C_54,A_55,B_56] :
      ( v1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_234,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_227])).

tff(c_247,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_234])).

tff(c_248,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_312,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_248])).

tff(c_72,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_854,plain,(
    ! [A_116,B_117,C_118] :
      ( k1_relset_1(A_116,B_117,C_118) = k1_relat_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_887,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_854])).

tff(c_4833,plain,(
    ! [B_326,A_327,C_328] :
      ( k1_xboole_0 = B_326
      | k1_relset_1(A_327,B_326,C_328) = A_327
      | ~ v1_funct_2(C_328,A_327,B_326)
      | ~ m1_subset_1(C_328,k1_zfmisc_1(k2_zfmisc_1(A_327,B_326))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_4852,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_4833])).

tff(c_4867,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_887,c_4852])).

tff(c_4871,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4867])).

tff(c_1794,plain,(
    ! [B_178,A_179,C_180] :
      ( k1_xboole_0 = B_178
      | k1_relset_1(A_179,B_178,C_180) = A_179
      | ~ v1_funct_2(C_180,A_179,B_178)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_179,B_178))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1813,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_1794])).

tff(c_1831,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_887,c_1813])).

tff(c_1835,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1831])).

tff(c_34,plain,(
    ! [A_15] :
      ( k2_relat_1(k2_funct_1(A_15)) = k1_relat_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_32,plain,(
    ! [A_14] :
      ( v1_relat_1(k2_funct_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_249,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_582,plain,(
    ! [A_98] :
      ( k2_relat_1(k2_funct_1(A_98)) = k1_relat_1(A_98)
      | ~ v2_funct_1(A_98)
      | ~ v1_funct_1(A_98)
      | ~ v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_60,plain,(
    ! [A_32] :
      ( v1_funct_2(A_32,k1_relat_1(A_32),k2_relat_1(A_32))
      | ~ v1_funct_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_3137,plain,(
    ! [A_263] :
      ( v1_funct_2(k2_funct_1(A_263),k1_relat_1(k2_funct_1(A_263)),k1_relat_1(A_263))
      | ~ v1_funct_1(k2_funct_1(A_263))
      | ~ v1_relat_1(k2_funct_1(A_263))
      | ~ v2_funct_1(A_263)
      | ~ v1_funct_1(A_263)
      | ~ v1_relat_1(A_263) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_582,c_60])).

tff(c_3140,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1835,c_3137])).

tff(c_3163,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_74,c_68,c_249,c_3140])).

tff(c_3172,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3163])).

tff(c_3175,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_3172])).

tff(c_3179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_74,c_3175])).

tff(c_3181,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3163])).

tff(c_680,plain,(
    ! [A_107,B_108,C_109] :
      ( k2_relset_1(A_107,B_108,C_109) = k2_relat_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_693,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_680])).

tff(c_706,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_693])).

tff(c_734,plain,(
    ! [A_114] :
      ( m1_subset_1(A_114,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_114),k2_relat_1(A_114))))
      | ~ v1_funct_1(A_114)
      | ~ v1_relat_1(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_3771,plain,(
    ! [A_286] :
      ( m1_subset_1(k2_funct_1(A_286),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_286),k2_relat_1(k2_funct_1(A_286)))))
      | ~ v1_funct_1(k2_funct_1(A_286))
      | ~ v1_relat_1(k2_funct_1(A_286))
      | ~ v2_funct_1(A_286)
      | ~ v1_funct_1(A_286)
      | ~ v1_relat_1(A_286) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_734])).

tff(c_3806,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3')))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_706,c_3771])).

tff(c_3828,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_74,c_68,c_3181,c_249,c_3806])).

tff(c_3854,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3'))))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_3828])).

tff(c_3870,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_74,c_68,c_1835,c_3854])).

tff(c_3872,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_312,c_3870])).

tff(c_3873,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1831])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3921,plain,(
    ! [A_4] : r1_tarski('#skF_2',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3873,c_12])).

tff(c_16,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3919,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3873,c_3873,c_16])).

tff(c_751,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_706,c_734])).

tff(c_777,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_74,c_751])).

tff(c_22,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_806,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_777,c_22])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( B_3 = A_2
      | ~ r1_tarski(B_3,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_824,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_806,c_6])).

tff(c_1018,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_824])).

tff(c_4010,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3919,c_1018])).

tff(c_4020,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3921,c_4010])).

tff(c_4021,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_824])).

tff(c_4876,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4871,c_4021])).

tff(c_166,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(A_43,B_44)
      | ~ m1_subset_1(A_43,k1_zfmisc_1(B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_173,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_70,c_166])).

tff(c_345,plain,(
    ! [B_73,A_74] :
      ( B_73 = A_74
      | ~ r1_tarski(B_73,A_74)
      | ~ r1_tarski(A_74,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_352,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_173,c_345])).

tff(c_371,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_352])).

tff(c_4930,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4876,c_371])).

tff(c_4935,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_4930])).

tff(c_4936,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4867])).

tff(c_4982,plain,(
    ! [A_4] : r1_tarski('#skF_2',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4936,c_12])).

tff(c_4980,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4936,c_4936,c_16])).

tff(c_5198,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4980,c_371])).

tff(c_5203,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4982,c_5198])).

tff(c_5204,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_352])).

tff(c_5232,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5204,c_70])).

tff(c_5762,plain,(
    ! [A_388,B_389,C_390] :
      ( k2_relset_1(A_388,B_389,C_390) = k2_relat_1(C_390)
      | ~ m1_subset_1(C_390,k1_zfmisc_1(k2_zfmisc_1(A_388,B_389))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_5820,plain,(
    ! [C_397] :
      ( k2_relset_1('#skF_1','#skF_2',C_397) = k2_relat_1(C_397)
      | ~ m1_subset_1(C_397,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5204,c_5762])).

tff(c_5823,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5232,c_5820])).

tff(c_5833,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_5823])).

tff(c_5479,plain,(
    ! [A_361] :
      ( k1_relat_1(k2_funct_1(A_361)) = k2_relat_1(A_361)
      | ~ v2_funct_1(A_361)
      | ~ v1_funct_1(A_361)
      | ~ v1_relat_1(A_361) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_9474,plain,(
    ! [A_570] :
      ( v1_funct_2(k2_funct_1(A_570),k2_relat_1(A_570),k2_relat_1(k2_funct_1(A_570)))
      | ~ v1_funct_1(k2_funct_1(A_570))
      | ~ v1_relat_1(k2_funct_1(A_570))
      | ~ v2_funct_1(A_570)
      | ~ v1_funct_1(A_570)
      | ~ v1_relat_1(A_570) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5479,c_60])).

tff(c_9483,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5833,c_9474])).

tff(c_9495,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_74,c_68,c_249,c_9483])).

tff(c_9496,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_9495])).

tff(c_9499,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_9496])).

tff(c_9503,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_74,c_9499])).

tff(c_9505,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_9495])).

tff(c_5586,plain,(
    ! [A_371,B_372,C_373] :
      ( k1_relset_1(A_371,B_372,C_373) = k1_relat_1(C_373)
      | ~ m1_subset_1(C_373,k1_zfmisc_1(k2_zfmisc_1(A_371,B_372))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_5697,plain,(
    ! [C_380] :
      ( k1_relset_1('#skF_1','#skF_2',C_380) = k1_relat_1(C_380)
      | ~ m1_subset_1(C_380,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5204,c_5586])).

tff(c_5709,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5232,c_5697])).

tff(c_7355,plain,(
    ! [B_468,A_469,C_470] :
      ( k1_xboole_0 = B_468
      | k1_relset_1(A_469,B_468,C_470) = A_469
      | ~ v1_funct_2(C_470,A_469,B_468)
      | ~ m1_subset_1(C_470,k1_zfmisc_1(k2_zfmisc_1(A_469,B_468))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_7370,plain,(
    ! [C_470] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_470) = '#skF_1'
      | ~ v1_funct_2(C_470,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_470,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5204,c_7355])).

tff(c_7568,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_7370])).

tff(c_14,plain,(
    ! [B_6,A_5] :
      ( k1_xboole_0 = B_6
      | k1_xboole_0 = A_5
      | k2_zfmisc_1(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_5244,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_5204,c_14])).

tff(c_5295,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5244])).

tff(c_7595,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7568,c_5295])).

tff(c_7750,plain,(
    ! [A_483] : k2_zfmisc_1(A_483,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7568,c_7568,c_16])).

tff(c_6260,plain,(
    ! [B_421,C_422,A_423] :
      ( k1_xboole_0 = B_421
      | v1_funct_2(C_422,A_423,B_421)
      | k1_relset_1(A_423,B_421,C_422) != A_423
      | ~ m1_subset_1(C_422,k1_zfmisc_1(k2_zfmisc_1(A_423,B_421))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_6275,plain,(
    ! [C_422] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_2(C_422,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',C_422) != '#skF_1'
      | ~ m1_subset_1(C_422,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5204,c_6260])).

tff(c_6374,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_6275])).

tff(c_6417,plain,(
    ! [A_4] : r1_tarski('#skF_2',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6374,c_12])).

tff(c_6415,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6374,c_6374,c_16])).

tff(c_58,plain,(
    ! [A_32] :
      ( m1_subset_1(A_32,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_32),k2_relat_1(A_32))))
      | ~ v1_funct_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_5840,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5833,c_58])).

tff(c_5847,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_74,c_5840])).

tff(c_5878,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_5847,c_22])).

tff(c_5922,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_5878,c_6])).

tff(c_6039,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_5922])).

tff(c_6513,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6415,c_6039])).

tff(c_6519,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6417,c_6513])).

tff(c_6521,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_6275])).

tff(c_6807,plain,(
    ! [B_444,A_445,C_446] :
      ( k1_xboole_0 = B_444
      | k1_relset_1(A_445,B_444,C_446) = A_445
      | ~ v1_funct_2(C_446,A_445,B_444)
      | ~ m1_subset_1(C_446,k1_zfmisc_1(k2_zfmisc_1(A_445,B_444))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_6822,plain,(
    ! [C_446] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_446) = '#skF_1'
      | ~ v1_funct_2(C_446,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_446,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5204,c_6807])).

tff(c_7210,plain,(
    ! [C_462] :
      ( k1_relset_1('#skF_1','#skF_2',C_462) = '#skF_1'
      | ~ v1_funct_2(C_462,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_462,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6521,c_6822])).

tff(c_7213,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_5232,c_7210])).

tff(c_7224,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_5709,c_7213])).

tff(c_7228,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7224,c_6039])).

tff(c_7239,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_5204,c_7228])).

tff(c_7240,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5922])).

tff(c_7766,plain,(
    '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_7750,c_7240])).

tff(c_7804,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7595,c_7766])).

tff(c_8314,plain,(
    ! [C_507] :
      ( k1_relset_1('#skF_1','#skF_2',C_507) = '#skF_1'
      | ~ v1_funct_2(C_507,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_507,k1_zfmisc_1('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_7370])).

tff(c_8317,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_5232,c_8314])).

tff(c_8328,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_5709,c_8317])).

tff(c_5613,plain,(
    ! [A_374] :
      ( m1_subset_1(A_374,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_374),k2_relat_1(A_374))))
      | ~ v1_funct_1(A_374)
      | ~ v1_relat_1(A_374) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_10453,plain,(
    ! [A_615] :
      ( m1_subset_1(k2_funct_1(A_615),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_615)),k1_relat_1(A_615))))
      | ~ v1_funct_1(k2_funct_1(A_615))
      | ~ v1_relat_1(k2_funct_1(A_615))
      | ~ v2_funct_1(A_615)
      | ~ v1_funct_1(A_615)
      | ~ v1_relat_1(A_615) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_5613])).

tff(c_10482,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8328,c_10453])).

tff(c_10518,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_74,c_68,c_9505,c_249,c_10482])).

tff(c_10553,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_10518])).

tff(c_10574,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_74,c_68,c_5833,c_10553])).

tff(c_10576,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_312,c_10574])).

tff(c_10578,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5244])).

tff(c_18,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10590,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_3',B_6) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10578,c_10578,c_18])).

tff(c_10577,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5244])).

tff(c_10696,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10578,c_10578,c_10577])).

tff(c_10697,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_10696])).

tff(c_10700,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10697,c_312])).

tff(c_10782,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10590,c_10700])).

tff(c_20,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10591,plain,(
    ! [A_7] : m1_subset_1('#skF_3',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10578,c_20])).

tff(c_11228,plain,(
    ! [A_672,B_673,C_674] :
      ( k2_relset_1(A_672,B_673,C_674) = k2_relat_1(C_674)
      | ~ m1_subset_1(C_674,k1_zfmisc_1(k2_zfmisc_1(A_672,B_673))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_11255,plain,(
    ! [A_675,B_676] : k2_relset_1(A_675,B_676,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10591,c_11228])).

tff(c_10701,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10697,c_10697,c_66])).

tff(c_11259,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_11255,c_10701])).

tff(c_10829,plain,(
    ! [A_632] :
      ( k1_relat_1(k2_funct_1(A_632)) = k2_relat_1(A_632)
      | ~ v2_funct_1(A_632)
      | ~ v1_funct_1(A_632)
      | ~ v1_relat_1(A_632) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_12465,plain,(
    ! [A_746] :
      ( v1_funct_2(k2_funct_1(A_746),k2_relat_1(A_746),k2_relat_1(k2_funct_1(A_746)))
      | ~ v1_funct_1(k2_funct_1(A_746))
      | ~ v1_relat_1(k2_funct_1(A_746))
      | ~ v2_funct_1(A_746)
      | ~ v1_funct_1(A_746)
      | ~ v1_relat_1(A_746) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10829,c_60])).

tff(c_12474,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_11259,c_12465])).

tff(c_12486,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_74,c_68,c_249,c_12474])).

tff(c_12487,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_12486])).

tff(c_12490,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_12487])).

tff(c_12494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_74,c_12490])).

tff(c_12496,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_12486])).

tff(c_11140,plain,(
    ! [A_666] :
      ( m1_subset_1(A_666,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_666),k2_relat_1(A_666))))
      | ~ v1_funct_1(A_666)
      | ~ v1_relat_1(A_666) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_12739,plain,(
    ! [A_760] :
      ( m1_subset_1(k2_funct_1(A_760),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_760),k2_relat_1(k2_funct_1(A_760)))))
      | ~ v1_funct_1(k2_funct_1(A_760))
      | ~ v1_relat_1(k2_funct_1(A_760))
      | ~ v2_funct_1(A_760)
      | ~ v1_funct_1(A_760)
      | ~ v1_relat_1(A_760) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_11140])).

tff(c_12771,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_3')))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_11259,c_12739])).

tff(c_12791,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_74,c_68,c_12496,c_249,c_10590,c_12771])).

tff(c_12793,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10782,c_12791])).

tff(c_12794,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_10696])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_10595,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10578,c_2])).

tff(c_12802,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12794,c_10595])).

tff(c_12815,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5230,c_12802])).

tff(c_12817,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_5225])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_12833,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_12817,c_4])).

tff(c_12816,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_5225])).

tff(c_12825,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_12816,c_4])).

tff(c_12855,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12833,c_12825])).

tff(c_12845,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12825,c_12825,c_16])).

tff(c_12941,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12855,c_12855,c_12845])).

tff(c_12862,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12855,c_312])).

tff(c_13138,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12941,c_12862])).

tff(c_12863,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12855,c_274])).

tff(c_12870,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12855,c_74])).

tff(c_12869,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12855,c_68])).

tff(c_12864,plain,(
    v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12855,c_249])).

tff(c_116,plain,(
    ! [A_39] :
      ( v1_xboole_0(k1_relat_1(A_39))
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_121,plain,(
    ! [A_40] :
      ( k1_relat_1(A_40) = k1_xboole_0
      | ~ v1_xboole_0(A_40) ) ),
    inference(resolution,[status(thm)],[c_116,c_4])).

tff(c_129,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_121])).

tff(c_12841,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12825,c_12825,c_129])).

tff(c_12891,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12855,c_12855,c_12841])).

tff(c_13034,plain,(
    ! [A_773] :
      ( k2_relat_1(k2_funct_1(A_773)) = k1_relat_1(A_773)
      | ~ v2_funct_1(A_773)
      | ~ v1_funct_1(A_773)
      | ~ v1_relat_1(A_773) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_14867,plain,(
    ! [A_903] :
      ( v1_funct_2(k2_funct_1(A_903),k1_relat_1(k2_funct_1(A_903)),k1_relat_1(A_903))
      | ~ v1_funct_1(k2_funct_1(A_903))
      | ~ v1_relat_1(k2_funct_1(A_903))
      | ~ v2_funct_1(A_903)
      | ~ v1_funct_1(A_903)
      | ~ v1_relat_1(A_903) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13034,c_60])).

tff(c_14888,plain,
    ( v1_funct_2(k2_funct_1('#skF_1'),k1_relat_1(k2_funct_1('#skF_1')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_12891,c_14867])).

tff(c_14896,plain,
    ( v1_funct_2(k2_funct_1('#skF_1'),k1_relat_1(k2_funct_1('#skF_1')),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12863,c_12870,c_12869,c_12864,c_14888])).

tff(c_14897,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_14896])).

tff(c_14900,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_14897])).

tff(c_14904,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12863,c_12870,c_14900])).

tff(c_14906,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_14896])).

tff(c_13184,plain,(
    ! [A_789] :
      ( m1_subset_1(A_789,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_789),k2_relat_1(A_789))))
      | ~ v1_funct_1(A_789)
      | ~ v1_relat_1(A_789) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_15230,plain,(
    ! [A_931] :
      ( m1_subset_1(k2_funct_1(A_931),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_931)),k1_relat_1(A_931))))
      | ~ v1_funct_1(k2_funct_1(A_931))
      | ~ v1_relat_1(k2_funct_1(A_931))
      | ~ v2_funct_1(A_931)
      | ~ v1_funct_1(A_931)
      | ~ v1_relat_1(A_931) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_13184])).

tff(c_15277,plain,
    ( m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_1')),'#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_12891,c_15230])).

tff(c_15294,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12863,c_12870,c_12869,c_14906,c_12864,c_12941,c_15277])).

tff(c_15296,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13138,c_15294])).

tff(c_15297,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_248])).

tff(c_15298,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_248])).

tff(c_16673,plain,(
    ! [A_1049,B_1050,C_1051] :
      ( k1_relset_1(A_1049,B_1050,C_1051) = k1_relat_1(C_1051)
      | ~ m1_subset_1(C_1051,k1_zfmisc_1(k2_zfmisc_1(A_1049,B_1050))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_16700,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_15298,c_16673])).

tff(c_17274,plain,(
    ! [B_1095,C_1096,A_1097] :
      ( k1_xboole_0 = B_1095
      | v1_funct_2(C_1096,A_1097,B_1095)
      | k1_relset_1(A_1097,B_1095,C_1096) != A_1097
      | ~ m1_subset_1(C_1096,k1_zfmisc_1(k2_zfmisc_1(A_1097,B_1095))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_17289,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_15298,c_17274])).

tff(c_17312,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16700,c_17289])).

tff(c_17313,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_15297,c_17312])).

tff(c_17320,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_17313])).

tff(c_17323,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_17320])).

tff(c_17326,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_74,c_68,c_16671,c_17323])).

tff(c_17327,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_17313])).

tff(c_17370,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17327,c_2])).

tff(c_17372,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16373,c_17370])).

tff(c_17374,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_16368])).

tff(c_17390,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_17374,c_4])).

tff(c_17373,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_16368])).

tff(c_17382,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_17373,c_4])).

tff(c_17416,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17390,c_17382])).

tff(c_17403,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_3',B_6) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17382,c_17382,c_18])).

tff(c_17537,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_1',B_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17416,c_17416,c_17403])).

tff(c_15340,plain,(
    ! [B_937,A_938] :
      ( B_937 = A_938
      | ~ r1_tarski(B_937,A_938)
      | ~ r1_tarski(A_938,B_937) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_15350,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_173,c_15340])).

tff(c_16328,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_15350])).

tff(c_17424,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17416,c_16328])).

tff(c_17651,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_17537,c_17424])).

tff(c_17652,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_15350])).

tff(c_17725,plain,(
    ! [C_1121,A_1122,B_1123] :
      ( v1_xboole_0(C_1121)
      | ~ m1_subset_1(C_1121,k1_zfmisc_1(k2_zfmisc_1(A_1122,B_1123)))
      | ~ v1_xboole_0(A_1122) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_17728,plain,(
    ! [C_1121] :
      ( v1_xboole_0(C_1121)
      | ~ m1_subset_1(C_1121,k1_zfmisc_1('#skF_3'))
      | ~ v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17652,c_17725])).

tff(c_17796,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_17728])).

tff(c_17655,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17652,c_70])).

tff(c_18079,plain,(
    ! [A_1149,B_1150,C_1151] :
      ( k2_relset_1(A_1149,B_1150,C_1151) = k2_relat_1(C_1151)
      | ~ m1_subset_1(C_1151,k1_zfmisc_1(k2_zfmisc_1(A_1149,B_1150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_18287,plain,(
    ! [C_1170] :
      ( k2_relset_1('#skF_1','#skF_2',C_1170) = k2_relat_1(C_1170)
      | ~ m1_subset_1(C_1170,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17652,c_18079])).

tff(c_18290,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_17655,c_18287])).

tff(c_18300,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_18290])).

tff(c_18027,plain,(
    ! [A_1142,B_1143,C_1144] :
      ( k1_relset_1(A_1142,B_1143,C_1144) = k1_relat_1(C_1144)
      | ~ m1_subset_1(C_1144,k1_zfmisc_1(k2_zfmisc_1(A_1142,B_1143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_18054,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_15298,c_18027])).

tff(c_18877,plain,(
    ! [B_1202,C_1203,A_1204] :
      ( k1_xboole_0 = B_1202
      | v1_funct_2(C_1203,A_1204,B_1202)
      | k1_relset_1(A_1204,B_1202,C_1203) != A_1204
      | ~ m1_subset_1(C_1203,k1_zfmisc_1(k2_zfmisc_1(A_1204,B_1202))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_18895,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_15298,c_18877])).

tff(c_18915,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18054,c_18895])).

tff(c_18916,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_15297,c_18915])).

tff(c_18921,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_18916])).

tff(c_18924,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_18921])).

tff(c_18927,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_74,c_68,c_18300,c_18924])).

tff(c_18928,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_18916])).

tff(c_18973,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18928,c_2])).

tff(c_18975,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17796,c_18973])).

tff(c_18977,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_17728])).

tff(c_18985,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_18977,c_4])).

tff(c_17664,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_17652,c_14])).

tff(c_17723,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_17664])).

tff(c_18988,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18985,c_17723])).

tff(c_19001,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_1',B_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18985,c_18985,c_18])).

tff(c_19057,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19001,c_17652])).

tff(c_19059,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18988,c_19057])).

tff(c_19061,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_17664])).

tff(c_19072,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19061,c_19061,c_129])).

tff(c_19075,plain,(
    ! [A_7] : m1_subset_1('#skF_3',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19061,c_20])).

tff(c_19942,plain,(
    ! [A_1266,B_1267,C_1268] :
      ( k1_relset_1(A_1266,B_1267,C_1268) = k1_relat_1(C_1268)
      | ~ m1_subset_1(C_1268,k1_zfmisc_1(k2_zfmisc_1(A_1266,B_1267))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_19949,plain,(
    ! [A_1266,B_1267] : k1_relset_1(A_1266,B_1267,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_19075,c_19942])).

tff(c_19962,plain,(
    ! [A_1266,B_1267] : k1_relset_1(A_1266,B_1267,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19072,c_19949])).

tff(c_50,plain,(
    ! [C_31,B_30] :
      ( v1_funct_2(C_31,k1_xboole_0,B_30)
      | k1_relset_1(k1_xboole_0,B_30,C_31) != k1_xboole_0
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_78,plain,(
    ! [C_31,B_30] :
      ( v1_funct_2(C_31,k1_xboole_0,B_30)
      | k1_relset_1(k1_xboole_0,B_30,C_31) != k1_xboole_0
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_50])).

tff(c_20372,plain,(
    ! [C_1309,B_1310] :
      ( v1_funct_2(C_1309,'#skF_3',B_1310)
      | k1_relset_1('#skF_3',B_1310,C_1309) != '#skF_3'
      | ~ m1_subset_1(C_1309,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19061,c_19061,c_19061,c_19061,c_78])).

tff(c_20377,plain,(
    ! [B_1310] :
      ( v1_funct_2('#skF_3','#skF_3',B_1310)
      | k1_relset_1('#skF_3',B_1310,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_19075,c_20372])).

tff(c_20384,plain,(
    ! [B_1310] : v1_funct_2('#skF_3','#skF_3',B_1310) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19962,c_20377])).

tff(c_19079,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19061,c_2])).

tff(c_19060,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_17664])).

tff(c_19130,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19061,c_19061,c_19060])).

tff(c_19131,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_19130])).

tff(c_19086,plain,(
    ! [C_1207,A_1208,B_1209] :
      ( v1_xboole_0(C_1207)
      | ~ m1_subset_1(C_1207,k1_zfmisc_1(k2_zfmisc_1(A_1208,B_1209)))
      | ~ v1_xboole_0(A_1208) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_19097,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_15298,c_19086])).

tff(c_19129,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_19097])).

tff(c_19132,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19131,c_19129])).

tff(c_19142,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19079,c_19132])).

tff(c_19143,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_19130])).

tff(c_19144,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_19130])).

tff(c_19169,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19143,c_19144])).

tff(c_46,plain,(
    ! [A_29] :
      ( v1_funct_2(k1_xboole_0,A_29,k1_xboole_0)
      | k1_xboole_0 = A_29
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_29,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_76,plain,(
    ! [A_29] :
      ( v1_funct_2(k1_xboole_0,A_29,k1_xboole_0)
      | k1_xboole_0 = A_29 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_46])).

tff(c_19071,plain,(
    ! [A_29] :
      ( v1_funct_2('#skF_3',A_29,'#skF_3')
      | A_29 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19061,c_19061,c_19061,c_76])).

tff(c_19407,plain,(
    ! [A_29] :
      ( v1_funct_2('#skF_1',A_29,'#skF_1')
      | A_29 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19143,c_19143,c_19143,c_19071])).

tff(c_19076,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19061,c_19061,c_16])).

tff(c_19271,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19143,c_19143,c_19076])).

tff(c_15306,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_15298,c_22])).

tff(c_19155,plain,(
    r1_tarski(k2_funct_1('#skF_1'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19143,c_15306])).

tff(c_19415,plain,(
    r1_tarski(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19271,c_19155])).

tff(c_15351,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_15340])).

tff(c_19065,plain,(
    ! [A_4] :
      ( A_4 = '#skF_3'
      | ~ r1_tarski(A_4,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19061,c_19061,c_15351])).

tff(c_19339,plain,(
    ! [A_4] :
      ( A_4 = '#skF_1'
      | ~ r1_tarski(A_4,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19143,c_19143,c_19065])).

tff(c_19426,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_19415,c_19339])).

tff(c_19158,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19143,c_15297])).

tff(c_19431,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19426,c_19158])).

tff(c_19493,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_19407,c_19431])).

tff(c_19497,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19169,c_19493])).

tff(c_19498,plain,(
    v1_xboole_0(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_19097])).

tff(c_19537,plain,(
    ! [A_1235] :
      ( A_1235 = '#skF_3'
      | ~ v1_xboole_0(A_1235) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19061,c_4])).

tff(c_19547,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_19498,c_19537])).

tff(c_19519,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19061,c_19061,c_19060])).

tff(c_19520,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_19519])).

tff(c_19526,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19520,c_15297])).

tff(c_19700,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19547,c_19526])).

tff(c_20389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20384,c_19700])).

tff(c_20390,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_19519])).

tff(c_20391,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_19519])).

tff(c_20418,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20390,c_20391])).

tff(c_19499,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_19097])).

tff(c_19077,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19061,c_4])).

tff(c_20485,plain,(
    ! [A_1314] :
      ( A_1314 = '#skF_1'
      | ~ v1_xboole_0(A_1314) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20390,c_19077])).

tff(c_20494,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_19499,c_20485])).

tff(c_20504,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20418,c_20494])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:22:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.82/3.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.05/3.79  
% 10.05/3.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.05/3.79  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 10.05/3.79  
% 10.05/3.79  %Foreground sorts:
% 10.05/3.79  
% 10.05/3.79  
% 10.05/3.79  %Background operators:
% 10.05/3.79  
% 10.05/3.79  
% 10.05/3.79  %Foreground operators:
% 10.05/3.79  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.05/3.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.05/3.79  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 10.05/3.79  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.05/3.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.05/3.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.05/3.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.05/3.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.05/3.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.05/3.79  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.05/3.79  tff('#skF_2', type, '#skF_2': $i).
% 10.05/3.79  tff('#skF_3', type, '#skF_3': $i).
% 10.05/3.79  tff('#skF_1', type, '#skF_1': $i).
% 10.05/3.79  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.05/3.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.05/3.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.05/3.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.05/3.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.05/3.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.05/3.79  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.05/3.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.05/3.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.05/3.79  
% 10.05/3.83  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.05/3.83  tff(f_142, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 10.05/3.83  tff(f_89, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 10.05/3.83  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.05/3.83  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.05/3.83  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 10.05/3.83  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 10.05/3.83  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.05/3.83  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 10.05/3.83  tff(f_125, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 10.05/3.83  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 10.05/3.83  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 10.05/3.83  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.05/3.83  tff(f_46, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 10.05/3.83  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 10.05/3.83  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 10.05/3.83  tff(f_60, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 10.05/3.83  tff(c_10, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.05/3.83  tff(c_70, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 10.05/3.83  tff(c_16345, plain, (![C_1022, A_1023, B_1024]: (v1_xboole_0(C_1022) | ~m1_subset_1(C_1022, k1_zfmisc_1(k2_zfmisc_1(A_1023, B_1024))) | ~v1_xboole_0(A_1023))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.05/3.83  tff(c_16368, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_70, c_16345])).
% 10.05/3.83  tff(c_16373, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_16368])).
% 10.05/3.83  tff(c_257, plain, (![C_61, A_62, B_63]: (v1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.05/3.83  tff(c_274, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_257])).
% 10.05/3.83  tff(c_74, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 10.05/3.83  tff(c_68, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 10.05/3.83  tff(c_66, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_142])).
% 10.05/3.83  tff(c_16641, plain, (![A_1046, B_1047, C_1048]: (k2_relset_1(A_1046, B_1047, C_1048)=k2_relat_1(C_1048) | ~m1_subset_1(C_1048, k1_zfmisc_1(k2_zfmisc_1(A_1046, B_1047))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.05/3.83  tff(c_16657, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_16641])).
% 10.05/3.83  tff(c_16671, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_16657])).
% 10.05/3.83  tff(c_36, plain, (![A_15]: (k1_relat_1(k2_funct_1(A_15))=k2_relat_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.05/3.83  tff(c_5206, plain, (![C_336, A_337, B_338]: (v1_xboole_0(C_336) | ~m1_subset_1(C_336, k1_zfmisc_1(k2_zfmisc_1(A_337, B_338))) | ~v1_xboole_0(A_337))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.05/3.83  tff(c_5225, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_70, c_5206])).
% 10.05/3.83  tff(c_5230, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_5225])).
% 10.05/3.83  tff(c_177, plain, (![A_45]: (v1_funct_1(k2_funct_1(A_45)) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.05/3.83  tff(c_64, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 10.05/3.83  tff(c_176, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_64])).
% 10.05/3.83  tff(c_180, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_177, c_176])).
% 10.05/3.83  tff(c_183, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_180])).
% 10.05/3.83  tff(c_227, plain, (![C_54, A_55, B_56]: (v1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.05/3.83  tff(c_234, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_227])).
% 10.05/3.83  tff(c_247, plain, $false, inference(negUnitSimplification, [status(thm)], [c_183, c_234])).
% 10.05/3.83  tff(c_248, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_64])).
% 10.05/3.83  tff(c_312, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_248])).
% 10.05/3.83  tff(c_72, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_142])).
% 10.05/3.83  tff(c_854, plain, (![A_116, B_117, C_118]: (k1_relset_1(A_116, B_117, C_118)=k1_relat_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.05/3.83  tff(c_887, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_854])).
% 10.05/3.83  tff(c_4833, plain, (![B_326, A_327, C_328]: (k1_xboole_0=B_326 | k1_relset_1(A_327, B_326, C_328)=A_327 | ~v1_funct_2(C_328, A_327, B_326) | ~m1_subset_1(C_328, k1_zfmisc_1(k2_zfmisc_1(A_327, B_326))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.05/3.83  tff(c_4852, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_70, c_4833])).
% 10.05/3.83  tff(c_4867, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_887, c_4852])).
% 10.05/3.83  tff(c_4871, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_4867])).
% 10.05/3.83  tff(c_1794, plain, (![B_178, A_179, C_180]: (k1_xboole_0=B_178 | k1_relset_1(A_179, B_178, C_180)=A_179 | ~v1_funct_2(C_180, A_179, B_178) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_179, B_178))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.05/3.83  tff(c_1813, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_70, c_1794])).
% 10.05/3.83  tff(c_1831, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_887, c_1813])).
% 10.05/3.83  tff(c_1835, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_1831])).
% 10.05/3.83  tff(c_34, plain, (![A_15]: (k2_relat_1(k2_funct_1(A_15))=k1_relat_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.05/3.83  tff(c_32, plain, (![A_14]: (v1_relat_1(k2_funct_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.05/3.83  tff(c_249, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_64])).
% 10.05/3.83  tff(c_582, plain, (![A_98]: (k2_relat_1(k2_funct_1(A_98))=k1_relat_1(A_98) | ~v2_funct_1(A_98) | ~v1_funct_1(A_98) | ~v1_relat_1(A_98))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.05/3.83  tff(c_60, plain, (![A_32]: (v1_funct_2(A_32, k1_relat_1(A_32), k2_relat_1(A_32)) | ~v1_funct_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.05/3.83  tff(c_3137, plain, (![A_263]: (v1_funct_2(k2_funct_1(A_263), k1_relat_1(k2_funct_1(A_263)), k1_relat_1(A_263)) | ~v1_funct_1(k2_funct_1(A_263)) | ~v1_relat_1(k2_funct_1(A_263)) | ~v2_funct_1(A_263) | ~v1_funct_1(A_263) | ~v1_relat_1(A_263))), inference(superposition, [status(thm), theory('equality')], [c_582, c_60])).
% 10.05/3.83  tff(c_3140, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1835, c_3137])).
% 10.05/3.83  tff(c_3163, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_274, c_74, c_68, c_249, c_3140])).
% 10.05/3.83  tff(c_3172, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_3163])).
% 10.05/3.83  tff(c_3175, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_3172])).
% 10.05/3.83  tff(c_3179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_274, c_74, c_3175])).
% 10.05/3.83  tff(c_3181, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_3163])).
% 10.05/3.83  tff(c_680, plain, (![A_107, B_108, C_109]: (k2_relset_1(A_107, B_108, C_109)=k2_relat_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.05/3.83  tff(c_693, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_680])).
% 10.05/3.83  tff(c_706, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_693])).
% 10.05/3.83  tff(c_734, plain, (![A_114]: (m1_subset_1(A_114, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_114), k2_relat_1(A_114)))) | ~v1_funct_1(A_114) | ~v1_relat_1(A_114))), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.05/3.83  tff(c_3771, plain, (![A_286]: (m1_subset_1(k2_funct_1(A_286), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_286), k2_relat_1(k2_funct_1(A_286))))) | ~v1_funct_1(k2_funct_1(A_286)) | ~v1_relat_1(k2_funct_1(A_286)) | ~v2_funct_1(A_286) | ~v1_funct_1(A_286) | ~v1_relat_1(A_286))), inference(superposition, [status(thm), theory('equality')], [c_36, c_734])).
% 10.05/3.83  tff(c_3806, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3'))))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_706, c_3771])).
% 10.05/3.83  tff(c_3828, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_274, c_74, c_68, c_3181, c_249, c_3806])).
% 10.05/3.83  tff(c_3854, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3')))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34, c_3828])).
% 10.05/3.83  tff(c_3870, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_274, c_74, c_68, c_1835, c_3854])).
% 10.05/3.83  tff(c_3872, plain, $false, inference(negUnitSimplification, [status(thm)], [c_312, c_3870])).
% 10.05/3.83  tff(c_3873, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1831])).
% 10.05/3.83  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.05/3.83  tff(c_3921, plain, (![A_4]: (r1_tarski('#skF_2', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_3873, c_12])).
% 10.05/3.83  tff(c_16, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.05/3.83  tff(c_3919, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3873, c_3873, c_16])).
% 10.05/3.83  tff(c_751, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_706, c_734])).
% 10.05/3.83  tff(c_777, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_274, c_74, c_751])).
% 10.05/3.83  tff(c_22, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.05/3.83  tff(c_806, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_777, c_22])).
% 10.05/3.83  tff(c_6, plain, (![B_3, A_2]: (B_3=A_2 | ~r1_tarski(B_3, A_2) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.05/3.83  tff(c_824, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_806, c_6])).
% 10.05/3.83  tff(c_1018, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_824])).
% 10.05/3.83  tff(c_4010, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3919, c_1018])).
% 10.05/3.83  tff(c_4020, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3921, c_4010])).
% 10.05/3.83  tff(c_4021, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_824])).
% 10.05/3.83  tff(c_4876, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4871, c_4021])).
% 10.05/3.83  tff(c_166, plain, (![A_43, B_44]: (r1_tarski(A_43, B_44) | ~m1_subset_1(A_43, k1_zfmisc_1(B_44)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.05/3.83  tff(c_173, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_70, c_166])).
% 10.05/3.83  tff(c_345, plain, (![B_73, A_74]: (B_73=A_74 | ~r1_tarski(B_73, A_74) | ~r1_tarski(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.05/3.83  tff(c_352, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_173, c_345])).
% 10.05/3.83  tff(c_371, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_352])).
% 10.05/3.83  tff(c_4930, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4876, c_371])).
% 10.05/3.83  tff(c_4935, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_4930])).
% 10.05/3.83  tff(c_4936, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_4867])).
% 10.05/3.83  tff(c_4982, plain, (![A_4]: (r1_tarski('#skF_2', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_4936, c_12])).
% 10.05/3.83  tff(c_4980, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4936, c_4936, c_16])).
% 10.05/3.83  tff(c_5198, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4980, c_371])).
% 10.05/3.83  tff(c_5203, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4982, c_5198])).
% 10.05/3.83  tff(c_5204, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_352])).
% 10.05/3.83  tff(c_5232, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5204, c_70])).
% 10.05/3.83  tff(c_5762, plain, (![A_388, B_389, C_390]: (k2_relset_1(A_388, B_389, C_390)=k2_relat_1(C_390) | ~m1_subset_1(C_390, k1_zfmisc_1(k2_zfmisc_1(A_388, B_389))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.05/3.83  tff(c_5820, plain, (![C_397]: (k2_relset_1('#skF_1', '#skF_2', C_397)=k2_relat_1(C_397) | ~m1_subset_1(C_397, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5204, c_5762])).
% 10.05/3.83  tff(c_5823, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_5232, c_5820])).
% 10.05/3.83  tff(c_5833, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_5823])).
% 10.05/3.83  tff(c_5479, plain, (![A_361]: (k1_relat_1(k2_funct_1(A_361))=k2_relat_1(A_361) | ~v2_funct_1(A_361) | ~v1_funct_1(A_361) | ~v1_relat_1(A_361))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.05/3.83  tff(c_9474, plain, (![A_570]: (v1_funct_2(k2_funct_1(A_570), k2_relat_1(A_570), k2_relat_1(k2_funct_1(A_570))) | ~v1_funct_1(k2_funct_1(A_570)) | ~v1_relat_1(k2_funct_1(A_570)) | ~v2_funct_1(A_570) | ~v1_funct_1(A_570) | ~v1_relat_1(A_570))), inference(superposition, [status(thm), theory('equality')], [c_5479, c_60])).
% 10.05/3.83  tff(c_9483, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5833, c_9474])).
% 10.05/3.83  tff(c_9495, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_274, c_74, c_68, c_249, c_9483])).
% 10.05/3.83  tff(c_9496, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_9495])).
% 10.05/3.83  tff(c_9499, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_9496])).
% 10.05/3.83  tff(c_9503, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_274, c_74, c_9499])).
% 10.05/3.83  tff(c_9505, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_9495])).
% 10.05/3.83  tff(c_5586, plain, (![A_371, B_372, C_373]: (k1_relset_1(A_371, B_372, C_373)=k1_relat_1(C_373) | ~m1_subset_1(C_373, k1_zfmisc_1(k2_zfmisc_1(A_371, B_372))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.05/3.83  tff(c_5697, plain, (![C_380]: (k1_relset_1('#skF_1', '#skF_2', C_380)=k1_relat_1(C_380) | ~m1_subset_1(C_380, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5204, c_5586])).
% 10.05/3.83  tff(c_5709, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_5232, c_5697])).
% 10.05/3.83  tff(c_7355, plain, (![B_468, A_469, C_470]: (k1_xboole_0=B_468 | k1_relset_1(A_469, B_468, C_470)=A_469 | ~v1_funct_2(C_470, A_469, B_468) | ~m1_subset_1(C_470, k1_zfmisc_1(k2_zfmisc_1(A_469, B_468))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.05/3.83  tff(c_7370, plain, (![C_470]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_470)='#skF_1' | ~v1_funct_2(C_470, '#skF_1', '#skF_2') | ~m1_subset_1(C_470, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5204, c_7355])).
% 10.05/3.83  tff(c_7568, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_7370])).
% 10.05/3.83  tff(c_14, plain, (![B_6, A_5]: (k1_xboole_0=B_6 | k1_xboole_0=A_5 | k2_zfmisc_1(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.05/3.83  tff(c_5244, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_5204, c_14])).
% 10.05/3.83  tff(c_5295, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_5244])).
% 10.05/3.83  tff(c_7595, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7568, c_5295])).
% 10.05/3.83  tff(c_7750, plain, (![A_483]: (k2_zfmisc_1(A_483, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7568, c_7568, c_16])).
% 10.05/3.83  tff(c_6260, plain, (![B_421, C_422, A_423]: (k1_xboole_0=B_421 | v1_funct_2(C_422, A_423, B_421) | k1_relset_1(A_423, B_421, C_422)!=A_423 | ~m1_subset_1(C_422, k1_zfmisc_1(k2_zfmisc_1(A_423, B_421))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.05/3.83  tff(c_6275, plain, (![C_422]: (k1_xboole_0='#skF_2' | v1_funct_2(C_422, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', C_422)!='#skF_1' | ~m1_subset_1(C_422, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5204, c_6260])).
% 10.05/3.83  tff(c_6374, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_6275])).
% 10.05/3.83  tff(c_6417, plain, (![A_4]: (r1_tarski('#skF_2', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_6374, c_12])).
% 10.05/3.83  tff(c_6415, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6374, c_6374, c_16])).
% 10.05/3.83  tff(c_58, plain, (![A_32]: (m1_subset_1(A_32, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_32), k2_relat_1(A_32)))) | ~v1_funct_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.05/3.83  tff(c_5840, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5833, c_58])).
% 10.05/3.83  tff(c_5847, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_274, c_74, c_5840])).
% 10.05/3.83  tff(c_5878, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_5847, c_22])).
% 10.05/3.83  tff(c_5922, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_5878, c_6])).
% 10.05/3.83  tff(c_6039, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_5922])).
% 10.05/3.83  tff(c_6513, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6415, c_6039])).
% 10.05/3.83  tff(c_6519, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6417, c_6513])).
% 10.05/3.83  tff(c_6521, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_6275])).
% 10.05/3.83  tff(c_6807, plain, (![B_444, A_445, C_446]: (k1_xboole_0=B_444 | k1_relset_1(A_445, B_444, C_446)=A_445 | ~v1_funct_2(C_446, A_445, B_444) | ~m1_subset_1(C_446, k1_zfmisc_1(k2_zfmisc_1(A_445, B_444))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.05/3.83  tff(c_6822, plain, (![C_446]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_446)='#skF_1' | ~v1_funct_2(C_446, '#skF_1', '#skF_2') | ~m1_subset_1(C_446, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5204, c_6807])).
% 10.05/3.83  tff(c_7210, plain, (![C_462]: (k1_relset_1('#skF_1', '#skF_2', C_462)='#skF_1' | ~v1_funct_2(C_462, '#skF_1', '#skF_2') | ~m1_subset_1(C_462, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_6521, c_6822])).
% 10.05/3.83  tff(c_7213, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_5232, c_7210])).
% 10.05/3.83  tff(c_7224, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_5709, c_7213])).
% 10.05/3.83  tff(c_7228, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7224, c_6039])).
% 10.05/3.83  tff(c_7239, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_5204, c_7228])).
% 10.05/3.83  tff(c_7240, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_5922])).
% 10.05/3.83  tff(c_7766, plain, ('#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_7750, c_7240])).
% 10.05/3.83  tff(c_7804, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7595, c_7766])).
% 10.05/3.83  tff(c_8314, plain, (![C_507]: (k1_relset_1('#skF_1', '#skF_2', C_507)='#skF_1' | ~v1_funct_2(C_507, '#skF_1', '#skF_2') | ~m1_subset_1(C_507, k1_zfmisc_1('#skF_3')))), inference(splitRight, [status(thm)], [c_7370])).
% 10.05/3.83  tff(c_8317, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_5232, c_8314])).
% 10.05/3.83  tff(c_8328, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_5709, c_8317])).
% 10.05/3.83  tff(c_5613, plain, (![A_374]: (m1_subset_1(A_374, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_374), k2_relat_1(A_374)))) | ~v1_funct_1(A_374) | ~v1_relat_1(A_374))), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.05/3.83  tff(c_10453, plain, (![A_615]: (m1_subset_1(k2_funct_1(A_615), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_615)), k1_relat_1(A_615)))) | ~v1_funct_1(k2_funct_1(A_615)) | ~v1_relat_1(k2_funct_1(A_615)) | ~v2_funct_1(A_615) | ~v1_funct_1(A_615) | ~v1_relat_1(A_615))), inference(superposition, [status(thm), theory('equality')], [c_34, c_5613])).
% 10.05/3.83  tff(c_10482, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8328, c_10453])).
% 10.05/3.83  tff(c_10518, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_274, c_74, c_68, c_9505, c_249, c_10482])).
% 10.05/3.83  tff(c_10553, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_10518])).
% 10.05/3.83  tff(c_10574, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_274, c_74, c_68, c_5833, c_10553])).
% 10.05/3.83  tff(c_10576, plain, $false, inference(negUnitSimplification, [status(thm)], [c_312, c_10574])).
% 10.05/3.83  tff(c_10578, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_5244])).
% 10.05/3.83  tff(c_18, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.05/3.83  tff(c_10590, plain, (![B_6]: (k2_zfmisc_1('#skF_3', B_6)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10578, c_10578, c_18])).
% 10.05/3.83  tff(c_10577, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_5244])).
% 10.05/3.83  tff(c_10696, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10578, c_10578, c_10577])).
% 10.05/3.83  tff(c_10697, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_10696])).
% 10.05/3.83  tff(c_10700, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_10697, c_312])).
% 10.05/3.83  tff(c_10782, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_10590, c_10700])).
% 10.05/3.83  tff(c_20, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.05/3.83  tff(c_10591, plain, (![A_7]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_10578, c_20])).
% 10.05/3.83  tff(c_11228, plain, (![A_672, B_673, C_674]: (k2_relset_1(A_672, B_673, C_674)=k2_relat_1(C_674) | ~m1_subset_1(C_674, k1_zfmisc_1(k2_zfmisc_1(A_672, B_673))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.05/3.83  tff(c_11255, plain, (![A_675, B_676]: (k2_relset_1(A_675, B_676, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_10591, c_11228])).
% 10.05/3.83  tff(c_10701, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10697, c_10697, c_66])).
% 10.05/3.83  tff(c_11259, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_11255, c_10701])).
% 10.05/3.83  tff(c_10829, plain, (![A_632]: (k1_relat_1(k2_funct_1(A_632))=k2_relat_1(A_632) | ~v2_funct_1(A_632) | ~v1_funct_1(A_632) | ~v1_relat_1(A_632))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.05/3.83  tff(c_12465, plain, (![A_746]: (v1_funct_2(k2_funct_1(A_746), k2_relat_1(A_746), k2_relat_1(k2_funct_1(A_746))) | ~v1_funct_1(k2_funct_1(A_746)) | ~v1_relat_1(k2_funct_1(A_746)) | ~v2_funct_1(A_746) | ~v1_funct_1(A_746) | ~v1_relat_1(A_746))), inference(superposition, [status(thm), theory('equality')], [c_10829, c_60])).
% 10.05/3.83  tff(c_12474, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_11259, c_12465])).
% 10.05/3.83  tff(c_12486, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_274, c_74, c_68, c_249, c_12474])).
% 10.05/3.83  tff(c_12487, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_12486])).
% 10.05/3.83  tff(c_12490, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_12487])).
% 10.05/3.83  tff(c_12494, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_274, c_74, c_12490])).
% 10.05/3.83  tff(c_12496, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_12486])).
% 10.05/3.83  tff(c_11140, plain, (![A_666]: (m1_subset_1(A_666, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_666), k2_relat_1(A_666)))) | ~v1_funct_1(A_666) | ~v1_relat_1(A_666))), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.05/3.83  tff(c_12739, plain, (![A_760]: (m1_subset_1(k2_funct_1(A_760), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_760), k2_relat_1(k2_funct_1(A_760))))) | ~v1_funct_1(k2_funct_1(A_760)) | ~v1_relat_1(k2_funct_1(A_760)) | ~v2_funct_1(A_760) | ~v1_funct_1(A_760) | ~v1_relat_1(A_760))), inference(superposition, [status(thm), theory('equality')], [c_36, c_11140])).
% 10.05/3.83  tff(c_12771, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_3'))))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_11259, c_12739])).
% 10.05/3.83  tff(c_12791, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_274, c_74, c_68, c_12496, c_249, c_10590, c_12771])).
% 10.05/3.83  tff(c_12793, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10782, c_12791])).
% 10.05/3.83  tff(c_12794, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_10696])).
% 10.05/3.83  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 10.05/3.83  tff(c_10595, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10578, c_2])).
% 10.05/3.83  tff(c_12802, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12794, c_10595])).
% 10.05/3.83  tff(c_12815, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5230, c_12802])).
% 10.05/3.83  tff(c_12817, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_5225])).
% 10.05/3.83  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 10.05/3.83  tff(c_12833, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_12817, c_4])).
% 10.05/3.83  tff(c_12816, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_5225])).
% 10.05/3.83  tff(c_12825, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_12816, c_4])).
% 10.05/3.83  tff(c_12855, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12833, c_12825])).
% 10.05/3.83  tff(c_12845, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12825, c_12825, c_16])).
% 10.05/3.83  tff(c_12941, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12855, c_12855, c_12845])).
% 10.05/3.83  tff(c_12862, plain, (~m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_12855, c_312])).
% 10.05/3.83  tff(c_13138, plain, (~m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_12941, c_12862])).
% 10.05/3.83  tff(c_12863, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12855, c_274])).
% 10.05/3.83  tff(c_12870, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12855, c_74])).
% 10.05/3.83  tff(c_12869, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12855, c_68])).
% 10.05/3.83  tff(c_12864, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_12855, c_249])).
% 10.05/3.83  tff(c_116, plain, (![A_39]: (v1_xboole_0(k1_relat_1(A_39)) | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.05/3.83  tff(c_121, plain, (![A_40]: (k1_relat_1(A_40)=k1_xboole_0 | ~v1_xboole_0(A_40))), inference(resolution, [status(thm)], [c_116, c_4])).
% 10.05/3.83  tff(c_129, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_121])).
% 10.05/3.83  tff(c_12841, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12825, c_12825, c_129])).
% 10.05/3.83  tff(c_12891, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12855, c_12855, c_12841])).
% 10.05/3.83  tff(c_13034, plain, (![A_773]: (k2_relat_1(k2_funct_1(A_773))=k1_relat_1(A_773) | ~v2_funct_1(A_773) | ~v1_funct_1(A_773) | ~v1_relat_1(A_773))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.05/3.83  tff(c_14867, plain, (![A_903]: (v1_funct_2(k2_funct_1(A_903), k1_relat_1(k2_funct_1(A_903)), k1_relat_1(A_903)) | ~v1_funct_1(k2_funct_1(A_903)) | ~v1_relat_1(k2_funct_1(A_903)) | ~v2_funct_1(A_903) | ~v1_funct_1(A_903) | ~v1_relat_1(A_903))), inference(superposition, [status(thm), theory('equality')], [c_13034, c_60])).
% 10.05/3.83  tff(c_14888, plain, (v1_funct_2(k2_funct_1('#skF_1'), k1_relat_1(k2_funct_1('#skF_1')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_12891, c_14867])).
% 10.05/3.83  tff(c_14896, plain, (v1_funct_2(k2_funct_1('#skF_1'), k1_relat_1(k2_funct_1('#skF_1')), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_12863, c_12870, c_12869, c_12864, c_14888])).
% 10.05/3.83  tff(c_14897, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_14896])).
% 10.05/3.83  tff(c_14900, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_32, c_14897])).
% 10.05/3.83  tff(c_14904, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12863, c_12870, c_14900])).
% 10.05/3.83  tff(c_14906, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_14896])).
% 10.05/3.83  tff(c_13184, plain, (![A_789]: (m1_subset_1(A_789, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_789), k2_relat_1(A_789)))) | ~v1_funct_1(A_789) | ~v1_relat_1(A_789))), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.05/3.83  tff(c_15230, plain, (![A_931]: (m1_subset_1(k2_funct_1(A_931), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_931)), k1_relat_1(A_931)))) | ~v1_funct_1(k2_funct_1(A_931)) | ~v1_relat_1(k2_funct_1(A_931)) | ~v2_funct_1(A_931) | ~v1_funct_1(A_931) | ~v1_relat_1(A_931))), inference(superposition, [status(thm), theory('equality')], [c_34, c_13184])).
% 10.05/3.83  tff(c_15277, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_1')), '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_12891, c_15230])).
% 10.05/3.83  tff(c_15294, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_12863, c_12870, c_12869, c_14906, c_12864, c_12941, c_15277])).
% 10.05/3.83  tff(c_15296, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13138, c_15294])).
% 10.05/3.83  tff(c_15297, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_248])).
% 10.05/3.83  tff(c_15298, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_248])).
% 10.05/3.83  tff(c_16673, plain, (![A_1049, B_1050, C_1051]: (k1_relset_1(A_1049, B_1050, C_1051)=k1_relat_1(C_1051) | ~m1_subset_1(C_1051, k1_zfmisc_1(k2_zfmisc_1(A_1049, B_1050))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.05/3.83  tff(c_16700, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_15298, c_16673])).
% 10.05/3.83  tff(c_17274, plain, (![B_1095, C_1096, A_1097]: (k1_xboole_0=B_1095 | v1_funct_2(C_1096, A_1097, B_1095) | k1_relset_1(A_1097, B_1095, C_1096)!=A_1097 | ~m1_subset_1(C_1096, k1_zfmisc_1(k2_zfmisc_1(A_1097, B_1095))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.05/3.83  tff(c_17289, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_15298, c_17274])).
% 10.05/3.83  tff(c_17312, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_16700, c_17289])).
% 10.05/3.83  tff(c_17313, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_15297, c_17312])).
% 10.34/3.83  tff(c_17320, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_17313])).
% 10.34/3.83  tff(c_17323, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_17320])).
% 10.34/3.83  tff(c_17326, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_274, c_74, c_68, c_16671, c_17323])).
% 10.34/3.83  tff(c_17327, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_17313])).
% 10.34/3.83  tff(c_17370, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_17327, c_2])).
% 10.34/3.83  tff(c_17372, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16373, c_17370])).
% 10.34/3.83  tff(c_17374, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_16368])).
% 10.34/3.83  tff(c_17390, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_17374, c_4])).
% 10.34/3.83  tff(c_17373, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_16368])).
% 10.34/3.83  tff(c_17382, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_17373, c_4])).
% 10.34/3.83  tff(c_17416, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_17390, c_17382])).
% 10.34/3.83  tff(c_17403, plain, (![B_6]: (k2_zfmisc_1('#skF_3', B_6)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_17382, c_17382, c_18])).
% 10.34/3.83  tff(c_17537, plain, (![B_6]: (k2_zfmisc_1('#skF_1', B_6)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_17416, c_17416, c_17403])).
% 10.34/3.83  tff(c_15340, plain, (![B_937, A_938]: (B_937=A_938 | ~r1_tarski(B_937, A_938) | ~r1_tarski(A_938, B_937))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.34/3.83  tff(c_15350, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_173, c_15340])).
% 10.34/3.83  tff(c_16328, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_15350])).
% 10.34/3.83  tff(c_17424, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_17416, c_16328])).
% 10.34/3.83  tff(c_17651, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_17537, c_17424])).
% 10.34/3.83  tff(c_17652, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_15350])).
% 10.34/3.83  tff(c_17725, plain, (![C_1121, A_1122, B_1123]: (v1_xboole_0(C_1121) | ~m1_subset_1(C_1121, k1_zfmisc_1(k2_zfmisc_1(A_1122, B_1123))) | ~v1_xboole_0(A_1122))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.34/3.83  tff(c_17728, plain, (![C_1121]: (v1_xboole_0(C_1121) | ~m1_subset_1(C_1121, k1_zfmisc_1('#skF_3')) | ~v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_17652, c_17725])).
% 10.34/3.83  tff(c_17796, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_17728])).
% 10.34/3.83  tff(c_17655, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_17652, c_70])).
% 10.34/3.83  tff(c_18079, plain, (![A_1149, B_1150, C_1151]: (k2_relset_1(A_1149, B_1150, C_1151)=k2_relat_1(C_1151) | ~m1_subset_1(C_1151, k1_zfmisc_1(k2_zfmisc_1(A_1149, B_1150))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.34/3.83  tff(c_18287, plain, (![C_1170]: (k2_relset_1('#skF_1', '#skF_2', C_1170)=k2_relat_1(C_1170) | ~m1_subset_1(C_1170, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_17652, c_18079])).
% 10.34/3.83  tff(c_18290, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_17655, c_18287])).
% 10.34/3.83  tff(c_18300, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_18290])).
% 10.34/3.83  tff(c_18027, plain, (![A_1142, B_1143, C_1144]: (k1_relset_1(A_1142, B_1143, C_1144)=k1_relat_1(C_1144) | ~m1_subset_1(C_1144, k1_zfmisc_1(k2_zfmisc_1(A_1142, B_1143))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.34/3.83  tff(c_18054, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_15298, c_18027])).
% 10.34/3.83  tff(c_18877, plain, (![B_1202, C_1203, A_1204]: (k1_xboole_0=B_1202 | v1_funct_2(C_1203, A_1204, B_1202) | k1_relset_1(A_1204, B_1202, C_1203)!=A_1204 | ~m1_subset_1(C_1203, k1_zfmisc_1(k2_zfmisc_1(A_1204, B_1202))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.34/3.83  tff(c_18895, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_15298, c_18877])).
% 10.34/3.83  tff(c_18915, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18054, c_18895])).
% 10.34/3.83  tff(c_18916, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_15297, c_18915])).
% 10.34/3.83  tff(c_18921, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_18916])).
% 10.34/3.83  tff(c_18924, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_18921])).
% 10.34/3.83  tff(c_18927, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_274, c_74, c_68, c_18300, c_18924])).
% 10.34/3.83  tff(c_18928, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_18916])).
% 10.34/3.83  tff(c_18973, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18928, c_2])).
% 10.34/3.83  tff(c_18975, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17796, c_18973])).
% 10.34/3.83  tff(c_18977, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_17728])).
% 10.34/3.83  tff(c_18985, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_18977, c_4])).
% 10.34/3.83  tff(c_17664, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_17652, c_14])).
% 10.34/3.83  tff(c_17723, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_17664])).
% 10.34/3.83  tff(c_18988, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18985, c_17723])).
% 10.34/3.83  tff(c_19001, plain, (![B_6]: (k2_zfmisc_1('#skF_1', B_6)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18985, c_18985, c_18])).
% 10.34/3.83  tff(c_19057, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_19001, c_17652])).
% 10.34/3.83  tff(c_19059, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18988, c_19057])).
% 10.34/3.83  tff(c_19061, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_17664])).
% 10.34/3.83  tff(c_19072, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_19061, c_19061, c_129])).
% 10.34/3.83  tff(c_19075, plain, (![A_7]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_19061, c_20])).
% 10.34/3.83  tff(c_19942, plain, (![A_1266, B_1267, C_1268]: (k1_relset_1(A_1266, B_1267, C_1268)=k1_relat_1(C_1268) | ~m1_subset_1(C_1268, k1_zfmisc_1(k2_zfmisc_1(A_1266, B_1267))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.34/3.83  tff(c_19949, plain, (![A_1266, B_1267]: (k1_relset_1(A_1266, B_1267, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_19075, c_19942])).
% 10.34/3.83  tff(c_19962, plain, (![A_1266, B_1267]: (k1_relset_1(A_1266, B_1267, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_19072, c_19949])).
% 10.34/3.83  tff(c_50, plain, (![C_31, B_30]: (v1_funct_2(C_31, k1_xboole_0, B_30) | k1_relset_1(k1_xboole_0, B_30, C_31)!=k1_xboole_0 | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_30))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.34/3.83  tff(c_78, plain, (![C_31, B_30]: (v1_funct_2(C_31, k1_xboole_0, B_30) | k1_relset_1(k1_xboole_0, B_30, C_31)!=k1_xboole_0 | ~m1_subset_1(C_31, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_50])).
% 10.34/3.83  tff(c_20372, plain, (![C_1309, B_1310]: (v1_funct_2(C_1309, '#skF_3', B_1310) | k1_relset_1('#skF_3', B_1310, C_1309)!='#skF_3' | ~m1_subset_1(C_1309, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_19061, c_19061, c_19061, c_19061, c_78])).
% 10.34/3.83  tff(c_20377, plain, (![B_1310]: (v1_funct_2('#skF_3', '#skF_3', B_1310) | k1_relset_1('#skF_3', B_1310, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_19075, c_20372])).
% 10.34/3.83  tff(c_20384, plain, (![B_1310]: (v1_funct_2('#skF_3', '#skF_3', B_1310))), inference(demodulation, [status(thm), theory('equality')], [c_19962, c_20377])).
% 10.34/3.83  tff(c_19079, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_19061, c_2])).
% 10.34/3.83  tff(c_19060, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_17664])).
% 10.34/3.83  tff(c_19130, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_19061, c_19061, c_19060])).
% 10.34/3.83  tff(c_19131, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_19130])).
% 10.34/3.83  tff(c_19086, plain, (![C_1207, A_1208, B_1209]: (v1_xboole_0(C_1207) | ~m1_subset_1(C_1207, k1_zfmisc_1(k2_zfmisc_1(A_1208, B_1209))) | ~v1_xboole_0(A_1208))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.34/3.83  tff(c_19097, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_15298, c_19086])).
% 10.34/3.83  tff(c_19129, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_19097])).
% 10.34/3.83  tff(c_19132, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_19131, c_19129])).
% 10.34/3.83  tff(c_19142, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19079, c_19132])).
% 10.34/3.83  tff(c_19143, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_19130])).
% 10.34/3.83  tff(c_19144, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_19130])).
% 10.34/3.83  tff(c_19169, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_19143, c_19144])).
% 10.34/3.83  tff(c_46, plain, (![A_29]: (v1_funct_2(k1_xboole_0, A_29, k1_xboole_0) | k1_xboole_0=A_29 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_29, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.34/3.83  tff(c_76, plain, (![A_29]: (v1_funct_2(k1_xboole_0, A_29, k1_xboole_0) | k1_xboole_0=A_29)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_46])).
% 10.34/3.83  tff(c_19071, plain, (![A_29]: (v1_funct_2('#skF_3', A_29, '#skF_3') | A_29='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_19061, c_19061, c_19061, c_76])).
% 10.34/3.83  tff(c_19407, plain, (![A_29]: (v1_funct_2('#skF_1', A_29, '#skF_1') | A_29='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_19143, c_19143, c_19143, c_19071])).
% 10.34/3.83  tff(c_19076, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_19061, c_19061, c_16])).
% 10.34/3.83  tff(c_19271, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_19143, c_19143, c_19076])).
% 10.34/3.83  tff(c_15306, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_15298, c_22])).
% 10.34/3.83  tff(c_19155, plain, (r1_tarski(k2_funct_1('#skF_1'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_19143, c_15306])).
% 10.34/3.83  tff(c_19415, plain, (r1_tarski(k2_funct_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_19271, c_19155])).
% 10.34/3.83  tff(c_15351, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_15340])).
% 10.34/3.83  tff(c_19065, plain, (![A_4]: (A_4='#skF_3' | ~r1_tarski(A_4, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_19061, c_19061, c_15351])).
% 10.34/3.83  tff(c_19339, plain, (![A_4]: (A_4='#skF_1' | ~r1_tarski(A_4, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_19143, c_19143, c_19065])).
% 10.34/3.83  tff(c_19426, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_19415, c_19339])).
% 10.34/3.83  tff(c_19158, plain, (~v1_funct_2(k2_funct_1('#skF_1'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_19143, c_15297])).
% 10.34/3.83  tff(c_19431, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_19426, c_19158])).
% 10.34/3.83  tff(c_19493, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_19407, c_19431])).
% 10.34/3.83  tff(c_19497, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19169, c_19493])).
% 10.34/3.83  tff(c_19498, plain, (v1_xboole_0(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_19097])).
% 10.34/3.83  tff(c_19537, plain, (![A_1235]: (A_1235='#skF_3' | ~v1_xboole_0(A_1235))), inference(demodulation, [status(thm), theory('equality')], [c_19061, c_4])).
% 10.34/3.83  tff(c_19547, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_19498, c_19537])).
% 10.34/3.83  tff(c_19519, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_19061, c_19061, c_19060])).
% 10.34/3.83  tff(c_19520, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_19519])).
% 10.34/3.83  tff(c_19526, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_19520, c_15297])).
% 10.34/3.83  tff(c_19700, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_19547, c_19526])).
% 10.34/3.83  tff(c_20389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20384, c_19700])).
% 10.34/3.83  tff(c_20390, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_19519])).
% 10.34/3.83  tff(c_20391, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_19519])).
% 10.34/3.83  tff(c_20418, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20390, c_20391])).
% 10.34/3.83  tff(c_19499, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_19097])).
% 10.34/3.83  tff(c_19077, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_19061, c_4])).
% 10.34/3.83  tff(c_20485, plain, (![A_1314]: (A_1314='#skF_1' | ~v1_xboole_0(A_1314))), inference(demodulation, [status(thm), theory('equality')], [c_20390, c_19077])).
% 10.34/3.83  tff(c_20494, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_19499, c_20485])).
% 10.34/3.83  tff(c_20504, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20418, c_20494])).
% 10.34/3.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.34/3.83  
% 10.34/3.83  Inference rules
% 10.34/3.83  ----------------------
% 10.34/3.83  #Ref     : 0
% 10.34/3.83  #Sup     : 4620
% 10.34/3.83  #Fact    : 0
% 10.34/3.83  #Define  : 0
% 10.34/3.83  #Split   : 57
% 10.34/3.83  #Chain   : 0
% 10.34/3.83  #Close   : 0
% 10.34/3.83  
% 10.34/3.83  Ordering : KBO
% 10.34/3.83  
% 10.34/3.83  Simplification rules
% 10.34/3.83  ----------------------
% 10.34/3.83  #Subsume      : 893
% 10.34/3.83  #Demod        : 4618
% 10.34/3.83  #Tautology    : 2086
% 10.34/3.83  #SimpNegUnit  : 49
% 10.34/3.83  #BackRed      : 607
% 10.34/3.83  
% 10.34/3.83  #Partial instantiations: 0
% 10.34/3.83  #Strategies tried      : 1
% 10.34/3.83  
% 10.34/3.83  Timing (in seconds)
% 10.34/3.83  ----------------------
% 10.34/3.84  Preprocessing        : 0.35
% 10.34/3.84  Parsing              : 0.18
% 10.34/3.84  CNF conversion       : 0.02
% 10.34/3.84  Main loop            : 2.63
% 10.34/3.84  Inferencing          : 0.82
% 10.34/3.84  Reduction            : 0.94
% 10.34/3.84  Demodulation         : 0.67
% 10.34/3.84  BG Simplification    : 0.09
% 10.34/3.84  Subsumption          : 0.57
% 10.34/3.84  Abstraction          : 0.12
% 10.34/3.84  MUC search           : 0.00
% 10.34/3.84  Cooper               : 0.00
% 10.34/3.84  Total                : 3.09
% 10.34/3.84  Index Insertion      : 0.00
% 10.34/3.84  Index Deletion       : 0.00
% 10.34/3.84  Index Matching       : 0.00
% 10.34/3.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
