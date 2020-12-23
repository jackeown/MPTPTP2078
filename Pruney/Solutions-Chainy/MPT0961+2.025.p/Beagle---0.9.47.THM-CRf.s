%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:44 EST 2020

% Result     : Theorem 5.69s
% Output     : CNFRefutation 5.75s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 539 expanded)
%              Number of leaves         :   33 ( 194 expanded)
%              Depth                    :   13
%              Number of atoms          :  172 (1131 expanded)
%              Number of equality atoms :   45 ( 237 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_48,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_50,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_95,axiom,(
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

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_48,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_16,plain,(
    ! [A_9] : k2_subset_1(A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_18,plain,(
    ! [A_10] : m1_subset_1(k2_subset_1(A_10),k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_51,plain,(
    ! [A_10] : m1_subset_1(A_10,k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18])).

tff(c_4752,plain,(
    ! [A_348,B_349] :
      ( r1_tarski(A_348,B_349)
      | ~ m1_subset_1(A_348,k1_zfmisc_1(B_349)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4760,plain,(
    ! [A_10] : r1_tarski(A_10,A_10) ),
    inference(resolution,[status(thm)],[c_51,c_4752])).

tff(c_5037,plain,(
    ! [C_379,A_380,B_381] :
      ( m1_subset_1(C_379,k1_zfmisc_1(k2_zfmisc_1(A_380,B_381)))
      | ~ r1_tarski(k2_relat_1(C_379),B_381)
      | ~ r1_tarski(k1_relat_1(C_379),A_380)
      | ~ v1_relat_1(C_379) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_158,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,B_41)
      | ~ m1_subset_1(A_40,k1_zfmisc_1(B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_162,plain,(
    ! [A_10] : r1_tarski(A_10,A_10) ),
    inference(resolution,[status(thm)],[c_51,c_158])).

tff(c_484,plain,(
    ! [C_79,A_80,B_81] :
      ( m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81)))
      | ~ r1_tarski(k2_relat_1(C_79),B_81)
      | ~ r1_tarski(k1_relat_1(C_79),A_80)
      | ~ v1_relat_1(C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1289,plain,(
    ! [C_149,A_150,B_151] :
      ( r1_tarski(C_149,k2_zfmisc_1(A_150,B_151))
      | ~ r1_tarski(k2_relat_1(C_149),B_151)
      | ~ r1_tarski(k1_relat_1(C_149),A_150)
      | ~ v1_relat_1(C_149) ) ),
    inference(resolution,[status(thm)],[c_484,c_20])).

tff(c_1294,plain,(
    ! [C_152,A_153] :
      ( r1_tarski(C_152,k2_zfmisc_1(A_153,k2_relat_1(C_152)))
      | ~ r1_tarski(k1_relat_1(C_152),A_153)
      | ~ v1_relat_1(C_152) ) ),
    inference(resolution,[status(thm)],[c_162,c_1289])).

tff(c_22,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_280,plain,(
    ! [A_60,B_61,C_62] :
      ( k1_relset_1(A_60,B_61,C_62) = k1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_295,plain,(
    ! [A_60,B_61,A_11] :
      ( k1_relset_1(A_60,B_61,A_11) = k1_relat_1(A_11)
      | ~ r1_tarski(A_11,k2_zfmisc_1(A_60,B_61)) ) ),
    inference(resolution,[status(thm)],[c_22,c_280])).

tff(c_1338,plain,(
    ! [A_155,C_156] :
      ( k1_relset_1(A_155,k2_relat_1(C_156),C_156) = k1_relat_1(C_156)
      | ~ r1_tarski(k1_relat_1(C_156),A_155)
      | ~ v1_relat_1(C_156) ) ),
    inference(resolution,[status(thm)],[c_1294,c_295])).

tff(c_1357,plain,(
    ! [C_156] :
      ( k1_relset_1(k1_relat_1(C_156),k2_relat_1(C_156),C_156) = k1_relat_1(C_156)
      | ~ v1_relat_1(C_156) ) ),
    inference(resolution,[status(thm)],[c_162,c_1338])).

tff(c_30,plain,(
    ! [C_23,A_21,B_22] :
      ( m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ r1_tarski(k2_relat_1(C_23),B_22)
      | ~ r1_tarski(k1_relat_1(C_23),A_21)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_678,plain,(
    ! [B_100,C_101,A_102] :
      ( k1_xboole_0 = B_100
      | v1_funct_2(C_101,A_102,B_100)
      | k1_relset_1(A_102,B_100,C_101) != A_102
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_102,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_3883,plain,(
    ! [B_302,C_303,A_304] :
      ( k1_xboole_0 = B_302
      | v1_funct_2(C_303,A_304,B_302)
      | k1_relset_1(A_304,B_302,C_303) != A_304
      | ~ r1_tarski(k2_relat_1(C_303),B_302)
      | ~ r1_tarski(k1_relat_1(C_303),A_304)
      | ~ v1_relat_1(C_303) ) ),
    inference(resolution,[status(thm)],[c_30,c_678])).

tff(c_4338,plain,(
    ! [C_335,A_336] :
      ( k2_relat_1(C_335) = k1_xboole_0
      | v1_funct_2(C_335,A_336,k2_relat_1(C_335))
      | k1_relset_1(A_336,k2_relat_1(C_335),C_335) != A_336
      | ~ r1_tarski(k1_relat_1(C_335),A_336)
      | ~ v1_relat_1(C_335) ) ),
    inference(resolution,[status(thm)],[c_162,c_3883])).

tff(c_46,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_44,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_50,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44])).

tff(c_92,plain,(
    ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_4350,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k1_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4338,c_92])).

tff(c_4358,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_162,c_4350])).

tff(c_4359,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_4358])).

tff(c_4362,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1357,c_4359])).

tff(c_4366,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4362])).

tff(c_4367,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_4358])).

tff(c_26,plain,(
    ! [C_17,B_15,A_14] :
      ( v1_xboole_0(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(B_15,A_14)))
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1059,plain,(
    ! [C_128,B_129,A_130] :
      ( v1_xboole_0(C_128)
      | ~ v1_xboole_0(B_129)
      | ~ r1_tarski(k2_relat_1(C_128),B_129)
      | ~ r1_tarski(k1_relat_1(C_128),A_130)
      | ~ v1_relat_1(C_128) ) ),
    inference(resolution,[status(thm)],[c_484,c_26])).

tff(c_1064,plain,(
    ! [C_131,A_132] :
      ( v1_xboole_0(C_131)
      | ~ v1_xboole_0(k2_relat_1(C_131))
      | ~ r1_tarski(k1_relat_1(C_131),A_132)
      | ~ v1_relat_1(C_131) ) ),
    inference(resolution,[status(thm)],[c_162,c_1059])).

tff(c_1080,plain,(
    ! [C_131] :
      ( v1_xboole_0(C_131)
      | ~ v1_xboole_0(k2_relat_1(C_131))
      | ~ v1_relat_1(C_131) ) ),
    inference(resolution,[status(thm)],[c_162,c_1064])).

tff(c_4394,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4367,c_1080])).

tff(c_4418,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_6,c_4394])).

tff(c_99,plain,(
    ! [A_36] :
      ( r2_hidden('#skF_2'(A_36),A_36)
      | k1_xboole_0 = A_36 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_103,plain,(
    ! [A_36] :
      ( ~ v1_xboole_0(A_36)
      | k1_xboole_0 = A_36 ) ),
    inference(resolution,[status(thm)],[c_99,c_2])).

tff(c_4432,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4418,c_103])).

tff(c_24,plain,(
    ! [A_13] :
      ( v1_xboole_0(k1_relat_1(A_13))
      | ~ v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_104,plain,(
    ! [A_37] :
      ( ~ v1_xboole_0(A_37)
      | k1_xboole_0 = A_37 ) ),
    inference(resolution,[status(thm)],[c_99,c_2])).

tff(c_114,plain,(
    ! [A_38] :
      ( k1_relat_1(A_38) = k1_xboole_0
      | ~ v1_xboole_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_24,c_104])).

tff(c_122,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_114])).

tff(c_14,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_421,plain,(
    ! [A_71,B_72] : k1_relset_1(A_71,B_72,k2_zfmisc_1(A_71,B_72)) = k1_relat_1(k2_zfmisc_1(A_71,B_72)) ),
    inference(resolution,[status(thm)],[c_51,c_280])).

tff(c_436,plain,(
    ! [B_8] : k1_relat_1(k2_zfmisc_1(k1_xboole_0,B_8)) = k1_relset_1(k1_xboole_0,B_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_421])).

tff(c_442,plain,(
    ! [B_8] : k1_relset_1(k1_xboole_0,B_8,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_14,c_436])).

tff(c_36,plain,(
    ! [C_26,B_25] :
      ( v1_funct_2(C_26,k1_xboole_0,B_25)
      | k1_relset_1(k1_xboole_0,B_25,C_26) != k1_xboole_0
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_603,plain,(
    ! [C_93,B_94] :
      ( v1_funct_2(C_93,k1_xboole_0,B_94)
      | k1_relset_1(k1_xboole_0,B_94,C_93) != k1_xboole_0
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_36])).

tff(c_609,plain,(
    ! [B_94] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_94)
      | k1_relset_1(k1_xboole_0,B_94,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_51,c_603])).

tff(c_613,plain,(
    ! [B_94] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_94) ),
    inference(demodulation,[status(thm),theory(equality)],[c_442,c_609])).

tff(c_4484,plain,(
    ! [B_94] : v1_funct_2('#skF_3','#skF_3',B_94) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4432,c_4432,c_613])).

tff(c_111,plain,(
    ! [A_13] :
      ( k1_relat_1(A_13) = k1_xboole_0
      | ~ v1_xboole_0(A_13) ) ),
    inference(resolution,[status(thm)],[c_24,c_104])).

tff(c_4431,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4418,c_111])).

tff(c_4517,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4432,c_4431])).

tff(c_4369,plain,(
    ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4367,c_92])).

tff(c_4433,plain,(
    ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4432,c_4369])).

tff(c_4662,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4517,c_4433])).

tff(c_4679,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4484,c_4662])).

tff(c_4680,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_5049,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5037,c_4680])).

tff(c_5068,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4760,c_4760,c_5049])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:13:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.69/2.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.75/2.08  
% 5.75/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.75/2.08  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3
% 5.75/2.08  
% 5.75/2.08  %Foreground sorts:
% 5.75/2.08  
% 5.75/2.08  
% 5.75/2.08  %Background operators:
% 5.75/2.08  
% 5.75/2.08  
% 5.75/2.08  %Foreground operators:
% 5.75/2.08  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.75/2.08  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.75/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.75/2.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.75/2.08  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.75/2.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.75/2.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.75/2.08  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.75/2.08  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.75/2.08  tff('#skF_3', type, '#skF_3': $i).
% 5.75/2.08  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.75/2.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.75/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.75/2.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.75/2.08  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.75/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.75/2.08  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.75/2.08  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.75/2.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.75/2.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.75/2.08  
% 5.75/2.10  tff(f_106, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 5.75/2.10  tff(f_48, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 5.75/2.10  tff(f_50, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 5.75/2.10  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.75/2.10  tff(f_77, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 5.75/2.10  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.75/2.10  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.75/2.10  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.75/2.10  tff(f_65, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 5.75/2.10  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.75/2.10  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.75/2.10  tff(f_58, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 5.75/2.10  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.75/2.10  tff(c_48, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.75/2.10  tff(c_16, plain, (![A_9]: (k2_subset_1(A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.75/2.10  tff(c_18, plain, (![A_10]: (m1_subset_1(k2_subset_1(A_10), k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.75/2.10  tff(c_51, plain, (![A_10]: (m1_subset_1(A_10, k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18])).
% 5.75/2.10  tff(c_4752, plain, (![A_348, B_349]: (r1_tarski(A_348, B_349) | ~m1_subset_1(A_348, k1_zfmisc_1(B_349)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.75/2.10  tff(c_4760, plain, (![A_10]: (r1_tarski(A_10, A_10))), inference(resolution, [status(thm)], [c_51, c_4752])).
% 5.75/2.10  tff(c_5037, plain, (![C_379, A_380, B_381]: (m1_subset_1(C_379, k1_zfmisc_1(k2_zfmisc_1(A_380, B_381))) | ~r1_tarski(k2_relat_1(C_379), B_381) | ~r1_tarski(k1_relat_1(C_379), A_380) | ~v1_relat_1(C_379))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.75/2.10  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.75/2.10  tff(c_158, plain, (![A_40, B_41]: (r1_tarski(A_40, B_41) | ~m1_subset_1(A_40, k1_zfmisc_1(B_41)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.75/2.10  tff(c_162, plain, (![A_10]: (r1_tarski(A_10, A_10))), inference(resolution, [status(thm)], [c_51, c_158])).
% 5.75/2.10  tff(c_484, plain, (![C_79, A_80, B_81]: (m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))) | ~r1_tarski(k2_relat_1(C_79), B_81) | ~r1_tarski(k1_relat_1(C_79), A_80) | ~v1_relat_1(C_79))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.75/2.10  tff(c_20, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.75/2.10  tff(c_1289, plain, (![C_149, A_150, B_151]: (r1_tarski(C_149, k2_zfmisc_1(A_150, B_151)) | ~r1_tarski(k2_relat_1(C_149), B_151) | ~r1_tarski(k1_relat_1(C_149), A_150) | ~v1_relat_1(C_149))), inference(resolution, [status(thm)], [c_484, c_20])).
% 5.75/2.10  tff(c_1294, plain, (![C_152, A_153]: (r1_tarski(C_152, k2_zfmisc_1(A_153, k2_relat_1(C_152))) | ~r1_tarski(k1_relat_1(C_152), A_153) | ~v1_relat_1(C_152))), inference(resolution, [status(thm)], [c_162, c_1289])).
% 5.75/2.10  tff(c_22, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.75/2.10  tff(c_280, plain, (![A_60, B_61, C_62]: (k1_relset_1(A_60, B_61, C_62)=k1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.75/2.10  tff(c_295, plain, (![A_60, B_61, A_11]: (k1_relset_1(A_60, B_61, A_11)=k1_relat_1(A_11) | ~r1_tarski(A_11, k2_zfmisc_1(A_60, B_61)))), inference(resolution, [status(thm)], [c_22, c_280])).
% 5.75/2.10  tff(c_1338, plain, (![A_155, C_156]: (k1_relset_1(A_155, k2_relat_1(C_156), C_156)=k1_relat_1(C_156) | ~r1_tarski(k1_relat_1(C_156), A_155) | ~v1_relat_1(C_156))), inference(resolution, [status(thm)], [c_1294, c_295])).
% 5.75/2.10  tff(c_1357, plain, (![C_156]: (k1_relset_1(k1_relat_1(C_156), k2_relat_1(C_156), C_156)=k1_relat_1(C_156) | ~v1_relat_1(C_156))), inference(resolution, [status(thm)], [c_162, c_1338])).
% 5.75/2.10  tff(c_30, plain, (![C_23, A_21, B_22]: (m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~r1_tarski(k2_relat_1(C_23), B_22) | ~r1_tarski(k1_relat_1(C_23), A_21) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.75/2.10  tff(c_678, plain, (![B_100, C_101, A_102]: (k1_xboole_0=B_100 | v1_funct_2(C_101, A_102, B_100) | k1_relset_1(A_102, B_100, C_101)!=A_102 | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_102, B_100))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.75/2.10  tff(c_3883, plain, (![B_302, C_303, A_304]: (k1_xboole_0=B_302 | v1_funct_2(C_303, A_304, B_302) | k1_relset_1(A_304, B_302, C_303)!=A_304 | ~r1_tarski(k2_relat_1(C_303), B_302) | ~r1_tarski(k1_relat_1(C_303), A_304) | ~v1_relat_1(C_303))), inference(resolution, [status(thm)], [c_30, c_678])).
% 5.75/2.10  tff(c_4338, plain, (![C_335, A_336]: (k2_relat_1(C_335)=k1_xboole_0 | v1_funct_2(C_335, A_336, k2_relat_1(C_335)) | k1_relset_1(A_336, k2_relat_1(C_335), C_335)!=A_336 | ~r1_tarski(k1_relat_1(C_335), A_336) | ~v1_relat_1(C_335))), inference(resolution, [status(thm)], [c_162, c_3883])).
% 5.75/2.10  tff(c_46, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.75/2.10  tff(c_44, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.75/2.10  tff(c_50, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44])).
% 5.75/2.10  tff(c_92, plain, (~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_50])).
% 5.75/2.10  tff(c_4350, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4338, c_92])).
% 5.75/2.10  tff(c_4358, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_162, c_4350])).
% 5.75/2.10  tff(c_4359, plain, (k1_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_4358])).
% 5.75/2.10  tff(c_4362, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1357, c_4359])).
% 5.75/2.10  tff(c_4366, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_4362])).
% 5.75/2.10  tff(c_4367, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_4358])).
% 5.75/2.10  tff(c_26, plain, (![C_17, B_15, A_14]: (v1_xboole_0(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(B_15, A_14))) | ~v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.75/2.10  tff(c_1059, plain, (![C_128, B_129, A_130]: (v1_xboole_0(C_128) | ~v1_xboole_0(B_129) | ~r1_tarski(k2_relat_1(C_128), B_129) | ~r1_tarski(k1_relat_1(C_128), A_130) | ~v1_relat_1(C_128))), inference(resolution, [status(thm)], [c_484, c_26])).
% 5.75/2.10  tff(c_1064, plain, (![C_131, A_132]: (v1_xboole_0(C_131) | ~v1_xboole_0(k2_relat_1(C_131)) | ~r1_tarski(k1_relat_1(C_131), A_132) | ~v1_relat_1(C_131))), inference(resolution, [status(thm)], [c_162, c_1059])).
% 5.75/2.10  tff(c_1080, plain, (![C_131]: (v1_xboole_0(C_131) | ~v1_xboole_0(k2_relat_1(C_131)) | ~v1_relat_1(C_131))), inference(resolution, [status(thm)], [c_162, c_1064])).
% 5.75/2.10  tff(c_4394, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4367, c_1080])).
% 5.75/2.10  tff(c_4418, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_6, c_4394])).
% 5.75/2.10  tff(c_99, plain, (![A_36]: (r2_hidden('#skF_2'(A_36), A_36) | k1_xboole_0=A_36)), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.75/2.10  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.75/2.10  tff(c_103, plain, (![A_36]: (~v1_xboole_0(A_36) | k1_xboole_0=A_36)), inference(resolution, [status(thm)], [c_99, c_2])).
% 5.75/2.10  tff(c_4432, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_4418, c_103])).
% 5.75/2.10  tff(c_24, plain, (![A_13]: (v1_xboole_0(k1_relat_1(A_13)) | ~v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.75/2.10  tff(c_104, plain, (![A_37]: (~v1_xboole_0(A_37) | k1_xboole_0=A_37)), inference(resolution, [status(thm)], [c_99, c_2])).
% 5.75/2.10  tff(c_114, plain, (![A_38]: (k1_relat_1(A_38)=k1_xboole_0 | ~v1_xboole_0(A_38))), inference(resolution, [status(thm)], [c_24, c_104])).
% 5.75/2.10  tff(c_122, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_114])).
% 5.75/2.10  tff(c_14, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.75/2.10  tff(c_421, plain, (![A_71, B_72]: (k1_relset_1(A_71, B_72, k2_zfmisc_1(A_71, B_72))=k1_relat_1(k2_zfmisc_1(A_71, B_72)))), inference(resolution, [status(thm)], [c_51, c_280])).
% 5.75/2.10  tff(c_436, plain, (![B_8]: (k1_relat_1(k2_zfmisc_1(k1_xboole_0, B_8))=k1_relset_1(k1_xboole_0, B_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_421])).
% 5.75/2.10  tff(c_442, plain, (![B_8]: (k1_relset_1(k1_xboole_0, B_8, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_122, c_14, c_436])).
% 5.75/2.10  tff(c_36, plain, (![C_26, B_25]: (v1_funct_2(C_26, k1_xboole_0, B_25) | k1_relset_1(k1_xboole_0, B_25, C_26)!=k1_xboole_0 | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_25))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.75/2.10  tff(c_603, plain, (![C_93, B_94]: (v1_funct_2(C_93, k1_xboole_0, B_94) | k1_relset_1(k1_xboole_0, B_94, C_93)!=k1_xboole_0 | ~m1_subset_1(C_93, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_36])).
% 5.75/2.10  tff(c_609, plain, (![B_94]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_94) | k1_relset_1(k1_xboole_0, B_94, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_51, c_603])).
% 5.75/2.10  tff(c_613, plain, (![B_94]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_94))), inference(demodulation, [status(thm), theory('equality')], [c_442, c_609])).
% 5.75/2.10  tff(c_4484, plain, (![B_94]: (v1_funct_2('#skF_3', '#skF_3', B_94))), inference(demodulation, [status(thm), theory('equality')], [c_4432, c_4432, c_613])).
% 5.75/2.10  tff(c_111, plain, (![A_13]: (k1_relat_1(A_13)=k1_xboole_0 | ~v1_xboole_0(A_13))), inference(resolution, [status(thm)], [c_24, c_104])).
% 5.75/2.10  tff(c_4431, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_4418, c_111])).
% 5.75/2.10  tff(c_4517, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4432, c_4431])).
% 5.75/2.10  tff(c_4369, plain, (~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4367, c_92])).
% 5.75/2.10  tff(c_4433, plain, (~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4432, c_4369])).
% 5.75/2.10  tff(c_4662, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4517, c_4433])).
% 5.75/2.10  tff(c_4679, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4484, c_4662])).
% 5.75/2.10  tff(c_4680, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(splitRight, [status(thm)], [c_50])).
% 5.75/2.10  tff(c_5049, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_5037, c_4680])).
% 5.75/2.10  tff(c_5068, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_4760, c_4760, c_5049])).
% 5.75/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.75/2.10  
% 5.75/2.10  Inference rules
% 5.75/2.10  ----------------------
% 5.75/2.10  #Ref     : 0
% 5.75/2.10  #Sup     : 1195
% 5.75/2.10  #Fact    : 0
% 5.75/2.10  #Define  : 0
% 5.75/2.10  #Split   : 4
% 5.75/2.10  #Chain   : 0
% 5.75/2.10  #Close   : 0
% 5.75/2.10  
% 5.75/2.10  Ordering : KBO
% 5.75/2.10  
% 5.75/2.10  Simplification rules
% 5.75/2.10  ----------------------
% 5.75/2.10  #Subsume      : 290
% 5.75/2.10  #Demod        : 1356
% 5.75/2.10  #Tautology    : 547
% 5.75/2.10  #SimpNegUnit  : 0
% 5.75/2.10  #BackRed      : 157
% 5.75/2.10  
% 5.75/2.10  #Partial instantiations: 0
% 5.75/2.10  #Strategies tried      : 1
% 5.75/2.10  
% 5.75/2.10  Timing (in seconds)
% 5.75/2.10  ----------------------
% 5.75/2.11  Preprocessing        : 0.32
% 5.75/2.11  Parsing              : 0.17
% 5.75/2.11  CNF conversion       : 0.02
% 5.75/2.11  Main loop            : 1.01
% 5.75/2.11  Inferencing          : 0.35
% 5.75/2.11  Reduction            : 0.33
% 5.75/2.11  Demodulation         : 0.24
% 5.75/2.11  BG Simplification    : 0.04
% 5.75/2.11  Subsumption          : 0.22
% 5.75/2.11  Abstraction          : 0.06
% 5.75/2.11  MUC search           : 0.00
% 5.75/2.11  Cooper               : 0.00
% 5.75/2.11  Total                : 1.37
% 5.75/2.11  Index Insertion      : 0.00
% 5.75/2.11  Index Deletion       : 0.00
% 5.75/2.11  Index Matching       : 0.00
% 5.75/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
