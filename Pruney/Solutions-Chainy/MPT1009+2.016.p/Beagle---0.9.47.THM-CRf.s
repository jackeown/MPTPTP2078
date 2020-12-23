%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:44 EST 2020

% Result     : Theorem 3.88s
% Output     : CNFRefutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 290 expanded)
%              Number of leaves         :   39 ( 112 expanded)
%              Depth                    :   14
%              Number of atoms          :  140 ( 600 expanded)
%              Number of equality atoms :   54 ( 197 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_101,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_145,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_157,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_145])).

tff(c_36,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k9_relat_1(B_20,A_19),k2_relat_1(B_20))
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_40,plain,(
    ! [A_21] :
      ( k1_relat_1(A_21) != k1_xboole_0
      | k1_xboole_0 = A_21
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_165,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_157,c_40])).

tff(c_167,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_165])).

tff(c_455,plain,(
    ! [A_106,B_107,C_108,D_109] :
      ( k7_relset_1(A_106,B_107,C_108,D_109) = k9_relat_1(C_108,D_109)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_465,plain,(
    ! [D_109] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_109) = k9_relat_1('#skF_4',D_109) ),
    inference(resolution,[status(thm)],[c_60,c_455])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_402,plain,(
    ! [B_98,A_99] :
      ( k1_tarski(k1_funct_1(B_98,A_99)) = k2_relat_1(B_98)
      | k1_tarski(A_99) != k1_relat_1(B_98)
      | ~ v1_funct_1(B_98)
      | ~ v1_relat_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_56,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_414,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_56])).

tff(c_422,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_64,c_414])).

tff(c_633,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_422])).

tff(c_634,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_633])).

tff(c_380,plain,(
    ! [C_91,A_92,B_93] :
      ( v4_relat_1(C_91,A_92)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_394,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_60,c_380])).

tff(c_32,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(B_16),A_15)
      | ~ v4_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_352,plain,(
    ! [B_86,A_87] :
      ( k1_tarski(B_86) = A_87
      | k1_xboole_0 = A_87
      | ~ r1_tarski(A_87,k1_tarski(B_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1088,plain,(
    ! [B_180,B_181] :
      ( k1_tarski(B_180) = k1_relat_1(B_181)
      | k1_relat_1(B_181) = k1_xboole_0
      | ~ v4_relat_1(B_181,k1_tarski(B_180))
      | ~ v1_relat_1(B_181) ) ),
    inference(resolution,[status(thm)],[c_32,c_352])).

tff(c_1146,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_394,c_1088])).

tff(c_1185,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_1146])).

tff(c_1187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_634,c_1185])).

tff(c_1188,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_633])).

tff(c_1228,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_1188])).

tff(c_1232,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_1228])).

tff(c_1233,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_22,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1239,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1233,c_1233,c_22])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1506,plain,(
    ! [C_224,A_225,B_226] :
      ( v4_relat_1(C_224,A_225)
      | ~ m1_subset_1(C_224,k1_zfmisc_1(k2_zfmisc_1(A_225,B_226))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1547,plain,(
    ! [A_236,A_237,B_238] :
      ( v4_relat_1(A_236,A_237)
      | ~ r1_tarski(A_236,k2_zfmisc_1(A_237,B_238)) ) ),
    inference(resolution,[status(thm)],[c_28,c_1506])).

tff(c_1564,plain,(
    ! [A_239,B_240] : v4_relat_1(k2_zfmisc_1(A_239,B_240),A_239) ),
    inference(resolution,[status(thm)],[c_6,c_1547])).

tff(c_1567,plain,(
    ! [A_11] : v4_relat_1('#skF_4',A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_1239,c_1564])).

tff(c_1234,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_1249,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1233,c_1234])).

tff(c_1572,plain,(
    ! [B_241,A_242] :
      ( r1_tarski(k1_relat_1(B_241),A_242)
      | ~ v4_relat_1(B_241,A_242)
      | ~ v1_relat_1(B_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1600,plain,(
    ! [A_242] :
      ( r1_tarski('#skF_4',A_242)
      | ~ v4_relat_1('#skF_4',A_242)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1249,c_1572])).

tff(c_1609,plain,(
    ! [A_242] :
      ( r1_tarski('#skF_4',A_242)
      | ~ v4_relat_1('#skF_4',A_242) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_1600])).

tff(c_1615,plain,(
    ! [A_242] : r1_tarski('#skF_4',A_242) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1567,c_1609])).

tff(c_44,plain,(
    ! [A_22] :
      ( k2_relat_1(A_22) = k1_xboole_0
      | k1_relat_1(A_22) != k1_xboole_0
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1378,plain,(
    ! [A_198] :
      ( k2_relat_1(A_198) = '#skF_4'
      | k1_relat_1(A_198) != '#skF_4'
      | ~ v1_relat_1(A_198) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1233,c_1233,c_44])).

tff(c_1381,plain,
    ( k2_relat_1('#skF_4') = '#skF_4'
    | k1_relat_1('#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_157,c_1378])).

tff(c_1387,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1249,c_1381])).

tff(c_1393,plain,(
    ! [B_199,A_200] :
      ( r1_tarski(k9_relat_1(B_199,A_200),k2_relat_1(B_199))
      | ~ v1_relat_1(B_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1398,plain,(
    ! [A_200] :
      ( r1_tarski(k9_relat_1('#skF_4',A_200),'#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1387,c_1393])).

tff(c_1402,plain,(
    ! [A_201] : r1_tarski(k9_relat_1('#skF_4',A_201),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_1398])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1408,plain,(
    ! [A_201] :
      ( k9_relat_1('#skF_4',A_201) = '#skF_4'
      | ~ r1_tarski('#skF_4',k9_relat_1('#skF_4',A_201)) ) ),
    inference(resolution,[status(thm)],[c_1402,c_2])).

tff(c_1617,plain,(
    ! [A_201] : k9_relat_1('#skF_4',A_201) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1615,c_1408])).

tff(c_1896,plain,(
    ! [A_265,B_266,C_267,D_268] :
      ( k7_relset_1(A_265,B_266,C_267,D_268) = k9_relat_1(C_267,D_268)
      | ~ m1_subset_1(C_267,k1_zfmisc_1(k2_zfmisc_1(A_265,B_266))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1902,plain,(
    ! [D_268] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_268) = k9_relat_1('#skF_4',D_268) ),
    inference(resolution,[status(thm)],[c_60,c_1896])).

tff(c_1907,plain,(
    ! [D_268] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_268) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1617,c_1902])).

tff(c_1909,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1907,c_56])).

tff(c_1912,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1615,c_1909])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:55:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.88/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.72  
% 3.88/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.72  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.88/1.72  
% 3.88/1.72  %Foreground sorts:
% 3.88/1.72  
% 3.88/1.72  
% 3.88/1.72  %Background operators:
% 3.88/1.72  
% 3.88/1.72  
% 3.88/1.72  %Foreground operators:
% 3.88/1.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.88/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.88/1.72  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.88/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.88/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.88/1.72  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.88/1.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.88/1.72  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.88/1.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.88/1.72  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.88/1.72  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.88/1.72  tff('#skF_2', type, '#skF_2': $i).
% 3.88/1.72  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.88/1.72  tff('#skF_3', type, '#skF_3': $i).
% 3.88/1.72  tff('#skF_1', type, '#skF_1': $i).
% 3.88/1.72  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.88/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.88/1.72  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.88/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.88/1.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.88/1.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.88/1.72  tff('#skF_4', type, '#skF_4': $i).
% 3.88/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.88/1.72  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.88/1.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.88/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.88/1.72  
% 3.88/1.74  tff(f_113, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 3.88/1.74  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.88/1.74  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 3.88/1.74  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.88/1.74  tff(f_101, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.88/1.74  tff(f_87, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.88/1.74  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.88/1.74  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.88/1.74  tff(f_43, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.88/1.74  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.88/1.74  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.88/1.74  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.88/1.74  tff(f_79, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 3.88/1.74  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.88/1.74  tff(c_145, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.88/1.74  tff(c_157, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_145])).
% 3.88/1.74  tff(c_36, plain, (![B_20, A_19]: (r1_tarski(k9_relat_1(B_20, A_19), k2_relat_1(B_20)) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.88/1.74  tff(c_40, plain, (![A_21]: (k1_relat_1(A_21)!=k1_xboole_0 | k1_xboole_0=A_21 | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.88/1.74  tff(c_165, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_157, c_40])).
% 3.88/1.74  tff(c_167, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_165])).
% 3.88/1.74  tff(c_455, plain, (![A_106, B_107, C_108, D_109]: (k7_relset_1(A_106, B_107, C_108, D_109)=k9_relat_1(C_108, D_109) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.88/1.74  tff(c_465, plain, (![D_109]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_109)=k9_relat_1('#skF_4', D_109))), inference(resolution, [status(thm)], [c_60, c_455])).
% 3.88/1.74  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.88/1.74  tff(c_402, plain, (![B_98, A_99]: (k1_tarski(k1_funct_1(B_98, A_99))=k2_relat_1(B_98) | k1_tarski(A_99)!=k1_relat_1(B_98) | ~v1_funct_1(B_98) | ~v1_relat_1(B_98))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.88/1.74  tff(c_56, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.88/1.74  tff(c_414, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_402, c_56])).
% 3.88/1.74  tff(c_422, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_157, c_64, c_414])).
% 3.88/1.74  tff(c_633, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_465, c_422])).
% 3.88/1.74  tff(c_634, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_633])).
% 3.88/1.74  tff(c_380, plain, (![C_91, A_92, B_93]: (v4_relat_1(C_91, A_92) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.88/1.74  tff(c_394, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_60, c_380])).
% 3.88/1.74  tff(c_32, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(B_16), A_15) | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.88/1.74  tff(c_352, plain, (![B_86, A_87]: (k1_tarski(B_86)=A_87 | k1_xboole_0=A_87 | ~r1_tarski(A_87, k1_tarski(B_86)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.88/1.74  tff(c_1088, plain, (![B_180, B_181]: (k1_tarski(B_180)=k1_relat_1(B_181) | k1_relat_1(B_181)=k1_xboole_0 | ~v4_relat_1(B_181, k1_tarski(B_180)) | ~v1_relat_1(B_181))), inference(resolution, [status(thm)], [c_32, c_352])).
% 3.88/1.74  tff(c_1146, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_394, c_1088])).
% 3.88/1.74  tff(c_1185, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_157, c_1146])).
% 3.88/1.74  tff(c_1187, plain, $false, inference(negUnitSimplification, [status(thm)], [c_167, c_634, c_1185])).
% 3.88/1.74  tff(c_1188, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_633])).
% 3.88/1.74  tff(c_1228, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_1188])).
% 3.88/1.74  tff(c_1232, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_157, c_1228])).
% 3.88/1.74  tff(c_1233, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_165])).
% 3.88/1.74  tff(c_22, plain, (![A_11]: (k2_zfmisc_1(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.88/1.74  tff(c_1239, plain, (![A_11]: (k2_zfmisc_1(A_11, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1233, c_1233, c_22])).
% 3.88/1.74  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.88/1.74  tff(c_28, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.88/1.74  tff(c_1506, plain, (![C_224, A_225, B_226]: (v4_relat_1(C_224, A_225) | ~m1_subset_1(C_224, k1_zfmisc_1(k2_zfmisc_1(A_225, B_226))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.88/1.74  tff(c_1547, plain, (![A_236, A_237, B_238]: (v4_relat_1(A_236, A_237) | ~r1_tarski(A_236, k2_zfmisc_1(A_237, B_238)))), inference(resolution, [status(thm)], [c_28, c_1506])).
% 3.88/1.74  tff(c_1564, plain, (![A_239, B_240]: (v4_relat_1(k2_zfmisc_1(A_239, B_240), A_239))), inference(resolution, [status(thm)], [c_6, c_1547])).
% 3.88/1.74  tff(c_1567, plain, (![A_11]: (v4_relat_1('#skF_4', A_11))), inference(superposition, [status(thm), theory('equality')], [c_1239, c_1564])).
% 3.88/1.74  tff(c_1234, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_165])).
% 3.88/1.74  tff(c_1249, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1233, c_1234])).
% 3.88/1.74  tff(c_1572, plain, (![B_241, A_242]: (r1_tarski(k1_relat_1(B_241), A_242) | ~v4_relat_1(B_241, A_242) | ~v1_relat_1(B_241))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.88/1.74  tff(c_1600, plain, (![A_242]: (r1_tarski('#skF_4', A_242) | ~v4_relat_1('#skF_4', A_242) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1249, c_1572])).
% 3.88/1.74  tff(c_1609, plain, (![A_242]: (r1_tarski('#skF_4', A_242) | ~v4_relat_1('#skF_4', A_242))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_1600])).
% 3.88/1.74  tff(c_1615, plain, (![A_242]: (r1_tarski('#skF_4', A_242))), inference(demodulation, [status(thm), theory('equality')], [c_1567, c_1609])).
% 3.88/1.74  tff(c_44, plain, (![A_22]: (k2_relat_1(A_22)=k1_xboole_0 | k1_relat_1(A_22)!=k1_xboole_0 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.88/1.74  tff(c_1378, plain, (![A_198]: (k2_relat_1(A_198)='#skF_4' | k1_relat_1(A_198)!='#skF_4' | ~v1_relat_1(A_198))), inference(demodulation, [status(thm), theory('equality')], [c_1233, c_1233, c_44])).
% 3.88/1.74  tff(c_1381, plain, (k2_relat_1('#skF_4')='#skF_4' | k1_relat_1('#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_157, c_1378])).
% 3.88/1.74  tff(c_1387, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1249, c_1381])).
% 3.88/1.74  tff(c_1393, plain, (![B_199, A_200]: (r1_tarski(k9_relat_1(B_199, A_200), k2_relat_1(B_199)) | ~v1_relat_1(B_199))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.88/1.74  tff(c_1398, plain, (![A_200]: (r1_tarski(k9_relat_1('#skF_4', A_200), '#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1387, c_1393])).
% 3.88/1.74  tff(c_1402, plain, (![A_201]: (r1_tarski(k9_relat_1('#skF_4', A_201), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_1398])).
% 3.88/1.74  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.88/1.74  tff(c_1408, plain, (![A_201]: (k9_relat_1('#skF_4', A_201)='#skF_4' | ~r1_tarski('#skF_4', k9_relat_1('#skF_4', A_201)))), inference(resolution, [status(thm)], [c_1402, c_2])).
% 3.88/1.74  tff(c_1617, plain, (![A_201]: (k9_relat_1('#skF_4', A_201)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1615, c_1408])).
% 3.88/1.74  tff(c_1896, plain, (![A_265, B_266, C_267, D_268]: (k7_relset_1(A_265, B_266, C_267, D_268)=k9_relat_1(C_267, D_268) | ~m1_subset_1(C_267, k1_zfmisc_1(k2_zfmisc_1(A_265, B_266))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.88/1.74  tff(c_1902, plain, (![D_268]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_268)=k9_relat_1('#skF_4', D_268))), inference(resolution, [status(thm)], [c_60, c_1896])).
% 3.88/1.74  tff(c_1907, plain, (![D_268]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_268)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1617, c_1902])).
% 3.88/1.74  tff(c_1909, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1907, c_56])).
% 3.88/1.74  tff(c_1912, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1615, c_1909])).
% 3.88/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.74  
% 3.88/1.74  Inference rules
% 3.88/1.74  ----------------------
% 3.88/1.74  #Ref     : 0
% 3.88/1.74  #Sup     : 380
% 3.88/1.74  #Fact    : 0
% 3.88/1.74  #Define  : 0
% 3.88/1.74  #Split   : 7
% 3.88/1.74  #Chain   : 0
% 3.88/1.74  #Close   : 0
% 3.88/1.74  
% 3.88/1.74  Ordering : KBO
% 3.88/1.74  
% 3.88/1.74  Simplification rules
% 3.88/1.74  ----------------------
% 3.88/1.74  #Subsume      : 50
% 3.88/1.74  #Demod        : 221
% 3.88/1.74  #Tautology    : 128
% 3.88/1.74  #SimpNegUnit  : 21
% 3.88/1.74  #BackRed      : 18
% 3.88/1.74  
% 3.88/1.74  #Partial instantiations: 0
% 3.88/1.74  #Strategies tried      : 1
% 3.88/1.74  
% 3.88/1.74  Timing (in seconds)
% 3.88/1.74  ----------------------
% 3.88/1.74  Preprocessing        : 0.36
% 3.88/1.74  Parsing              : 0.19
% 3.88/1.74  CNF conversion       : 0.02
% 3.88/1.74  Main loop            : 0.56
% 3.88/1.74  Inferencing          : 0.20
% 3.88/1.74  Reduction            : 0.19
% 3.88/1.74  Demodulation         : 0.13
% 3.88/1.74  BG Simplification    : 0.03
% 3.88/1.74  Subsumption          : 0.10
% 3.88/1.74  Abstraction          : 0.02
% 3.88/1.74  MUC search           : 0.00
% 3.88/1.75  Cooper               : 0.00
% 3.88/1.75  Total                : 0.96
% 3.88/1.75  Index Insertion      : 0.00
% 3.88/1.75  Index Deletion       : 0.00
% 3.88/1.75  Index Matching       : 0.00
% 3.88/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
