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
% DateTime   : Thu Dec  3 10:14:28 EST 2020

% Result     : Theorem 5.97s
% Output     : CNFRefutation 5.97s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 193 expanded)
%              Number of leaves         :   44 (  83 expanded)
%              Depth                    :   12
%              Number of atoms          :  146 ( 388 expanded)
%              Number of equality atoms :   58 ( 163 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_137,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_71,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_125,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_82,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_218,plain,(
    ! [C_69,A_70,B_71] :
      ( v1_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_226,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_218])).

tff(c_56,plain,(
    ! [A_24] :
      ( k1_relat_1(A_24) != k1_xboole_0
      | k1_xboole_0 = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_234,plain,
    ( k1_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_226,c_56])).

tff(c_244,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_234])).

tff(c_86,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_713,plain,(
    ! [B_147,A_148] :
      ( k1_tarski(k1_funct_1(B_147,A_148)) = k2_relat_1(B_147)
      | k1_tarski(A_148) != k1_relat_1(B_147)
      | ~ v1_funct_1(B_147)
      | ~ v1_relat_1(B_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_630,plain,(
    ! [A_136,B_137,C_138] :
      ( k2_relset_1(A_136,B_137,C_138) = k2_relat_1(C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_643,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_630])).

tff(c_78,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') != k1_tarski(k1_funct_1('#skF_6','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_692,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_4')) != k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_78])).

tff(c_719,plain,
    ( k1_tarski('#skF_4') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_713,c_692])).

tff(c_744,plain,(
    k1_tarski('#skF_4') != k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_86,c_719])).

tff(c_428,plain,(
    ! [C_110,A_111,B_112] :
      ( v4_relat_1(C_110,A_111)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_441,plain,(
    v4_relat_1('#skF_6',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_82,c_428])).

tff(c_503,plain,(
    ! [B_125,A_126] :
      ( r1_tarski(k1_relat_1(B_125),A_126)
      | ~ v4_relat_1(B_125,A_126)
      | ~ v1_relat_1(B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_34,plain,(
    ! [B_17,A_16] :
      ( k1_tarski(B_17) = A_16
      | k1_xboole_0 = A_16
      | ~ r1_tarski(A_16,k1_tarski(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3286,plain,(
    ! [B_7486,B_7487] :
      ( k1_tarski(B_7486) = k1_relat_1(B_7487)
      | k1_relat_1(B_7487) = k1_xboole_0
      | ~ v4_relat_1(B_7487,k1_tarski(B_7486))
      | ~ v1_relat_1(B_7487) ) ),
    inference(resolution,[status(thm)],[c_503,c_34])).

tff(c_3331,plain,
    ( k1_tarski('#skF_4') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_441,c_3286])).

tff(c_3347,plain,
    ( k1_tarski('#skF_4') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_3331])).

tff(c_3349,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_244,c_744,c_3347])).

tff(c_3350,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_234])).

tff(c_50,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3358,plain,(
    k2_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3350,c_3350,c_50])).

tff(c_3843,plain,(
    ! [A_7616,B_7617,C_7618] :
      ( k2_relset_1(A_7616,B_7617,C_7618) = k2_relat_1(C_7618)
      | ~ m1_subset_1(C_7618,k1_zfmisc_1(k2_zfmisc_1(A_7616,B_7617))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_3850,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_3843])).

tff(c_3857,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3358,c_3850])).

tff(c_3859,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_4')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3857,c_78])).

tff(c_113,plain,(
    ! [A_55] : k2_tarski(A_55,A_55) = k1_tarski(A_55) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12,plain,(
    ! [D_9,A_4] : r2_hidden(D_9,k2_tarski(A_4,D_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_119,plain,(
    ! [A_55] : r2_hidden(A_55,k1_tarski(A_55)) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_12])).

tff(c_80,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_3360,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3350,c_80])).

tff(c_84,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_76,plain,(
    ! [D_45,C_44,A_42,B_43] :
      ( r2_hidden(k1_funct_1(D_45,C_44),k2_relset_1(A_42,B_43,D_45))
      | k1_xboole_0 = B_43
      | ~ r2_hidden(C_44,A_42)
      | ~ m1_subset_1(D_45,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43)))
      | ~ v1_funct_2(D_45,A_42,B_43)
      | ~ v1_funct_1(D_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_5400,plain,(
    ! [D_12456,C_12457,A_12458,B_12459] :
      ( r2_hidden(k1_funct_1(D_12456,C_12457),k2_relset_1(A_12458,B_12459,D_12456))
      | B_12459 = '#skF_6'
      | ~ r2_hidden(C_12457,A_12458)
      | ~ m1_subset_1(D_12456,k1_zfmisc_1(k2_zfmisc_1(A_12458,B_12459)))
      | ~ v1_funct_2(D_12456,A_12458,B_12459)
      | ~ v1_funct_1(D_12456) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3350,c_76])).

tff(c_5410,plain,(
    ! [C_12457] :
      ( r2_hidden(k1_funct_1('#skF_6',C_12457),'#skF_6')
      | '#skF_5' = '#skF_6'
      | ~ r2_hidden(C_12457,k1_tarski('#skF_4'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5')))
      | ~ v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3857,c_5400])).

tff(c_5416,plain,(
    ! [C_12457] :
      ( r2_hidden(k1_funct_1('#skF_6',C_12457),'#skF_6')
      | '#skF_5' = '#skF_6'
      | ~ r2_hidden(C_12457,k1_tarski('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_5410])).

tff(c_5455,plain,(
    ! [C_12679] :
      ( r2_hidden(k1_funct_1('#skF_6',C_12679),'#skF_6')
      | ~ r2_hidden(C_12679,k1_tarski('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3360,c_5416])).

tff(c_3443,plain,(
    ! [A_7553,B_7554] :
      ( m1_subset_1(k1_tarski(A_7553),k1_zfmisc_1(B_7554))
      | ~ r2_hidden(A_7553,B_7554) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_42,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | ~ m1_subset_1(A_20,k1_zfmisc_1(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3453,plain,(
    ! [A_7555,B_7556] :
      ( r1_tarski(k1_tarski(A_7555),B_7556)
      | ~ r2_hidden(A_7555,B_7556) ) ),
    inference(resolution,[status(thm)],[c_3443,c_42])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3357,plain,(
    ! [A_3] : r1_tarski('#skF_6',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3350,c_8])).

tff(c_3407,plain,(
    ! [B_7545,A_7546] :
      ( B_7545 = A_7546
      | ~ r1_tarski(B_7545,A_7546)
      | ~ r1_tarski(A_7546,B_7545) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3412,plain,(
    ! [A_3] :
      ( A_3 = '#skF_6'
      | ~ r1_tarski(A_3,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_3357,c_3407])).

tff(c_3465,plain,(
    ! [A_7555] :
      ( k1_tarski(A_7555) = '#skF_6'
      | ~ r2_hidden(A_7555,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_3453,c_3412])).

tff(c_5574,plain,(
    ! [C_13125] :
      ( k1_tarski(k1_funct_1('#skF_6',C_13125)) = '#skF_6'
      | ~ r2_hidden(C_13125,k1_tarski('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_5455,c_3465])).

tff(c_5582,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_4')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_119,c_5574])).

tff(c_5587,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3859,c_5582])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:33:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.97/2.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.97/2.20  
% 5.97/2.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.97/2.20  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 5.97/2.20  
% 5.97/2.20  %Foreground sorts:
% 5.97/2.20  
% 5.97/2.20  
% 5.97/2.20  %Background operators:
% 5.97/2.20  
% 5.97/2.20  
% 5.97/2.20  %Foreground operators:
% 5.97/2.20  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.97/2.20  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.97/2.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.97/2.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.97/2.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.97/2.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.97/2.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.97/2.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.97/2.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.97/2.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.97/2.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.97/2.20  tff('#skF_5', type, '#skF_5': $i).
% 5.97/2.20  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.97/2.20  tff('#skF_6', type, '#skF_6': $i).
% 5.97/2.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.97/2.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.97/2.20  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.97/2.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.97/2.20  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.97/2.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.97/2.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.97/2.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.97/2.20  tff('#skF_4', type, '#skF_4': $i).
% 5.97/2.20  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.97/2.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.97/2.20  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.97/2.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.97/2.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.97/2.20  
% 5.97/2.21  tff(f_137, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 5.97/2.21  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.97/2.21  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 5.97/2.21  tff(f_87, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 5.97/2.21  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.97/2.21  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.97/2.21  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 5.97/2.21  tff(f_54, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 5.97/2.21  tff(f_71, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 5.97/2.21  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.97/2.21  tff(f_42, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 5.97/2.21  tff(f_125, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 5.97/2.21  tff(f_58, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 5.97/2.21  tff(f_62, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.97/2.21  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.97/2.21  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.97/2.21  tff(c_82, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.97/2.21  tff(c_218, plain, (![C_69, A_70, B_71]: (v1_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.97/2.21  tff(c_226, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_218])).
% 5.97/2.21  tff(c_56, plain, (![A_24]: (k1_relat_1(A_24)!=k1_xboole_0 | k1_xboole_0=A_24 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.97/2.21  tff(c_234, plain, (k1_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_226, c_56])).
% 5.97/2.21  tff(c_244, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_234])).
% 5.97/2.21  tff(c_86, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.97/2.21  tff(c_713, plain, (![B_147, A_148]: (k1_tarski(k1_funct_1(B_147, A_148))=k2_relat_1(B_147) | k1_tarski(A_148)!=k1_relat_1(B_147) | ~v1_funct_1(B_147) | ~v1_relat_1(B_147))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.97/2.21  tff(c_630, plain, (![A_136, B_137, C_138]: (k2_relset_1(A_136, B_137, C_138)=k2_relat_1(C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.97/2.21  tff(c_643, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_630])).
% 5.97/2.21  tff(c_78, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')!=k1_tarski(k1_funct_1('#skF_6', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.97/2.21  tff(c_692, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_4'))!=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_643, c_78])).
% 5.97/2.21  tff(c_719, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_713, c_692])).
% 5.97/2.21  tff(c_744, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_226, c_86, c_719])).
% 5.97/2.21  tff(c_428, plain, (![C_110, A_111, B_112]: (v4_relat_1(C_110, A_111) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.97/2.21  tff(c_441, plain, (v4_relat_1('#skF_6', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_82, c_428])).
% 5.97/2.21  tff(c_503, plain, (![B_125, A_126]: (r1_tarski(k1_relat_1(B_125), A_126) | ~v4_relat_1(B_125, A_126) | ~v1_relat_1(B_125))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.97/2.21  tff(c_34, plain, (![B_17, A_16]: (k1_tarski(B_17)=A_16 | k1_xboole_0=A_16 | ~r1_tarski(A_16, k1_tarski(B_17)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.97/2.21  tff(c_3286, plain, (![B_7486, B_7487]: (k1_tarski(B_7486)=k1_relat_1(B_7487) | k1_relat_1(B_7487)=k1_xboole_0 | ~v4_relat_1(B_7487, k1_tarski(B_7486)) | ~v1_relat_1(B_7487))), inference(resolution, [status(thm)], [c_503, c_34])).
% 5.97/2.21  tff(c_3331, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_441, c_3286])).
% 5.97/2.21  tff(c_3347, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_226, c_3331])).
% 5.97/2.21  tff(c_3349, plain, $false, inference(negUnitSimplification, [status(thm)], [c_244, c_744, c_3347])).
% 5.97/2.21  tff(c_3350, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_234])).
% 5.97/2.21  tff(c_50, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.97/2.21  tff(c_3358, plain, (k2_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3350, c_3350, c_50])).
% 5.97/2.21  tff(c_3843, plain, (![A_7616, B_7617, C_7618]: (k2_relset_1(A_7616, B_7617, C_7618)=k2_relat_1(C_7618) | ~m1_subset_1(C_7618, k1_zfmisc_1(k2_zfmisc_1(A_7616, B_7617))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.97/2.21  tff(c_3850, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_3843])).
% 5.97/2.21  tff(c_3857, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3358, c_3850])).
% 5.97/2.21  tff(c_3859, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_4'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3857, c_78])).
% 5.97/2.21  tff(c_113, plain, (![A_55]: (k2_tarski(A_55, A_55)=k1_tarski(A_55))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.97/2.21  tff(c_12, plain, (![D_9, A_4]: (r2_hidden(D_9, k2_tarski(A_4, D_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.97/2.21  tff(c_119, plain, (![A_55]: (r2_hidden(A_55, k1_tarski(A_55)))), inference(superposition, [status(thm), theory('equality')], [c_113, c_12])).
% 5.97/2.21  tff(c_80, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.97/2.21  tff(c_3360, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3350, c_80])).
% 5.97/2.21  tff(c_84, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.97/2.21  tff(c_76, plain, (![D_45, C_44, A_42, B_43]: (r2_hidden(k1_funct_1(D_45, C_44), k2_relset_1(A_42, B_43, D_45)) | k1_xboole_0=B_43 | ~r2_hidden(C_44, A_42) | ~m1_subset_1(D_45, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))) | ~v1_funct_2(D_45, A_42, B_43) | ~v1_funct_1(D_45))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.97/2.21  tff(c_5400, plain, (![D_12456, C_12457, A_12458, B_12459]: (r2_hidden(k1_funct_1(D_12456, C_12457), k2_relset_1(A_12458, B_12459, D_12456)) | B_12459='#skF_6' | ~r2_hidden(C_12457, A_12458) | ~m1_subset_1(D_12456, k1_zfmisc_1(k2_zfmisc_1(A_12458, B_12459))) | ~v1_funct_2(D_12456, A_12458, B_12459) | ~v1_funct_1(D_12456))), inference(demodulation, [status(thm), theory('equality')], [c_3350, c_76])).
% 5.97/2.21  tff(c_5410, plain, (![C_12457]: (r2_hidden(k1_funct_1('#skF_6', C_12457), '#skF_6') | '#skF_5'='#skF_6' | ~r2_hidden(C_12457, k1_tarski('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5'))) | ~v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5') | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3857, c_5400])).
% 5.97/2.21  tff(c_5416, plain, (![C_12457]: (r2_hidden(k1_funct_1('#skF_6', C_12457), '#skF_6') | '#skF_5'='#skF_6' | ~r2_hidden(C_12457, k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_5410])).
% 5.97/2.21  tff(c_5455, plain, (![C_12679]: (r2_hidden(k1_funct_1('#skF_6', C_12679), '#skF_6') | ~r2_hidden(C_12679, k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_3360, c_5416])).
% 5.97/2.21  tff(c_3443, plain, (![A_7553, B_7554]: (m1_subset_1(k1_tarski(A_7553), k1_zfmisc_1(B_7554)) | ~r2_hidden(A_7553, B_7554))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.97/2.21  tff(c_42, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | ~m1_subset_1(A_20, k1_zfmisc_1(B_21)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.97/2.21  tff(c_3453, plain, (![A_7555, B_7556]: (r1_tarski(k1_tarski(A_7555), B_7556) | ~r2_hidden(A_7555, B_7556))), inference(resolution, [status(thm)], [c_3443, c_42])).
% 5.97/2.21  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.97/2.21  tff(c_3357, plain, (![A_3]: (r1_tarski('#skF_6', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_3350, c_8])).
% 5.97/2.21  tff(c_3407, plain, (![B_7545, A_7546]: (B_7545=A_7546 | ~r1_tarski(B_7545, A_7546) | ~r1_tarski(A_7546, B_7545))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.97/2.21  tff(c_3412, plain, (![A_3]: (A_3='#skF_6' | ~r1_tarski(A_3, '#skF_6'))), inference(resolution, [status(thm)], [c_3357, c_3407])).
% 5.97/2.21  tff(c_3465, plain, (![A_7555]: (k1_tarski(A_7555)='#skF_6' | ~r2_hidden(A_7555, '#skF_6'))), inference(resolution, [status(thm)], [c_3453, c_3412])).
% 5.97/2.21  tff(c_5574, plain, (![C_13125]: (k1_tarski(k1_funct_1('#skF_6', C_13125))='#skF_6' | ~r2_hidden(C_13125, k1_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_5455, c_3465])).
% 5.97/2.21  tff(c_5582, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_4'))='#skF_6'), inference(resolution, [status(thm)], [c_119, c_5574])).
% 5.97/2.21  tff(c_5587, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3859, c_5582])).
% 5.97/2.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.97/2.21  
% 5.97/2.21  Inference rules
% 5.97/2.21  ----------------------
% 5.97/2.21  #Ref     : 4
% 5.97/2.21  #Sup     : 873
% 5.97/2.21  #Fact    : 8
% 5.97/2.21  #Define  : 0
% 5.97/2.21  #Split   : 6
% 5.97/2.21  #Chain   : 0
% 5.97/2.21  #Close   : 0
% 5.97/2.21  
% 5.97/2.21  Ordering : KBO
% 5.97/2.21  
% 5.97/2.21  Simplification rules
% 5.97/2.21  ----------------------
% 5.97/2.21  #Subsume      : 176
% 5.97/2.21  #Demod        : 313
% 5.97/2.21  #Tautology    : 252
% 5.97/2.21  #SimpNegUnit  : 16
% 5.97/2.21  #BackRed      : 19
% 5.97/2.21  
% 5.97/2.21  #Partial instantiations: 8007
% 5.97/2.22  #Strategies tried      : 1
% 5.97/2.22  
% 5.97/2.22  Timing (in seconds)
% 5.97/2.22  ----------------------
% 5.97/2.22  Preprocessing        : 0.34
% 5.97/2.22  Parsing              : 0.17
% 5.97/2.22  CNF conversion       : 0.02
% 5.97/2.22  Main loop            : 1.06
% 5.97/2.22  Inferencing          : 0.50
% 5.97/2.22  Reduction            : 0.28
% 5.97/2.22  Demodulation         : 0.19
% 5.97/2.22  BG Simplification    : 0.04
% 5.97/2.22  Subsumption          : 0.17
% 5.97/2.22  Abstraction          : 0.04
% 5.97/2.22  MUC search           : 0.00
% 5.97/2.22  Cooper               : 0.00
% 5.97/2.22  Total                : 1.43
% 5.97/2.22  Index Insertion      : 0.00
% 5.97/2.22  Index Deletion       : 0.00
% 5.97/2.22  Index Matching       : 0.00
% 5.97/2.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
