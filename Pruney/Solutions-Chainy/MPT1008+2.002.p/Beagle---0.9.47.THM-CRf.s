%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:26 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 311 expanded)
%              Number of leaves         :   41 ( 119 expanded)
%              Depth                    :   14
%              Number of atoms          :  158 ( 653 expanded)
%              Number of equality atoms :   70 ( 288 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_128,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_65,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_36,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_50,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_116,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_90,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_111,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_119,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_111])).

tff(c_34,plain,(
    ! [A_18] :
      ( k1_relat_1(A_18) != k1_xboole_0
      | k1_xboole_0 = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_128,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_119,c_34])).

tff(c_156,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_264,plain,(
    ! [B_82,A_83] :
      ( k1_tarski(k1_funct_1(B_82,A_83)) = k2_relat_1(B_82)
      | k1_tarski(A_83) != k1_relat_1(B_82)
      | ~ v1_funct_1(B_82)
      | ~ v1_relat_1(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_241,plain,(
    ! [A_77,B_78,C_79] :
      ( k2_relset_1(A_77,B_78,C_79) = k2_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_249,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_241])).

tff(c_52,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') != k1_tarski(k1_funct_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_259,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_52])).

tff(c_270,plain,
    ( k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_259])).

tff(c_286,plain,(
    k1_tarski('#skF_2') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_60,c_270])).

tff(c_168,plain,(
    ! [C_59,A_60,B_61] :
      ( v4_relat_1(C_59,A_60)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_176,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_56,c_168])).

tff(c_179,plain,(
    ! [B_63,A_64] :
      ( r1_tarski(k1_relat_1(B_63),A_64)
      | ~ v4_relat_1(B_63,A_64)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( k1_tarski(B_11) = A_10
      | k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_tarski(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_288,plain,(
    ! [B_84,B_85] :
      ( k1_tarski(B_84) = k1_relat_1(B_85)
      | k1_relat_1(B_85) = k1_xboole_0
      | ~ v4_relat_1(B_85,k1_tarski(B_84))
      | ~ v1_relat_1(B_85) ) ),
    inference(resolution,[status(thm)],[c_179,c_14])).

tff(c_294,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_176,c_288])).

tff(c_301,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_294])).

tff(c_303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_286,c_301])).

tff(c_304,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_28,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_316,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_304,c_28])).

tff(c_32,plain,(
    ! [A_18] :
      ( k2_relat_1(A_18) != k1_xboole_0
      | k1_xboole_0 = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_127,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_119,c_32])).

tff(c_143,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_307,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_143])).

tff(c_348,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_307])).

tff(c_349,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_6,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_358,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_6])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_360,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_349,c_30])).

tff(c_350,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_375,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_350])).

tff(c_38,plain,(
    ! [B_21,A_20] :
      ( k1_tarski(k1_funct_1(B_21,A_20)) = k2_relat_1(B_21)
      | k1_tarski(A_20) != k1_relat_1(B_21)
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_20,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_356,plain,(
    ! [A_12] : m1_subset_1('#skF_4',k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_20])).

tff(c_514,plain,(
    ! [A_119,B_120,C_121] :
      ( k2_relset_1(A_119,B_120,C_121) = k2_relat_1(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_518,plain,(
    ! [A_119,B_120] : k2_relset_1(A_119,B_120,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_356,c_514])).

tff(c_520,plain,(
    ! [A_119,B_120] : k2_relset_1(A_119,B_120,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_375,c_518])).

tff(c_521,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_520,c_52])).

tff(c_549,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_521])).

tff(c_551,plain,(
    k1_tarski('#skF_2') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_60,c_360,c_375,c_549])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_362,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_54])).

tff(c_58,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_355,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | A_1 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_4])).

tff(c_50,plain,(
    ! [D_36,C_35,A_33,B_34] :
      ( r2_hidden(k1_funct_1(D_36,C_35),k2_relset_1(A_33,B_34,D_36))
      | k1_xboole_0 = B_34
      | ~ r2_hidden(C_35,A_33)
      | ~ m1_subset_1(D_36,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34)))
      | ~ v1_funct_2(D_36,A_33,B_34)
      | ~ v1_funct_1(D_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_564,plain,(
    ! [D_128,C_129,A_130,B_131] :
      ( r2_hidden(k1_funct_1(D_128,C_129),k2_relset_1(A_130,B_131,D_128))
      | B_131 = '#skF_4'
      | ~ r2_hidden(C_129,A_130)
      | ~ m1_subset_1(D_128,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131)))
      | ~ v1_funct_2(D_128,A_130,B_131)
      | ~ v1_funct_1(D_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_50])).

tff(c_570,plain,(
    ! [C_129,B_120,A_119] :
      ( r2_hidden(k1_funct_1('#skF_4',C_129),'#skF_4')
      | B_120 = '#skF_4'
      | ~ r2_hidden(C_129,A_119)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_119,B_120)))
      | ~ v1_funct_2('#skF_4',A_119,B_120)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_520,c_564])).

tff(c_574,plain,(
    ! [C_132,B_133,A_134] :
      ( r2_hidden(k1_funct_1('#skF_4',C_132),'#skF_4')
      | B_133 = '#skF_4'
      | ~ r2_hidden(C_132,A_134)
      | ~ v1_funct_2('#skF_4',A_134,B_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_356,c_570])).

tff(c_581,plain,(
    ! [A_135,B_136] :
      ( r2_hidden(k1_funct_1('#skF_4','#skF_1'(A_135)),'#skF_4')
      | B_136 = '#skF_4'
      | ~ v1_funct_2('#skF_4',A_135,B_136)
      | A_135 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_355,c_574])).

tff(c_583,plain,
    ( r2_hidden(k1_funct_1('#skF_4','#skF_1'(k1_tarski('#skF_2'))),'#skF_4')
    | '#skF_3' = '#skF_4'
    | k1_tarski('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_58,c_581])).

tff(c_586,plain,(
    r2_hidden(k1_funct_1('#skF_4','#skF_1'(k1_tarski('#skF_2'))),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_551,c_362,c_583])).

tff(c_40,plain,(
    ! [B_23,A_22] :
      ( ~ r1_tarski(B_23,A_22)
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_593,plain,(
    ~ r1_tarski('#skF_4',k1_funct_1('#skF_4','#skF_1'(k1_tarski('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_586,c_40])).

tff(c_599,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_593])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:03:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.40  
% 2.62/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.40  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.62/1.40  
% 2.62/1.40  %Foreground sorts:
% 2.62/1.40  
% 2.62/1.40  
% 2.62/1.40  %Background operators:
% 2.62/1.40  
% 2.62/1.40  
% 2.62/1.40  %Foreground operators:
% 2.62/1.40  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.62/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.62/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.62/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.62/1.40  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.62/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.62/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.62/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.62/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.62/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.62/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.62/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.62/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.62/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.62/1.40  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.62/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.62/1.40  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.62/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.62/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.62/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.62/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.40  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.62/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.62/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.62/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.62/1.40  
% 2.62/1.42  tff(f_128, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 2.62/1.42  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.62/1.42  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.62/1.42  tff(f_85, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 2.62/1.42  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.62/1.42  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.62/1.42  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.62/1.42  tff(f_48, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.62/1.42  tff(f_65, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.62/1.42  tff(f_36, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.62/1.42  tff(f_50, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.62/1.42  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.62/1.42  tff(f_116, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 2.62/1.42  tff(f_90, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.62/1.42  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.62/1.42  tff(c_111, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.62/1.42  tff(c_119, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_111])).
% 2.62/1.42  tff(c_34, plain, (![A_18]: (k1_relat_1(A_18)!=k1_xboole_0 | k1_xboole_0=A_18 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.62/1.42  tff(c_128, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_119, c_34])).
% 2.62/1.42  tff(c_156, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_128])).
% 2.62/1.42  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.62/1.42  tff(c_264, plain, (![B_82, A_83]: (k1_tarski(k1_funct_1(B_82, A_83))=k2_relat_1(B_82) | k1_tarski(A_83)!=k1_relat_1(B_82) | ~v1_funct_1(B_82) | ~v1_relat_1(B_82))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.62/1.42  tff(c_241, plain, (![A_77, B_78, C_79]: (k2_relset_1(A_77, B_78, C_79)=k2_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.62/1.42  tff(c_249, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_241])).
% 2.62/1.42  tff(c_52, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')!=k1_tarski(k1_funct_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.62/1.42  tff(c_259, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_249, c_52])).
% 2.62/1.42  tff(c_270, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_264, c_259])).
% 2.62/1.42  tff(c_286, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_119, c_60, c_270])).
% 2.62/1.42  tff(c_168, plain, (![C_59, A_60, B_61]: (v4_relat_1(C_59, A_60) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.62/1.42  tff(c_176, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_56, c_168])).
% 2.62/1.42  tff(c_179, plain, (![B_63, A_64]: (r1_tarski(k1_relat_1(B_63), A_64) | ~v4_relat_1(B_63, A_64) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.62/1.42  tff(c_14, plain, (![B_11, A_10]: (k1_tarski(B_11)=A_10 | k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_tarski(B_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.62/1.42  tff(c_288, plain, (![B_84, B_85]: (k1_tarski(B_84)=k1_relat_1(B_85) | k1_relat_1(B_85)=k1_xboole_0 | ~v4_relat_1(B_85, k1_tarski(B_84)) | ~v1_relat_1(B_85))), inference(resolution, [status(thm)], [c_179, c_14])).
% 2.62/1.42  tff(c_294, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_176, c_288])).
% 2.62/1.42  tff(c_301, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_119, c_294])).
% 2.62/1.42  tff(c_303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_156, c_286, c_301])).
% 2.62/1.42  tff(c_304, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_128])).
% 2.62/1.42  tff(c_28, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.62/1.42  tff(c_316, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_304, c_304, c_28])).
% 2.62/1.42  tff(c_32, plain, (![A_18]: (k2_relat_1(A_18)!=k1_xboole_0 | k1_xboole_0=A_18 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.62/1.42  tff(c_127, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_119, c_32])).
% 2.62/1.42  tff(c_143, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_127])).
% 2.62/1.42  tff(c_307, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_304, c_143])).
% 2.62/1.42  tff(c_348, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_316, c_307])).
% 2.62/1.42  tff(c_349, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_127])).
% 2.62/1.42  tff(c_6, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.62/1.42  tff(c_358, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_349, c_6])).
% 2.62/1.42  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.62/1.42  tff(c_360, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_349, c_349, c_30])).
% 2.62/1.42  tff(c_350, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_127])).
% 2.62/1.42  tff(c_375, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_349, c_350])).
% 2.62/1.42  tff(c_38, plain, (![B_21, A_20]: (k1_tarski(k1_funct_1(B_21, A_20))=k2_relat_1(B_21) | k1_tarski(A_20)!=k1_relat_1(B_21) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.62/1.42  tff(c_20, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.62/1.42  tff(c_356, plain, (![A_12]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_349, c_20])).
% 2.62/1.42  tff(c_514, plain, (![A_119, B_120, C_121]: (k2_relset_1(A_119, B_120, C_121)=k2_relat_1(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.62/1.42  tff(c_518, plain, (![A_119, B_120]: (k2_relset_1(A_119, B_120, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_356, c_514])).
% 2.62/1.42  tff(c_520, plain, (![A_119, B_120]: (k2_relset_1(A_119, B_120, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_375, c_518])).
% 2.62/1.42  tff(c_521, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_520, c_52])).
% 2.62/1.42  tff(c_549, plain, (k2_relat_1('#skF_4')!='#skF_4' | k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_38, c_521])).
% 2.62/1.42  tff(c_551, plain, (k1_tarski('#skF_2')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_119, c_60, c_360, c_375, c_549])).
% 2.62/1.42  tff(c_54, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.62/1.42  tff(c_362, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_349, c_54])).
% 2.62/1.42  tff(c_58, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.62/1.42  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.62/1.42  tff(c_355, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | A_1='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_349, c_4])).
% 2.62/1.42  tff(c_50, plain, (![D_36, C_35, A_33, B_34]: (r2_hidden(k1_funct_1(D_36, C_35), k2_relset_1(A_33, B_34, D_36)) | k1_xboole_0=B_34 | ~r2_hidden(C_35, A_33) | ~m1_subset_1(D_36, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))) | ~v1_funct_2(D_36, A_33, B_34) | ~v1_funct_1(D_36))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.62/1.42  tff(c_564, plain, (![D_128, C_129, A_130, B_131]: (r2_hidden(k1_funct_1(D_128, C_129), k2_relset_1(A_130, B_131, D_128)) | B_131='#skF_4' | ~r2_hidden(C_129, A_130) | ~m1_subset_1(D_128, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))) | ~v1_funct_2(D_128, A_130, B_131) | ~v1_funct_1(D_128))), inference(demodulation, [status(thm), theory('equality')], [c_349, c_50])).
% 2.62/1.42  tff(c_570, plain, (![C_129, B_120, A_119]: (r2_hidden(k1_funct_1('#skF_4', C_129), '#skF_4') | B_120='#skF_4' | ~r2_hidden(C_129, A_119) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))) | ~v1_funct_2('#skF_4', A_119, B_120) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_520, c_564])).
% 2.62/1.42  tff(c_574, plain, (![C_132, B_133, A_134]: (r2_hidden(k1_funct_1('#skF_4', C_132), '#skF_4') | B_133='#skF_4' | ~r2_hidden(C_132, A_134) | ~v1_funct_2('#skF_4', A_134, B_133))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_356, c_570])).
% 2.62/1.42  tff(c_581, plain, (![A_135, B_136]: (r2_hidden(k1_funct_1('#skF_4', '#skF_1'(A_135)), '#skF_4') | B_136='#skF_4' | ~v1_funct_2('#skF_4', A_135, B_136) | A_135='#skF_4')), inference(resolution, [status(thm)], [c_355, c_574])).
% 2.62/1.42  tff(c_583, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_1'(k1_tarski('#skF_2'))), '#skF_4') | '#skF_3'='#skF_4' | k1_tarski('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_58, c_581])).
% 2.62/1.42  tff(c_586, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_1'(k1_tarski('#skF_2'))), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_551, c_362, c_583])).
% 2.62/1.42  tff(c_40, plain, (![B_23, A_22]: (~r1_tarski(B_23, A_22) | ~r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.62/1.42  tff(c_593, plain, (~r1_tarski('#skF_4', k1_funct_1('#skF_4', '#skF_1'(k1_tarski('#skF_2'))))), inference(resolution, [status(thm)], [c_586, c_40])).
% 2.62/1.42  tff(c_599, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_358, c_593])).
% 2.62/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.42  
% 2.62/1.42  Inference rules
% 2.62/1.42  ----------------------
% 2.62/1.42  #Ref     : 0
% 2.62/1.42  #Sup     : 105
% 2.62/1.42  #Fact    : 0
% 2.62/1.42  #Define  : 0
% 2.62/1.42  #Split   : 2
% 2.62/1.42  #Chain   : 0
% 2.62/1.42  #Close   : 0
% 2.62/1.42  
% 2.62/1.42  Ordering : KBO
% 2.62/1.42  
% 2.62/1.42  Simplification rules
% 2.62/1.42  ----------------------
% 2.62/1.42  #Subsume      : 1
% 2.62/1.42  #Demod        : 97
% 2.62/1.42  #Tautology    : 70
% 2.62/1.42  #SimpNegUnit  : 2
% 2.62/1.42  #BackRed      : 28
% 2.62/1.42  
% 2.62/1.42  #Partial instantiations: 0
% 2.62/1.42  #Strategies tried      : 1
% 2.62/1.42  
% 2.62/1.42  Timing (in seconds)
% 2.62/1.42  ----------------------
% 2.62/1.42  Preprocessing        : 0.32
% 2.62/1.42  Parsing              : 0.17
% 2.62/1.42  CNF conversion       : 0.02
% 2.62/1.42  Main loop            : 0.29
% 2.62/1.42  Inferencing          : 0.11
% 2.62/1.42  Reduction            : 0.09
% 2.62/1.42  Demodulation         : 0.07
% 2.62/1.42  BG Simplification    : 0.02
% 2.62/1.42  Subsumption          : 0.05
% 2.62/1.42  Abstraction          : 0.01
% 2.62/1.42  MUC search           : 0.00
% 2.62/1.42  Cooper               : 0.00
% 2.62/1.42  Total                : 0.64
% 2.62/1.42  Index Insertion      : 0.00
% 2.62/1.42  Index Deletion       : 0.00
% 2.62/1.42  Index Matching       : 0.00
% 2.62/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
