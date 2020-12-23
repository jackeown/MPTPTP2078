%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:32 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 172 expanded)
%              Number of leaves         :   43 (  76 expanded)
%              Depth                    :   13
%              Number of atoms          :  178 ( 363 expanded)
%              Number of equality atoms :   89 ( 168 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_42,axiom,(
    ! [A,B] : ~ v1_xboole_0(k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_137,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(D,k1_enumset1(A,B,C))
    <=> ~ ( D != k1_xboole_0
          & D != k1_tarski(A)
          & D != k1_tarski(B)
          & D != k1_tarski(C)
          & D != k2_tarski(A,B)
          & D != k2_tarski(B,C)
          & D != k2_tarski(A,C)
          & D != k1_enumset1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_78,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_125,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_99,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_80,plain,(
    ! [A_41] : k2_tarski(A_41,A_41) = k1_tarski(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_12,B_13] : ~ v1_xboole_0(k2_tarski(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_85,plain,(
    ! [A_41] : ~ v1_xboole_0(k1_tarski(A_41)) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_14])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_138,plain,(
    ! [C_65,A_66,B_67] :
      ( v1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_142,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_138])).

tff(c_44,plain,(
    ! [A_20] :
      ( k1_relat_1(A_20) != k1_xboole_0
      | k1_xboole_0 = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_149,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_142,c_44])).

tff(c_151,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_149])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_252,plain,(
    ! [B_100,A_101] :
      ( k1_tarski(k1_funct_1(B_100,A_101)) = k2_relat_1(B_100)
      | k1_tarski(A_101) != k1_relat_1(B_100)
      | ~ v1_funct_1(B_100)
      | ~ v1_relat_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_242,plain,(
    ! [A_97,B_98,C_99] :
      ( k2_relset_1(A_97,B_98,C_99) = k2_relat_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_246,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_242])).

tff(c_60,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') != k1_tarski(k1_funct_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_247,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_60])).

tff(c_258,plain,
    ( k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_247])).

tff(c_288,plain,(
    k1_tarski('#skF_2') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_68,c_258])).

tff(c_202,plain,(
    ! [C_84,A_85,B_86] :
      ( v4_relat_1(C_84,A_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_206,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_64,c_202])).

tff(c_8,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_36,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k1_relat_1(B_19),A_18)
      | ~ v4_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_10,plain,(
    ! [A_7,B_8] : k1_enumset1(A_7,A_7,B_8) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_387,plain,(
    ! [A_133,B_134,C_135,D_136] :
      ( k1_enumset1(A_133,B_134,C_135) = D_136
      | k2_tarski(A_133,C_135) = D_136
      | k2_tarski(B_134,C_135) = D_136
      | k2_tarski(A_133,B_134) = D_136
      | k1_tarski(C_135) = D_136
      | k1_tarski(B_134) = D_136
      | k1_tarski(A_133) = D_136
      | k1_xboole_0 = D_136
      | ~ r1_tarski(D_136,k1_enumset1(A_133,B_134,C_135)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_415,plain,(
    ! [A_7,B_8,D_136] :
      ( k1_enumset1(A_7,A_7,B_8) = D_136
      | k2_tarski(A_7,B_8) = D_136
      | k2_tarski(A_7,B_8) = D_136
      | k2_tarski(A_7,A_7) = D_136
      | k1_tarski(B_8) = D_136
      | k1_tarski(A_7) = D_136
      | k1_tarski(A_7) = D_136
      | k1_xboole_0 = D_136
      | ~ r1_tarski(D_136,k2_tarski(A_7,B_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_387])).

tff(c_490,plain,(
    ! [A_153,B_154,D_155] :
      ( k2_tarski(A_153,B_154) = D_155
      | k2_tarski(A_153,B_154) = D_155
      | k2_tarski(A_153,B_154) = D_155
      | k1_tarski(A_153) = D_155
      | k1_tarski(B_154) = D_155
      | k1_tarski(A_153) = D_155
      | k1_tarski(A_153) = D_155
      | k1_xboole_0 = D_155
      | ~ r1_tarski(D_155,k2_tarski(A_153,B_154)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10,c_415])).

tff(c_534,plain,(
    ! [A_160,B_161,B_162] :
      ( k2_tarski(A_160,B_161) = k1_relat_1(B_162)
      | k1_tarski(B_161) = k1_relat_1(B_162)
      | k1_tarski(A_160) = k1_relat_1(B_162)
      | k1_relat_1(B_162) = k1_xboole_0
      | ~ v4_relat_1(B_162,k2_tarski(A_160,B_161))
      | ~ v1_relat_1(B_162) ) ),
    inference(resolution,[status(thm)],[c_36,c_490])).

tff(c_537,plain,(
    ! [A_6,B_162] :
      ( k2_tarski(A_6,A_6) = k1_relat_1(B_162)
      | k1_tarski(A_6) = k1_relat_1(B_162)
      | k1_tarski(A_6) = k1_relat_1(B_162)
      | k1_relat_1(B_162) = k1_xboole_0
      | ~ v4_relat_1(B_162,k1_tarski(A_6))
      | ~ v1_relat_1(B_162) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_534])).

tff(c_539,plain,(
    ! [A_163,B_164] :
      ( k1_tarski(A_163) = k1_relat_1(B_164)
      | k1_tarski(A_163) = k1_relat_1(B_164)
      | k1_tarski(A_163) = k1_relat_1(B_164)
      | k1_relat_1(B_164) = k1_xboole_0
      | ~ v4_relat_1(B_164,k1_tarski(A_163))
      | ~ v1_relat_1(B_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_537])).

tff(c_545,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_206,c_539])).

tff(c_548,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_545])).

tff(c_550,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_288,c_548])).

tff(c_551,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_149])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_556,plain,(
    ! [A_5] : r1_tarski('#skF_4',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_551,c_6])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_559,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_551,c_62])).

tff(c_66,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_38,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_558,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_551,c_551,c_38])).

tff(c_702,plain,(
    ! [A_199,B_200,C_201] :
      ( k2_relset_1(A_199,B_200,C_201) = k2_relat_1(C_201)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(A_199,B_200))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_705,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_702])).

tff(c_707,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_705])).

tff(c_58,plain,(
    ! [D_37,C_36,A_34,B_35] :
      ( r2_hidden(k1_funct_1(D_37,C_36),k2_relset_1(A_34,B_35,D_37))
      | k1_xboole_0 = B_35
      | ~ r2_hidden(C_36,A_34)
      | ~ m1_subset_1(D_37,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ v1_funct_2(D_37,A_34,B_35)
      | ~ v1_funct_1(D_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_759,plain,(
    ! [D_207,C_208,A_209,B_210] :
      ( r2_hidden(k1_funct_1(D_207,C_208),k2_relset_1(A_209,B_210,D_207))
      | B_210 = '#skF_4'
      | ~ r2_hidden(C_208,A_209)
      | ~ m1_subset_1(D_207,k1_zfmisc_1(k2_zfmisc_1(A_209,B_210)))
      | ~ v1_funct_2(D_207,A_209,B_210)
      | ~ v1_funct_1(D_207) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_551,c_58])).

tff(c_768,plain,(
    ! [C_208] :
      ( r2_hidden(k1_funct_1('#skF_4',C_208),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_208,k1_tarski('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3')))
      | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_707,c_759])).

tff(c_772,plain,(
    ! [C_208] :
      ( r2_hidden(k1_funct_1('#skF_4',C_208),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_208,k1_tarski('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_768])).

tff(c_774,plain,(
    ! [C_211] :
      ( r2_hidden(k1_funct_1('#skF_4',C_211),'#skF_4')
      | ~ r2_hidden(C_211,k1_tarski('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_559,c_772])).

tff(c_48,plain,(
    ! [B_24,A_23] :
      ( ~ r1_tarski(B_24,A_23)
      | ~ r2_hidden(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_777,plain,(
    ! [C_211] :
      ( ~ r1_tarski('#skF_4',k1_funct_1('#skF_4',C_211))
      | ~ r2_hidden(C_211,k1_tarski('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_774,c_48])).

tff(c_787,plain,(
    ! [C_212] : ~ r2_hidden(C_212,k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_777])).

tff(c_791,plain,(
    v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_4,c_787])).

tff(c_795,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_791])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:16:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.07/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.54  
% 3.07/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.54  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.07/1.54  
% 3.07/1.54  %Foreground sorts:
% 3.07/1.54  
% 3.07/1.54  
% 3.07/1.54  %Background operators:
% 3.07/1.54  
% 3.07/1.54  
% 3.07/1.54  %Foreground operators:
% 3.07/1.54  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.07/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.07/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.07/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.07/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.07/1.54  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.07/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.07/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.07/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.07/1.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.07/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.07/1.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.07/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.07/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.07/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.07/1.54  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.07/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.07/1.54  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.07/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.07/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.07/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.07/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.07/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.07/1.54  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.07/1.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.07/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.07/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.07/1.54  
% 3.07/1.56  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.07/1.56  tff(f_42, axiom, (![A, B]: ~v1_xboole_0(k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_xboole_0)).
% 3.07/1.56  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.07/1.56  tff(f_137, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 3.07/1.56  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.07/1.56  tff(f_86, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.07/1.56  tff(f_94, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.07/1.56  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.07/1.56  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.07/1.56  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.07/1.56  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.07/1.56  tff(f_69, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 3.07/1.56  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.07/1.56  tff(f_78, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.07/1.56  tff(f_125, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 3.07/1.56  tff(f_99, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.07/1.56  tff(c_80, plain, (![A_41]: (k2_tarski(A_41, A_41)=k1_tarski(A_41))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.07/1.56  tff(c_14, plain, (![A_12, B_13]: (~v1_xboole_0(k2_tarski(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.07/1.56  tff(c_85, plain, (![A_41]: (~v1_xboole_0(k1_tarski(A_41)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_14])).
% 3.07/1.56  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.07/1.56  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.07/1.56  tff(c_138, plain, (![C_65, A_66, B_67]: (v1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.07/1.56  tff(c_142, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_138])).
% 3.07/1.56  tff(c_44, plain, (![A_20]: (k1_relat_1(A_20)!=k1_xboole_0 | k1_xboole_0=A_20 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.07/1.56  tff(c_149, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_142, c_44])).
% 3.07/1.56  tff(c_151, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_149])).
% 3.07/1.56  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.07/1.56  tff(c_252, plain, (![B_100, A_101]: (k1_tarski(k1_funct_1(B_100, A_101))=k2_relat_1(B_100) | k1_tarski(A_101)!=k1_relat_1(B_100) | ~v1_funct_1(B_100) | ~v1_relat_1(B_100))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.07/1.56  tff(c_242, plain, (![A_97, B_98, C_99]: (k2_relset_1(A_97, B_98, C_99)=k2_relat_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.07/1.56  tff(c_246, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_242])).
% 3.07/1.56  tff(c_60, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')!=k1_tarski(k1_funct_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.07/1.56  tff(c_247, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_246, c_60])).
% 3.07/1.56  tff(c_258, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_252, c_247])).
% 3.07/1.56  tff(c_288, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_68, c_258])).
% 3.07/1.56  tff(c_202, plain, (![C_84, A_85, B_86]: (v4_relat_1(C_84, A_85) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.07/1.56  tff(c_206, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_64, c_202])).
% 3.07/1.56  tff(c_8, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.07/1.56  tff(c_36, plain, (![B_19, A_18]: (r1_tarski(k1_relat_1(B_19), A_18) | ~v4_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.07/1.56  tff(c_10, plain, (![A_7, B_8]: (k1_enumset1(A_7, A_7, B_8)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.07/1.56  tff(c_387, plain, (![A_133, B_134, C_135, D_136]: (k1_enumset1(A_133, B_134, C_135)=D_136 | k2_tarski(A_133, C_135)=D_136 | k2_tarski(B_134, C_135)=D_136 | k2_tarski(A_133, B_134)=D_136 | k1_tarski(C_135)=D_136 | k1_tarski(B_134)=D_136 | k1_tarski(A_133)=D_136 | k1_xboole_0=D_136 | ~r1_tarski(D_136, k1_enumset1(A_133, B_134, C_135)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.07/1.56  tff(c_415, plain, (![A_7, B_8, D_136]: (k1_enumset1(A_7, A_7, B_8)=D_136 | k2_tarski(A_7, B_8)=D_136 | k2_tarski(A_7, B_8)=D_136 | k2_tarski(A_7, A_7)=D_136 | k1_tarski(B_8)=D_136 | k1_tarski(A_7)=D_136 | k1_tarski(A_7)=D_136 | k1_xboole_0=D_136 | ~r1_tarski(D_136, k2_tarski(A_7, B_8)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_387])).
% 3.07/1.56  tff(c_490, plain, (![A_153, B_154, D_155]: (k2_tarski(A_153, B_154)=D_155 | k2_tarski(A_153, B_154)=D_155 | k2_tarski(A_153, B_154)=D_155 | k1_tarski(A_153)=D_155 | k1_tarski(B_154)=D_155 | k1_tarski(A_153)=D_155 | k1_tarski(A_153)=D_155 | k1_xboole_0=D_155 | ~r1_tarski(D_155, k2_tarski(A_153, B_154)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10, c_415])).
% 3.07/1.56  tff(c_534, plain, (![A_160, B_161, B_162]: (k2_tarski(A_160, B_161)=k1_relat_1(B_162) | k1_tarski(B_161)=k1_relat_1(B_162) | k1_tarski(A_160)=k1_relat_1(B_162) | k1_relat_1(B_162)=k1_xboole_0 | ~v4_relat_1(B_162, k2_tarski(A_160, B_161)) | ~v1_relat_1(B_162))), inference(resolution, [status(thm)], [c_36, c_490])).
% 3.07/1.56  tff(c_537, plain, (![A_6, B_162]: (k2_tarski(A_6, A_6)=k1_relat_1(B_162) | k1_tarski(A_6)=k1_relat_1(B_162) | k1_tarski(A_6)=k1_relat_1(B_162) | k1_relat_1(B_162)=k1_xboole_0 | ~v4_relat_1(B_162, k1_tarski(A_6)) | ~v1_relat_1(B_162))), inference(superposition, [status(thm), theory('equality')], [c_8, c_534])).
% 3.07/1.56  tff(c_539, plain, (![A_163, B_164]: (k1_tarski(A_163)=k1_relat_1(B_164) | k1_tarski(A_163)=k1_relat_1(B_164) | k1_tarski(A_163)=k1_relat_1(B_164) | k1_relat_1(B_164)=k1_xboole_0 | ~v4_relat_1(B_164, k1_tarski(A_163)) | ~v1_relat_1(B_164))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_537])).
% 3.07/1.56  tff(c_545, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_206, c_539])).
% 3.07/1.56  tff(c_548, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_142, c_545])).
% 3.07/1.56  tff(c_550, plain, $false, inference(negUnitSimplification, [status(thm)], [c_151, c_288, c_548])).
% 3.07/1.56  tff(c_551, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_149])).
% 3.07/1.56  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.07/1.56  tff(c_556, plain, (![A_5]: (r1_tarski('#skF_4', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_551, c_6])).
% 3.07/1.56  tff(c_62, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.07/1.56  tff(c_559, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_551, c_62])).
% 3.07/1.56  tff(c_66, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.07/1.56  tff(c_38, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.07/1.56  tff(c_558, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_551, c_551, c_38])).
% 3.07/1.56  tff(c_702, plain, (![A_199, B_200, C_201]: (k2_relset_1(A_199, B_200, C_201)=k2_relat_1(C_201) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(A_199, B_200))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.07/1.56  tff(c_705, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_702])).
% 3.07/1.56  tff(c_707, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_558, c_705])).
% 3.07/1.56  tff(c_58, plain, (![D_37, C_36, A_34, B_35]: (r2_hidden(k1_funct_1(D_37, C_36), k2_relset_1(A_34, B_35, D_37)) | k1_xboole_0=B_35 | ~r2_hidden(C_36, A_34) | ~m1_subset_1(D_37, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))) | ~v1_funct_2(D_37, A_34, B_35) | ~v1_funct_1(D_37))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.07/1.56  tff(c_759, plain, (![D_207, C_208, A_209, B_210]: (r2_hidden(k1_funct_1(D_207, C_208), k2_relset_1(A_209, B_210, D_207)) | B_210='#skF_4' | ~r2_hidden(C_208, A_209) | ~m1_subset_1(D_207, k1_zfmisc_1(k2_zfmisc_1(A_209, B_210))) | ~v1_funct_2(D_207, A_209, B_210) | ~v1_funct_1(D_207))), inference(demodulation, [status(thm), theory('equality')], [c_551, c_58])).
% 3.07/1.56  tff(c_768, plain, (![C_208]: (r2_hidden(k1_funct_1('#skF_4', C_208), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_208, k1_tarski('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3') | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_707, c_759])).
% 3.07/1.56  tff(c_772, plain, (![C_208]: (r2_hidden(k1_funct_1('#skF_4', C_208), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_208, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_768])).
% 3.07/1.56  tff(c_774, plain, (![C_211]: (r2_hidden(k1_funct_1('#skF_4', C_211), '#skF_4') | ~r2_hidden(C_211, k1_tarski('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_559, c_772])).
% 3.07/1.56  tff(c_48, plain, (![B_24, A_23]: (~r1_tarski(B_24, A_23) | ~r2_hidden(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.07/1.56  tff(c_777, plain, (![C_211]: (~r1_tarski('#skF_4', k1_funct_1('#skF_4', C_211)) | ~r2_hidden(C_211, k1_tarski('#skF_2')))), inference(resolution, [status(thm)], [c_774, c_48])).
% 3.07/1.56  tff(c_787, plain, (![C_212]: (~r2_hidden(C_212, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_556, c_777])).
% 3.07/1.56  tff(c_791, plain, (v1_xboole_0(k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_4, c_787])).
% 3.07/1.56  tff(c_795, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_791])).
% 3.07/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.56  
% 3.07/1.56  Inference rules
% 3.07/1.56  ----------------------
% 3.07/1.56  #Ref     : 0
% 3.07/1.56  #Sup     : 157
% 3.07/1.56  #Fact    : 0
% 3.07/1.56  #Define  : 0
% 3.07/1.56  #Split   : 5
% 3.07/1.56  #Chain   : 0
% 3.07/1.56  #Close   : 0
% 3.07/1.56  
% 3.07/1.56  Ordering : KBO
% 3.07/1.56  
% 3.07/1.56  Simplification rules
% 3.07/1.56  ----------------------
% 3.07/1.56  #Subsume      : 27
% 3.07/1.56  #Demod        : 120
% 3.07/1.56  #Tautology    : 73
% 3.07/1.56  #SimpNegUnit  : 7
% 3.07/1.56  #BackRed      : 9
% 3.07/1.56  
% 3.07/1.56  #Partial instantiations: 0
% 3.07/1.56  #Strategies tried      : 1
% 3.07/1.56  
% 3.07/1.56  Timing (in seconds)
% 3.07/1.56  ----------------------
% 3.07/1.56  Preprocessing        : 0.37
% 3.07/1.56  Parsing              : 0.20
% 3.07/1.56  CNF conversion       : 0.02
% 3.07/1.56  Main loop            : 0.40
% 3.07/1.56  Inferencing          : 0.15
% 3.07/1.56  Reduction            : 0.13
% 3.07/1.56  Demodulation         : 0.09
% 3.07/1.56  BG Simplification    : 0.02
% 3.07/1.56  Subsumption          : 0.07
% 3.07/1.56  Abstraction          : 0.02
% 3.07/1.56  MUC search           : 0.00
% 3.07/1.56  Cooper               : 0.00
% 3.07/1.56  Total                : 0.81
% 3.07/1.56  Index Insertion      : 0.00
% 3.07/1.56  Index Deletion       : 0.00
% 3.07/1.56  Index Matching       : 0.00
% 3.07/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
