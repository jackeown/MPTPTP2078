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
% DateTime   : Thu Dec  3 10:14:32 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 208 expanded)
%              Number of leaves         :   43 (  87 expanded)
%              Depth                    :   13
%              Number of atoms          :  187 ( 447 expanded)
%              Number of equality atoms :   97 ( 208 expanded)
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

tff(f_42,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

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

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

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

tff(f_78,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

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

tff(c_14,plain,(
    ! [A_12] : ~ v1_xboole_0(k1_tarski(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_166,plain,(
    ! [C_72,A_73,B_74] :
      ( v1_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_170,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_166])).

tff(c_44,plain,(
    ! [A_19] :
      ( k1_relat_1(A_19) != k1_xboole_0
      | k1_xboole_0 = A_19
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_178,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_170,c_44])).

tff(c_180,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_254,plain,(
    ! [B_98,A_99] :
      ( k1_tarski(k1_funct_1(B_98,A_99)) = k2_relat_1(B_98)
      | k1_tarski(A_99) != k1_relat_1(B_98)
      | ~ v1_funct_1(B_98)
      | ~ v1_relat_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_244,plain,(
    ! [A_95,B_96,C_97] :
      ( k2_relset_1(A_95,B_96,C_97) = k2_relat_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_248,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_244])).

tff(c_60,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') != k1_tarski(k1_funct_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_249,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_60])).

tff(c_260,plain,
    ( k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_249])).

tff(c_290,plain,(
    k1_tarski('#skF_2') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_68,c_260])).

tff(c_234,plain,(
    ! [C_91,A_92,B_93] :
      ( v4_relat_1(C_91,A_92)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_238,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_64,c_234])).

tff(c_8,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_36,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k1_relat_1(B_18),A_17)
      | ~ v4_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_10,plain,(
    ! [A_7,B_8] : k1_enumset1(A_7,A_7,B_8) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_387,plain,(
    ! [A_132,B_133,C_134,D_135] :
      ( k1_enumset1(A_132,B_133,C_134) = D_135
      | k2_tarski(A_132,C_134) = D_135
      | k2_tarski(B_133,C_134) = D_135
      | k2_tarski(A_132,B_133) = D_135
      | k1_tarski(C_134) = D_135
      | k1_tarski(B_133) = D_135
      | k1_tarski(A_132) = D_135
      | k1_xboole_0 = D_135
      | ~ r1_tarski(D_135,k1_enumset1(A_132,B_133,C_134)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_418,plain,(
    ! [A_7,B_8,D_135] :
      ( k1_enumset1(A_7,A_7,B_8) = D_135
      | k2_tarski(A_7,B_8) = D_135
      | k2_tarski(A_7,B_8) = D_135
      | k2_tarski(A_7,A_7) = D_135
      | k1_tarski(B_8) = D_135
      | k1_tarski(A_7) = D_135
      | k1_tarski(A_7) = D_135
      | k1_xboole_0 = D_135
      | ~ r1_tarski(D_135,k2_tarski(A_7,B_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_387])).

tff(c_487,plain,(
    ! [A_150,B_151,D_152] :
      ( k2_tarski(A_150,B_151) = D_152
      | k2_tarski(A_150,B_151) = D_152
      | k2_tarski(A_150,B_151) = D_152
      | k1_tarski(A_150) = D_152
      | k1_tarski(B_151) = D_152
      | k1_tarski(A_150) = D_152
      | k1_tarski(A_150) = D_152
      | k1_xboole_0 = D_152
      | ~ r1_tarski(D_152,k2_tarski(A_150,B_151)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10,c_418])).

tff(c_526,plain,(
    ! [A_153,B_154,B_155] :
      ( k2_tarski(A_153,B_154) = k1_relat_1(B_155)
      | k1_tarski(B_154) = k1_relat_1(B_155)
      | k1_tarski(A_153) = k1_relat_1(B_155)
      | k1_relat_1(B_155) = k1_xboole_0
      | ~ v4_relat_1(B_155,k2_tarski(A_153,B_154))
      | ~ v1_relat_1(B_155) ) ),
    inference(resolution,[status(thm)],[c_36,c_487])).

tff(c_529,plain,(
    ! [A_6,B_155] :
      ( k2_tarski(A_6,A_6) = k1_relat_1(B_155)
      | k1_tarski(A_6) = k1_relat_1(B_155)
      | k1_tarski(A_6) = k1_relat_1(B_155)
      | k1_relat_1(B_155) = k1_xboole_0
      | ~ v4_relat_1(B_155,k1_tarski(A_6))
      | ~ v1_relat_1(B_155) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_526])).

tff(c_531,plain,(
    ! [A_156,B_157] :
      ( k1_tarski(A_156) = k1_relat_1(B_157)
      | k1_tarski(A_156) = k1_relat_1(B_157)
      | k1_tarski(A_156) = k1_relat_1(B_157)
      | k1_relat_1(B_157) = k1_xboole_0
      | ~ v4_relat_1(B_157,k1_tarski(A_156))
      | ~ v1_relat_1(B_157) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_529])).

tff(c_537,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_238,c_531])).

tff(c_540,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_537])).

tff(c_542,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_290,c_540])).

tff(c_543,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_38,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_560,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_543,c_543,c_38])).

tff(c_42,plain,(
    ! [A_19] :
      ( k2_relat_1(A_19) != k1_xboole_0
      | k1_xboole_0 = A_19
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_177,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_170,c_42])).

tff(c_179,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_177])).

tff(c_554,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_543,c_179])).

tff(c_584,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_554])).

tff(c_585,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_590,plain,(
    ! [A_5] : r1_tarski('#skF_4',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_585,c_6])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_593,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_585,c_62])).

tff(c_66,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_586,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_615,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_585,c_586])).

tff(c_705,plain,(
    ! [A_186,B_187,C_188] :
      ( k2_relset_1(A_186,B_187,C_188) = k2_relat_1(C_188)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(A_186,B_187))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_708,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_705])).

tff(c_710,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_615,c_708])).

tff(c_58,plain,(
    ! [D_36,C_35,A_33,B_34] :
      ( r2_hidden(k1_funct_1(D_36,C_35),k2_relset_1(A_33,B_34,D_36))
      | k1_xboole_0 = B_34
      | ~ r2_hidden(C_35,A_33)
      | ~ m1_subset_1(D_36,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34)))
      | ~ v1_funct_2(D_36,A_33,B_34)
      | ~ v1_funct_1(D_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_782,plain,(
    ! [D_200,C_201,A_202,B_203] :
      ( r2_hidden(k1_funct_1(D_200,C_201),k2_relset_1(A_202,B_203,D_200))
      | B_203 = '#skF_4'
      | ~ r2_hidden(C_201,A_202)
      | ~ m1_subset_1(D_200,k1_zfmisc_1(k2_zfmisc_1(A_202,B_203)))
      | ~ v1_funct_2(D_200,A_202,B_203)
      | ~ v1_funct_1(D_200) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_585,c_58])).

tff(c_791,plain,(
    ! [C_201] :
      ( r2_hidden(k1_funct_1('#skF_4',C_201),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_201,k1_tarski('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3')))
      | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_710,c_782])).

tff(c_795,plain,(
    ! [C_201] :
      ( r2_hidden(k1_funct_1('#skF_4',C_201),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_201,k1_tarski('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_791])).

tff(c_797,plain,(
    ! [C_204] :
      ( r2_hidden(k1_funct_1('#skF_4',C_204),'#skF_4')
      | ~ r2_hidden(C_204,k1_tarski('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_593,c_795])).

tff(c_48,plain,(
    ! [B_23,A_22] :
      ( ~ r1_tarski(B_23,A_22)
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_800,plain,(
    ! [C_204] :
      ( ~ r1_tarski('#skF_4',k1_funct_1('#skF_4',C_204))
      | ~ r2_hidden(C_204,k1_tarski('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_797,c_48])).

tff(c_810,plain,(
    ! [C_205] : ~ r2_hidden(C_205,k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_590,c_800])).

tff(c_814,plain,(
    v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_4,c_810])).

tff(c_818,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_814])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:09:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.25/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.51  
% 3.25/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.51  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.25/1.51  
% 3.25/1.51  %Foreground sorts:
% 3.25/1.51  
% 3.25/1.51  
% 3.25/1.51  %Background operators:
% 3.25/1.51  
% 3.25/1.51  
% 3.25/1.51  %Foreground operators:
% 3.25/1.51  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.25/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.25/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.25/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.25/1.51  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.25/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.25/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.25/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.25/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.25/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.25/1.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.25/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.25/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.25/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.25/1.51  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.25/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.25/1.51  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.25/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.25/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.25/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.25/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.51  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.25/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.25/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.25/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.25/1.51  
% 3.49/1.53  tff(f_42, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 3.49/1.53  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.49/1.53  tff(f_137, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 3.49/1.53  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.49/1.53  tff(f_86, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.49/1.53  tff(f_94, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.49/1.53  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.49/1.53  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.49/1.53  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.49/1.53  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.49/1.53  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.49/1.53  tff(f_69, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 3.49/1.53  tff(f_78, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.49/1.53  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.49/1.53  tff(f_125, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 3.49/1.53  tff(f_99, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.49/1.53  tff(c_14, plain, (![A_12]: (~v1_xboole_0(k1_tarski(A_12)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.49/1.53  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.49/1.53  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.49/1.53  tff(c_166, plain, (![C_72, A_73, B_74]: (v1_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.49/1.53  tff(c_170, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_166])).
% 3.49/1.53  tff(c_44, plain, (![A_19]: (k1_relat_1(A_19)!=k1_xboole_0 | k1_xboole_0=A_19 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.49/1.53  tff(c_178, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_170, c_44])).
% 3.49/1.53  tff(c_180, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_178])).
% 3.49/1.53  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.49/1.53  tff(c_254, plain, (![B_98, A_99]: (k1_tarski(k1_funct_1(B_98, A_99))=k2_relat_1(B_98) | k1_tarski(A_99)!=k1_relat_1(B_98) | ~v1_funct_1(B_98) | ~v1_relat_1(B_98))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.49/1.53  tff(c_244, plain, (![A_95, B_96, C_97]: (k2_relset_1(A_95, B_96, C_97)=k2_relat_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.49/1.53  tff(c_248, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_244])).
% 3.49/1.53  tff(c_60, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')!=k1_tarski(k1_funct_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.49/1.53  tff(c_249, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_248, c_60])).
% 3.49/1.53  tff(c_260, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_254, c_249])).
% 3.49/1.53  tff(c_290, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_170, c_68, c_260])).
% 3.49/1.53  tff(c_234, plain, (![C_91, A_92, B_93]: (v4_relat_1(C_91, A_92) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.49/1.53  tff(c_238, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_64, c_234])).
% 3.49/1.53  tff(c_8, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.49/1.53  tff(c_36, plain, (![B_18, A_17]: (r1_tarski(k1_relat_1(B_18), A_17) | ~v4_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.49/1.53  tff(c_10, plain, (![A_7, B_8]: (k1_enumset1(A_7, A_7, B_8)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.49/1.53  tff(c_387, plain, (![A_132, B_133, C_134, D_135]: (k1_enumset1(A_132, B_133, C_134)=D_135 | k2_tarski(A_132, C_134)=D_135 | k2_tarski(B_133, C_134)=D_135 | k2_tarski(A_132, B_133)=D_135 | k1_tarski(C_134)=D_135 | k1_tarski(B_133)=D_135 | k1_tarski(A_132)=D_135 | k1_xboole_0=D_135 | ~r1_tarski(D_135, k1_enumset1(A_132, B_133, C_134)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.49/1.53  tff(c_418, plain, (![A_7, B_8, D_135]: (k1_enumset1(A_7, A_7, B_8)=D_135 | k2_tarski(A_7, B_8)=D_135 | k2_tarski(A_7, B_8)=D_135 | k2_tarski(A_7, A_7)=D_135 | k1_tarski(B_8)=D_135 | k1_tarski(A_7)=D_135 | k1_tarski(A_7)=D_135 | k1_xboole_0=D_135 | ~r1_tarski(D_135, k2_tarski(A_7, B_8)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_387])).
% 3.49/1.53  tff(c_487, plain, (![A_150, B_151, D_152]: (k2_tarski(A_150, B_151)=D_152 | k2_tarski(A_150, B_151)=D_152 | k2_tarski(A_150, B_151)=D_152 | k1_tarski(A_150)=D_152 | k1_tarski(B_151)=D_152 | k1_tarski(A_150)=D_152 | k1_tarski(A_150)=D_152 | k1_xboole_0=D_152 | ~r1_tarski(D_152, k2_tarski(A_150, B_151)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10, c_418])).
% 3.49/1.53  tff(c_526, plain, (![A_153, B_154, B_155]: (k2_tarski(A_153, B_154)=k1_relat_1(B_155) | k1_tarski(B_154)=k1_relat_1(B_155) | k1_tarski(A_153)=k1_relat_1(B_155) | k1_relat_1(B_155)=k1_xboole_0 | ~v4_relat_1(B_155, k2_tarski(A_153, B_154)) | ~v1_relat_1(B_155))), inference(resolution, [status(thm)], [c_36, c_487])).
% 3.49/1.53  tff(c_529, plain, (![A_6, B_155]: (k2_tarski(A_6, A_6)=k1_relat_1(B_155) | k1_tarski(A_6)=k1_relat_1(B_155) | k1_tarski(A_6)=k1_relat_1(B_155) | k1_relat_1(B_155)=k1_xboole_0 | ~v4_relat_1(B_155, k1_tarski(A_6)) | ~v1_relat_1(B_155))), inference(superposition, [status(thm), theory('equality')], [c_8, c_526])).
% 3.49/1.53  tff(c_531, plain, (![A_156, B_157]: (k1_tarski(A_156)=k1_relat_1(B_157) | k1_tarski(A_156)=k1_relat_1(B_157) | k1_tarski(A_156)=k1_relat_1(B_157) | k1_relat_1(B_157)=k1_xboole_0 | ~v4_relat_1(B_157, k1_tarski(A_156)) | ~v1_relat_1(B_157))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_529])).
% 3.49/1.53  tff(c_537, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_238, c_531])).
% 3.49/1.53  tff(c_540, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_170, c_537])).
% 3.49/1.53  tff(c_542, plain, $false, inference(negUnitSimplification, [status(thm)], [c_180, c_290, c_540])).
% 3.49/1.53  tff(c_543, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_178])).
% 3.49/1.53  tff(c_38, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.49/1.53  tff(c_560, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_543, c_543, c_38])).
% 3.49/1.53  tff(c_42, plain, (![A_19]: (k2_relat_1(A_19)!=k1_xboole_0 | k1_xboole_0=A_19 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.49/1.53  tff(c_177, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_170, c_42])).
% 3.49/1.53  tff(c_179, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_177])).
% 3.49/1.53  tff(c_554, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_543, c_179])).
% 3.49/1.53  tff(c_584, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_560, c_554])).
% 3.49/1.53  tff(c_585, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_177])).
% 3.49/1.53  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.49/1.53  tff(c_590, plain, (![A_5]: (r1_tarski('#skF_4', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_585, c_6])).
% 3.49/1.53  tff(c_62, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.49/1.53  tff(c_593, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_585, c_62])).
% 3.49/1.53  tff(c_66, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.49/1.53  tff(c_586, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_177])).
% 3.49/1.53  tff(c_615, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_585, c_586])).
% 3.49/1.53  tff(c_705, plain, (![A_186, B_187, C_188]: (k2_relset_1(A_186, B_187, C_188)=k2_relat_1(C_188) | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1(A_186, B_187))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.49/1.53  tff(c_708, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_705])).
% 3.49/1.53  tff(c_710, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_615, c_708])).
% 3.49/1.53  tff(c_58, plain, (![D_36, C_35, A_33, B_34]: (r2_hidden(k1_funct_1(D_36, C_35), k2_relset_1(A_33, B_34, D_36)) | k1_xboole_0=B_34 | ~r2_hidden(C_35, A_33) | ~m1_subset_1(D_36, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))) | ~v1_funct_2(D_36, A_33, B_34) | ~v1_funct_1(D_36))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.49/1.53  tff(c_782, plain, (![D_200, C_201, A_202, B_203]: (r2_hidden(k1_funct_1(D_200, C_201), k2_relset_1(A_202, B_203, D_200)) | B_203='#skF_4' | ~r2_hidden(C_201, A_202) | ~m1_subset_1(D_200, k1_zfmisc_1(k2_zfmisc_1(A_202, B_203))) | ~v1_funct_2(D_200, A_202, B_203) | ~v1_funct_1(D_200))), inference(demodulation, [status(thm), theory('equality')], [c_585, c_58])).
% 3.49/1.53  tff(c_791, plain, (![C_201]: (r2_hidden(k1_funct_1('#skF_4', C_201), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_201, k1_tarski('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3') | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_710, c_782])).
% 3.49/1.53  tff(c_795, plain, (![C_201]: (r2_hidden(k1_funct_1('#skF_4', C_201), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_201, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_791])).
% 3.49/1.53  tff(c_797, plain, (![C_204]: (r2_hidden(k1_funct_1('#skF_4', C_204), '#skF_4') | ~r2_hidden(C_204, k1_tarski('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_593, c_795])).
% 3.49/1.53  tff(c_48, plain, (![B_23, A_22]: (~r1_tarski(B_23, A_22) | ~r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.49/1.53  tff(c_800, plain, (![C_204]: (~r1_tarski('#skF_4', k1_funct_1('#skF_4', C_204)) | ~r2_hidden(C_204, k1_tarski('#skF_2')))), inference(resolution, [status(thm)], [c_797, c_48])).
% 3.49/1.53  tff(c_810, plain, (![C_205]: (~r2_hidden(C_205, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_590, c_800])).
% 3.49/1.53  tff(c_814, plain, (v1_xboole_0(k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_4, c_810])).
% 3.49/1.53  tff(c_818, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_814])).
% 3.49/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.53  
% 3.49/1.53  Inference rules
% 3.49/1.53  ----------------------
% 3.49/1.53  #Ref     : 0
% 3.49/1.53  #Sup     : 162
% 3.49/1.53  #Fact    : 0
% 3.49/1.53  #Define  : 0
% 3.49/1.53  #Split   : 5
% 3.49/1.53  #Chain   : 0
% 3.49/1.53  #Close   : 0
% 3.49/1.53  
% 3.49/1.53  Ordering : KBO
% 3.49/1.53  
% 3.49/1.53  Simplification rules
% 3.49/1.53  ----------------------
% 3.49/1.53  #Subsume      : 29
% 3.49/1.53  #Demod        : 131
% 3.49/1.53  #Tautology    : 77
% 3.49/1.53  #SimpNegUnit  : 7
% 3.49/1.53  #BackRed      : 17
% 3.49/1.53  
% 3.49/1.53  #Partial instantiations: 0
% 3.49/1.53  #Strategies tried      : 1
% 3.49/1.53  
% 3.49/1.53  Timing (in seconds)
% 3.49/1.53  ----------------------
% 3.49/1.54  Preprocessing        : 0.35
% 3.49/1.54  Parsing              : 0.19
% 3.49/1.54  CNF conversion       : 0.02
% 3.49/1.54  Main loop            : 0.42
% 3.49/1.54  Inferencing          : 0.16
% 3.49/1.54  Reduction            : 0.14
% 3.49/1.54  Demodulation         : 0.10
% 3.49/1.54  BG Simplification    : 0.02
% 3.49/1.54  Subsumption          : 0.07
% 3.49/1.54  Abstraction          : 0.02
% 3.49/1.54  MUC search           : 0.00
% 3.49/1.54  Cooper               : 0.00
% 3.49/1.54  Total                : 0.81
% 3.49/1.54  Index Insertion      : 0.00
% 3.49/1.54  Index Deletion       : 0.00
% 3.49/1.54  Index Matching       : 0.00
% 3.49/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
