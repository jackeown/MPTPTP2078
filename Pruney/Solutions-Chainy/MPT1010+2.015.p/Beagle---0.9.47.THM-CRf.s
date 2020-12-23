%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:07 EST 2020

% Result     : Theorem 8.81s
% Output     : CNFRefutation 8.81s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 307 expanded)
%              Number of leaves         :   46 ( 125 expanded)
%              Depth                    :   18
%              Number of atoms          :  188 ( 711 expanded)
%              Number of equality atoms :   62 ( 222 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_114,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_103,axiom,(
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

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_57,axiom,(
    ! [A,B] : ~ v1_xboole_0(k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_xboole_0)).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_64,plain,(
    k1_funct_1('#skF_7','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_12,plain,(
    ! [C_10] : r2_hidden(C_10,k1_tarski(C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_108,plain,(
    ! [A_68,B_69] :
      ( ~ r2_hidden('#skF_1'(A_68,B_69),B_69)
      | r1_tarski(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_113,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_108])).

tff(c_66,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_140,plain,(
    ! [C_85,B_86,A_87] :
      ( r2_hidden(C_85,B_86)
      | ~ r2_hidden(C_85,A_87)
      | ~ r1_tarski(A_87,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_149,plain,(
    ! [B_86] :
      ( r2_hidden('#skF_6',B_86)
      | ~ r1_tarski('#skF_4',B_86) ) ),
    inference(resolution,[status(thm)],[c_66,c_140])).

tff(c_68,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_tarski('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_115,plain,(
    ! [C_71,A_72,B_73] :
      ( v1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_119,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_115])).

tff(c_72,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_70,plain,(
    v1_funct_2('#skF_7','#skF_4',k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_261,plain,(
    ! [A_120,B_121,C_122] :
      ( k1_relset_1(A_120,B_121,C_122) = k1_relat_1(C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_265,plain,(
    k1_relset_1('#skF_4',k1_tarski('#skF_5'),'#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_261])).

tff(c_369,plain,(
    ! [B_161,A_162,C_163] :
      ( k1_xboole_0 = B_161
      | k1_relset_1(A_162,B_161,C_163) = A_162
      | ~ v1_funct_2(C_163,A_162,B_161)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_162,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_372,plain,
    ( k1_tarski('#skF_5') = k1_xboole_0
    | k1_relset_1('#skF_4',k1_tarski('#skF_5'),'#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_68,c_369])).

tff(c_375,plain,
    ( k1_tarski('#skF_5') = k1_xboole_0
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_265,c_372])).

tff(c_376,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_375])).

tff(c_120,plain,(
    ! [C_74,B_75,A_76] :
      ( v5_relat_1(C_74,B_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_76,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_124,plain,(
    v5_relat_1('#skF_7',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_68,c_120])).

tff(c_40,plain,(
    ! [B_42,A_41] :
      ( r1_tarski(k2_relat_1(B_42),A_41)
      | ~ v5_relat_1(B_42,A_41)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_219,plain,(
    ! [A_107,B_108,B_109] :
      ( r2_hidden('#skF_1'(A_107,B_108),B_109)
      | ~ r1_tarski(A_107,B_109)
      | r1_tarski(A_107,B_108) ) ),
    inference(resolution,[status(thm)],[c_6,c_140])).

tff(c_10,plain,(
    ! [C_10,A_6] :
      ( C_10 = A_6
      | ~ r2_hidden(C_10,k1_tarski(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_245,plain,(
    ! [A_112,A_113,B_114] :
      ( A_112 = '#skF_1'(A_113,B_114)
      | ~ r1_tarski(A_113,k1_tarski(A_112))
      | r1_tarski(A_113,B_114) ) ),
    inference(resolution,[status(thm)],[c_219,c_10])).

tff(c_363,plain,(
    ! [A_158,B_159,B_160] :
      ( A_158 = '#skF_1'(k2_relat_1(B_159),B_160)
      | r1_tarski(k2_relat_1(B_159),B_160)
      | ~ v5_relat_1(B_159,k1_tarski(A_158))
      | ~ v1_relat_1(B_159) ) ),
    inference(resolution,[status(thm)],[c_40,c_245])).

tff(c_365,plain,(
    ! [B_160] :
      ( '#skF_1'(k2_relat_1('#skF_7'),B_160) = '#skF_5'
      | r1_tarski(k2_relat_1('#skF_7'),B_160)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_124,c_363])).

tff(c_368,plain,(
    ! [B_160] :
      ( '#skF_1'(k2_relat_1('#skF_7'),B_160) = '#skF_5'
      | r1_tarski(k2_relat_1('#skF_7'),B_160) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_365])).

tff(c_290,plain,(
    ! [B_134,A_135] :
      ( r2_hidden(k1_funct_1(B_134,A_135),k2_relat_1(B_134))
      | ~ r2_hidden(A_135,k1_relat_1(B_134))
      | ~ v1_funct_1(B_134)
      | ~ v1_relat_1(B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20374,plain,(
    ! [B_16192,A_16193,B_16194] :
      ( r2_hidden(k1_funct_1(B_16192,A_16193),B_16194)
      | ~ r1_tarski(k2_relat_1(B_16192),B_16194)
      | ~ r2_hidden(A_16193,k1_relat_1(B_16192))
      | ~ v1_funct_1(B_16192)
      | ~ v1_relat_1(B_16192) ) ),
    inference(resolution,[status(thm)],[c_290,c_2])).

tff(c_20389,plain,(
    ! [B_16299,A_16300,A_16301] :
      ( k1_funct_1(B_16299,A_16300) = A_16301
      | ~ r1_tarski(k2_relat_1(B_16299),k1_tarski(A_16301))
      | ~ r2_hidden(A_16300,k1_relat_1(B_16299))
      | ~ v1_funct_1(B_16299)
      | ~ v1_relat_1(B_16299) ) ),
    inference(resolution,[status(thm)],[c_20374,c_10])).

tff(c_20404,plain,(
    ! [A_16300,A_16301] :
      ( k1_funct_1('#skF_7',A_16300) = A_16301
      | ~ r2_hidden(A_16300,k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | '#skF_1'(k2_relat_1('#skF_7'),k1_tarski(A_16301)) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_368,c_20389])).

tff(c_20412,plain,(
    ! [A_16406,A_16407] :
      ( k1_funct_1('#skF_7',A_16406) = A_16407
      | ~ r2_hidden(A_16406,'#skF_4')
      | '#skF_1'(k2_relat_1('#skF_7'),k1_tarski(A_16407)) = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_72,c_376,c_20404])).

tff(c_20474,plain,(
    ! [A_16407] :
      ( k1_funct_1('#skF_7','#skF_6') = A_16407
      | '#skF_1'(k2_relat_1('#skF_7'),k1_tarski(A_16407)) = '#skF_5'
      | ~ r1_tarski('#skF_4','#skF_4') ) ),
    inference(resolution,[status(thm)],[c_149,c_20412])).

tff(c_20491,plain,(
    ! [A_16512] :
      ( k1_funct_1('#skF_7','#skF_6') = A_16512
      | '#skF_1'(k2_relat_1('#skF_7'),k1_tarski(A_16512)) = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_20474])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20506,plain,(
    ! [A_16512] :
      ( ~ r2_hidden('#skF_5',k1_tarski(A_16512))
      | r1_tarski(k2_relat_1('#skF_7'),k1_tarski(A_16512))
      | k1_funct_1('#skF_7','#skF_6') = A_16512 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20491,c_4])).

tff(c_293,plain,(
    ! [B_134,A_135,B_2] :
      ( r2_hidden(k1_funct_1(B_134,A_135),B_2)
      | ~ r1_tarski(k2_relat_1(B_134),B_2)
      | ~ r2_hidden(A_135,k1_relat_1(B_134))
      | ~ v1_funct_1(B_134)
      | ~ v1_relat_1(B_134) ) ),
    inference(resolution,[status(thm)],[c_290,c_2])).

tff(c_102,plain,(
    ! [A_66,B_67] :
      ( r2_hidden('#skF_1'(A_66,B_67),A_66)
      | r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_107,plain,(
    ! [A_6,B_67] :
      ( '#skF_1'(k1_tarski(A_6),B_67) = A_6
      | r1_tarski(k1_tarski(A_6),B_67) ) ),
    inference(resolution,[status(thm)],[c_102,c_10])).

tff(c_538,plain,(
    ! [A_180,A_181,B_182] :
      ( A_180 = '#skF_1'(k1_tarski(A_181),B_182)
      | r1_tarski(k1_tarski(A_181),B_182)
      | '#skF_1'(k1_tarski(A_181),k1_tarski(A_180)) = A_181 ) ),
    inference(resolution,[status(thm)],[c_107,c_245])).

tff(c_148,plain,(
    ! [C_10,B_86] :
      ( r2_hidden(C_10,B_86)
      | ~ r1_tarski(k1_tarski(C_10),B_86) ) ),
    inference(resolution,[status(thm)],[c_12,c_140])).

tff(c_2683,plain,(
    ! [A_3903,B_3904] :
      ( r2_hidden(A_3903,B_3904)
      | '#skF_1'(k1_tarski(A_3903),B_3904) = '#skF_5'
      | '#skF_1'(k1_tarski(A_3903),k1_tarski('#skF_5')) = A_3903 ) ),
    inference(resolution,[status(thm)],[c_538,c_148])).

tff(c_185,plain,(
    ! [A_97,B_98] :
      ( '#skF_1'(k1_tarski(A_97),B_98) = A_97
      | r1_tarski(k1_tarski(A_97),B_98) ) ),
    inference(resolution,[status(thm)],[c_102,c_10])).

tff(c_192,plain,(
    ! [A_97,B_98] :
      ( r2_hidden(A_97,B_98)
      | '#skF_1'(k1_tarski(A_97),B_98) = A_97 ) ),
    inference(resolution,[status(thm)],[c_185,c_148])).

tff(c_2686,plain,(
    ! [A_3903,B_3904] :
      ( r2_hidden(A_3903,B_3904)
      | A_3903 = '#skF_5'
      | r2_hidden(A_3903,B_3904)
      | '#skF_1'(k1_tarski(A_3903),k1_tarski('#skF_5')) = A_3903 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2683,c_192])).

tff(c_3761,plain,(
    ! [A_7756,B_7757] :
      ( A_7756 = '#skF_5'
      | '#skF_1'(k1_tarski(A_7756),k1_tarski('#skF_5')) = A_7756
      | r2_hidden(A_7756,B_7757) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_2686])).

tff(c_4574,plain,(
    ! [A_7969,A_7968] :
      ( A_7969 = A_7968
      | A_7968 = '#skF_5'
      | '#skF_1'(k1_tarski(A_7968),k1_tarski('#skF_5')) = A_7968 ) ),
    inference(resolution,[status(thm)],[c_3761,c_10])).

tff(c_18855,plain,(
    ! [A_7969] :
      ( A_7969 != '#skF_5'
      | k1_funct_1('#skF_7','#skF_6') = '#skF_5'
      | '#skF_1'(k1_tarski(k1_funct_1('#skF_7','#skF_6')),k1_tarski('#skF_5')) = k1_funct_1('#skF_7','#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4574,c_64])).

tff(c_19958,plain,(
    ! [A_7969] :
      ( A_7969 != '#skF_5'
      | '#skF_1'(k1_tarski(k1_funct_1('#skF_7','#skF_6')),k1_tarski('#skF_5')) = k1_funct_1('#skF_7','#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_18855])).

tff(c_20203,plain,(
    ! [A_7969] : A_7969 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_19958])).

tff(c_20211,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_20203])).

tff(c_20212,plain,(
    '#skF_1'(k1_tarski(k1_funct_1('#skF_7','#skF_6')),k1_tarski('#skF_5')) = k1_funct_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_19958])).

tff(c_20238,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_7','#skF_6'),k1_tarski('#skF_5'))
    | r1_tarski(k1_tarski(k1_funct_1('#skF_7','#skF_6')),k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_20212,c_4])).

tff(c_20616,plain,(
    ~ r2_hidden(k1_funct_1('#skF_7','#skF_6'),k1_tarski('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_20238])).

tff(c_20619,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_7'),k1_tarski('#skF_5'))
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_293,c_20616])).

tff(c_20622,plain,(
    ~ r1_tarski(k2_relat_1('#skF_7'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_72,c_66,c_376,c_20619])).

tff(c_20625,plain,
    ( ~ r2_hidden('#skF_5',k1_tarski('#skF_5'))
    | k1_funct_1('#skF_7','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_20506,c_20622])).

tff(c_20634,plain,(
    k1_funct_1('#skF_7','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_20625])).

tff(c_20636,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_20634])).

tff(c_20638,plain,(
    r2_hidden(k1_funct_1('#skF_7','#skF_6'),k1_tarski('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_20238])).

tff(c_20643,plain,(
    k1_funct_1('#skF_7','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_20638,c_10])).

tff(c_20648,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_20643])).

tff(c_20649,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_375])).

tff(c_75,plain,(
    ! [A_60] : k2_tarski(A_60,A_60) = k1_tarski(A_60) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_36,plain,(
    ! [A_39,B_40] : ~ v1_xboole_0(k2_tarski(A_39,B_40)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_80,plain,(
    ! [A_60] : ~ v1_xboole_0(k1_tarski(A_60)) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_36])).

tff(c_20692,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20649,c_80])).

tff(c_20703,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_20692])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:46:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.81/2.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.81/2.93  
% 8.81/2.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.81/2.94  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 8.81/2.94  
% 8.81/2.94  %Foreground sorts:
% 8.81/2.94  
% 8.81/2.94  
% 8.81/2.94  %Background operators:
% 8.81/2.94  
% 8.81/2.94  
% 8.81/2.94  %Foreground operators:
% 8.81/2.94  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.81/2.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.81/2.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.81/2.94  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.81/2.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.81/2.94  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.81/2.94  tff('#skF_7', type, '#skF_7': $i).
% 8.81/2.94  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.81/2.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.81/2.94  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.81/2.94  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.81/2.94  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.81/2.94  tff('#skF_5', type, '#skF_5': $i).
% 8.81/2.94  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.81/2.94  tff('#skF_6', type, '#skF_6': $i).
% 8.81/2.94  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.81/2.94  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.81/2.94  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.81/2.94  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.81/2.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.81/2.94  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.81/2.94  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.81/2.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.81/2.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.81/2.94  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.81/2.94  tff('#skF_4', type, '#skF_4': $i).
% 8.81/2.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.81/2.94  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.81/2.94  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.81/2.94  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.81/2.94  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.81/2.94  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.81/2.94  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.81/2.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.81/2.94  
% 8.81/2.95  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.81/2.95  tff(f_114, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 8.81/2.95  tff(f_40, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 8.81/2.95  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.81/2.95  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.81/2.95  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.81/2.95  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 8.81/2.95  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.81/2.95  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 8.81/2.95  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 8.81/2.95  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 8.81/2.95  tff(f_57, axiom, (![A, B]: ~v1_xboole_0(k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_xboole_0)).
% 8.81/2.95  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.81/2.95  tff(c_64, plain, (k1_funct_1('#skF_7', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_114])).
% 8.81/2.95  tff(c_12, plain, (![C_10]: (r2_hidden(C_10, k1_tarski(C_10)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.81/2.95  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.81/2.95  tff(c_108, plain, (![A_68, B_69]: (~r2_hidden('#skF_1'(A_68, B_69), B_69) | r1_tarski(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.81/2.95  tff(c_113, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_108])).
% 8.81/2.95  tff(c_66, plain, (r2_hidden('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_114])).
% 8.81/2.95  tff(c_140, plain, (![C_85, B_86, A_87]: (r2_hidden(C_85, B_86) | ~r2_hidden(C_85, A_87) | ~r1_tarski(A_87, B_86))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.81/2.95  tff(c_149, plain, (![B_86]: (r2_hidden('#skF_6', B_86) | ~r1_tarski('#skF_4', B_86))), inference(resolution, [status(thm)], [c_66, c_140])).
% 8.81/2.95  tff(c_68, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_tarski('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 8.81/2.95  tff(c_115, plain, (![C_71, A_72, B_73]: (v1_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.81/2.95  tff(c_119, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_68, c_115])).
% 8.81/2.95  tff(c_72, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_114])).
% 8.81/2.95  tff(c_70, plain, (v1_funct_2('#skF_7', '#skF_4', k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 8.81/2.95  tff(c_261, plain, (![A_120, B_121, C_122]: (k1_relset_1(A_120, B_121, C_122)=k1_relat_1(C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.81/2.95  tff(c_265, plain, (k1_relset_1('#skF_4', k1_tarski('#skF_5'), '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_68, c_261])).
% 8.81/2.95  tff(c_369, plain, (![B_161, A_162, C_163]: (k1_xboole_0=B_161 | k1_relset_1(A_162, B_161, C_163)=A_162 | ~v1_funct_2(C_163, A_162, B_161) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_162, B_161))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.81/2.95  tff(c_372, plain, (k1_tarski('#skF_5')=k1_xboole_0 | k1_relset_1('#skF_4', k1_tarski('#skF_5'), '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_68, c_369])).
% 8.81/2.95  tff(c_375, plain, (k1_tarski('#skF_5')=k1_xboole_0 | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_265, c_372])).
% 8.81/2.96  tff(c_376, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_375])).
% 8.81/2.96  tff(c_120, plain, (![C_74, B_75, A_76]: (v5_relat_1(C_74, B_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_76, B_75))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.81/2.96  tff(c_124, plain, (v5_relat_1('#skF_7', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_68, c_120])).
% 8.81/2.96  tff(c_40, plain, (![B_42, A_41]: (r1_tarski(k2_relat_1(B_42), A_41) | ~v5_relat_1(B_42, A_41) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.81/2.96  tff(c_219, plain, (![A_107, B_108, B_109]: (r2_hidden('#skF_1'(A_107, B_108), B_109) | ~r1_tarski(A_107, B_109) | r1_tarski(A_107, B_108))), inference(resolution, [status(thm)], [c_6, c_140])).
% 8.81/2.96  tff(c_10, plain, (![C_10, A_6]: (C_10=A_6 | ~r2_hidden(C_10, k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.81/2.96  tff(c_245, plain, (![A_112, A_113, B_114]: (A_112='#skF_1'(A_113, B_114) | ~r1_tarski(A_113, k1_tarski(A_112)) | r1_tarski(A_113, B_114))), inference(resolution, [status(thm)], [c_219, c_10])).
% 8.81/2.96  tff(c_363, plain, (![A_158, B_159, B_160]: (A_158='#skF_1'(k2_relat_1(B_159), B_160) | r1_tarski(k2_relat_1(B_159), B_160) | ~v5_relat_1(B_159, k1_tarski(A_158)) | ~v1_relat_1(B_159))), inference(resolution, [status(thm)], [c_40, c_245])).
% 8.81/2.96  tff(c_365, plain, (![B_160]: ('#skF_1'(k2_relat_1('#skF_7'), B_160)='#skF_5' | r1_tarski(k2_relat_1('#skF_7'), B_160) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_124, c_363])).
% 8.81/2.96  tff(c_368, plain, (![B_160]: ('#skF_1'(k2_relat_1('#skF_7'), B_160)='#skF_5' | r1_tarski(k2_relat_1('#skF_7'), B_160))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_365])).
% 8.81/2.96  tff(c_290, plain, (![B_134, A_135]: (r2_hidden(k1_funct_1(B_134, A_135), k2_relat_1(B_134)) | ~r2_hidden(A_135, k1_relat_1(B_134)) | ~v1_funct_1(B_134) | ~v1_relat_1(B_134))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.81/2.96  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.81/2.96  tff(c_20374, plain, (![B_16192, A_16193, B_16194]: (r2_hidden(k1_funct_1(B_16192, A_16193), B_16194) | ~r1_tarski(k2_relat_1(B_16192), B_16194) | ~r2_hidden(A_16193, k1_relat_1(B_16192)) | ~v1_funct_1(B_16192) | ~v1_relat_1(B_16192))), inference(resolution, [status(thm)], [c_290, c_2])).
% 8.81/2.96  tff(c_20389, plain, (![B_16299, A_16300, A_16301]: (k1_funct_1(B_16299, A_16300)=A_16301 | ~r1_tarski(k2_relat_1(B_16299), k1_tarski(A_16301)) | ~r2_hidden(A_16300, k1_relat_1(B_16299)) | ~v1_funct_1(B_16299) | ~v1_relat_1(B_16299))), inference(resolution, [status(thm)], [c_20374, c_10])).
% 8.81/2.96  tff(c_20404, plain, (![A_16300, A_16301]: (k1_funct_1('#skF_7', A_16300)=A_16301 | ~r2_hidden(A_16300, k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | '#skF_1'(k2_relat_1('#skF_7'), k1_tarski(A_16301))='#skF_5')), inference(resolution, [status(thm)], [c_368, c_20389])).
% 8.81/2.96  tff(c_20412, plain, (![A_16406, A_16407]: (k1_funct_1('#skF_7', A_16406)=A_16407 | ~r2_hidden(A_16406, '#skF_4') | '#skF_1'(k2_relat_1('#skF_7'), k1_tarski(A_16407))='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_119, c_72, c_376, c_20404])).
% 8.81/2.96  tff(c_20474, plain, (![A_16407]: (k1_funct_1('#skF_7', '#skF_6')=A_16407 | '#skF_1'(k2_relat_1('#skF_7'), k1_tarski(A_16407))='#skF_5' | ~r1_tarski('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_149, c_20412])).
% 8.81/2.96  tff(c_20491, plain, (![A_16512]: (k1_funct_1('#skF_7', '#skF_6')=A_16512 | '#skF_1'(k2_relat_1('#skF_7'), k1_tarski(A_16512))='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_20474])).
% 8.81/2.96  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.81/2.96  tff(c_20506, plain, (![A_16512]: (~r2_hidden('#skF_5', k1_tarski(A_16512)) | r1_tarski(k2_relat_1('#skF_7'), k1_tarski(A_16512)) | k1_funct_1('#skF_7', '#skF_6')=A_16512)), inference(superposition, [status(thm), theory('equality')], [c_20491, c_4])).
% 8.81/2.96  tff(c_293, plain, (![B_134, A_135, B_2]: (r2_hidden(k1_funct_1(B_134, A_135), B_2) | ~r1_tarski(k2_relat_1(B_134), B_2) | ~r2_hidden(A_135, k1_relat_1(B_134)) | ~v1_funct_1(B_134) | ~v1_relat_1(B_134))), inference(resolution, [status(thm)], [c_290, c_2])).
% 8.81/2.96  tff(c_102, plain, (![A_66, B_67]: (r2_hidden('#skF_1'(A_66, B_67), A_66) | r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.81/2.96  tff(c_107, plain, (![A_6, B_67]: ('#skF_1'(k1_tarski(A_6), B_67)=A_6 | r1_tarski(k1_tarski(A_6), B_67))), inference(resolution, [status(thm)], [c_102, c_10])).
% 8.81/2.96  tff(c_538, plain, (![A_180, A_181, B_182]: (A_180='#skF_1'(k1_tarski(A_181), B_182) | r1_tarski(k1_tarski(A_181), B_182) | '#skF_1'(k1_tarski(A_181), k1_tarski(A_180))=A_181)), inference(resolution, [status(thm)], [c_107, c_245])).
% 8.81/2.96  tff(c_148, plain, (![C_10, B_86]: (r2_hidden(C_10, B_86) | ~r1_tarski(k1_tarski(C_10), B_86))), inference(resolution, [status(thm)], [c_12, c_140])).
% 8.81/2.96  tff(c_2683, plain, (![A_3903, B_3904]: (r2_hidden(A_3903, B_3904) | '#skF_1'(k1_tarski(A_3903), B_3904)='#skF_5' | '#skF_1'(k1_tarski(A_3903), k1_tarski('#skF_5'))=A_3903)), inference(resolution, [status(thm)], [c_538, c_148])).
% 8.81/2.96  tff(c_185, plain, (![A_97, B_98]: ('#skF_1'(k1_tarski(A_97), B_98)=A_97 | r1_tarski(k1_tarski(A_97), B_98))), inference(resolution, [status(thm)], [c_102, c_10])).
% 8.81/2.96  tff(c_192, plain, (![A_97, B_98]: (r2_hidden(A_97, B_98) | '#skF_1'(k1_tarski(A_97), B_98)=A_97)), inference(resolution, [status(thm)], [c_185, c_148])).
% 8.81/2.96  tff(c_2686, plain, (![A_3903, B_3904]: (r2_hidden(A_3903, B_3904) | A_3903='#skF_5' | r2_hidden(A_3903, B_3904) | '#skF_1'(k1_tarski(A_3903), k1_tarski('#skF_5'))=A_3903)), inference(superposition, [status(thm), theory('equality')], [c_2683, c_192])).
% 8.81/2.96  tff(c_3761, plain, (![A_7756, B_7757]: (A_7756='#skF_5' | '#skF_1'(k1_tarski(A_7756), k1_tarski('#skF_5'))=A_7756 | r2_hidden(A_7756, B_7757))), inference(factorization, [status(thm), theory('equality')], [c_2686])).
% 8.81/2.96  tff(c_4574, plain, (![A_7969, A_7968]: (A_7969=A_7968 | A_7968='#skF_5' | '#skF_1'(k1_tarski(A_7968), k1_tarski('#skF_5'))=A_7968)), inference(resolution, [status(thm)], [c_3761, c_10])).
% 8.81/2.96  tff(c_18855, plain, (![A_7969]: (A_7969!='#skF_5' | k1_funct_1('#skF_7', '#skF_6')='#skF_5' | '#skF_1'(k1_tarski(k1_funct_1('#skF_7', '#skF_6')), k1_tarski('#skF_5'))=k1_funct_1('#skF_7', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_4574, c_64])).
% 8.81/2.96  tff(c_19958, plain, (![A_7969]: (A_7969!='#skF_5' | '#skF_1'(k1_tarski(k1_funct_1('#skF_7', '#skF_6')), k1_tarski('#skF_5'))=k1_funct_1('#skF_7', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_64, c_18855])).
% 8.81/2.96  tff(c_20203, plain, (![A_7969]: (A_7969!='#skF_5')), inference(splitLeft, [status(thm)], [c_19958])).
% 8.81/2.96  tff(c_20211, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_20203])).
% 8.81/2.96  tff(c_20212, plain, ('#skF_1'(k1_tarski(k1_funct_1('#skF_7', '#skF_6')), k1_tarski('#skF_5'))=k1_funct_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_19958])).
% 8.81/2.96  tff(c_20238, plain, (~r2_hidden(k1_funct_1('#skF_7', '#skF_6'), k1_tarski('#skF_5')) | r1_tarski(k1_tarski(k1_funct_1('#skF_7', '#skF_6')), k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_20212, c_4])).
% 8.81/2.96  tff(c_20616, plain, (~r2_hidden(k1_funct_1('#skF_7', '#skF_6'), k1_tarski('#skF_5'))), inference(splitLeft, [status(thm)], [c_20238])).
% 8.81/2.96  tff(c_20619, plain, (~r1_tarski(k2_relat_1('#skF_7'), k1_tarski('#skF_5')) | ~r2_hidden('#skF_6', k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_293, c_20616])).
% 8.81/2.96  tff(c_20622, plain, (~r1_tarski(k2_relat_1('#skF_7'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_72, c_66, c_376, c_20619])).
% 8.81/2.96  tff(c_20625, plain, (~r2_hidden('#skF_5', k1_tarski('#skF_5')) | k1_funct_1('#skF_7', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_20506, c_20622])).
% 8.81/2.96  tff(c_20634, plain, (k1_funct_1('#skF_7', '#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_20625])).
% 8.81/2.96  tff(c_20636, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_20634])).
% 8.81/2.96  tff(c_20638, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_6'), k1_tarski('#skF_5'))), inference(splitRight, [status(thm)], [c_20238])).
% 8.81/2.96  tff(c_20643, plain, (k1_funct_1('#skF_7', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_20638, c_10])).
% 8.81/2.96  tff(c_20648, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_20643])).
% 8.81/2.96  tff(c_20649, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_375])).
% 8.81/2.96  tff(c_75, plain, (![A_60]: (k2_tarski(A_60, A_60)=k1_tarski(A_60))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.81/2.96  tff(c_36, plain, (![A_39, B_40]: (~v1_xboole_0(k2_tarski(A_39, B_40)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.81/2.96  tff(c_80, plain, (![A_60]: (~v1_xboole_0(k1_tarski(A_60)))), inference(superposition, [status(thm), theory('equality')], [c_75, c_36])).
% 8.81/2.96  tff(c_20692, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20649, c_80])).
% 8.81/2.96  tff(c_20703, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_20692])).
% 8.81/2.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.81/2.96  
% 8.81/2.96  Inference rules
% 8.81/2.96  ----------------------
% 8.81/2.96  #Ref     : 1
% 8.81/2.96  #Sup     : 2976
% 8.81/2.96  #Fact    : 7
% 8.81/2.96  #Define  : 0
% 8.81/2.96  #Split   : 5
% 8.81/2.96  #Chain   : 0
% 8.81/2.96  #Close   : 0
% 8.81/2.96  
% 8.81/2.96  Ordering : KBO
% 8.81/2.96  
% 8.81/2.96  Simplification rules
% 8.81/2.96  ----------------------
% 8.81/2.96  #Subsume      : 833
% 8.81/2.96  #Demod        : 489
% 8.81/2.96  #Tautology    : 151
% 8.81/2.96  #SimpNegUnit  : 9
% 8.81/2.96  #BackRed      : 9
% 8.81/2.96  
% 8.81/2.96  #Partial instantiations: 7084
% 8.81/2.96  #Strategies tried      : 1
% 8.81/2.96  
% 8.81/2.96  Timing (in seconds)
% 8.81/2.96  ----------------------
% 8.81/2.96  Preprocessing        : 0.34
% 8.81/2.96  Parsing              : 0.17
% 8.81/2.96  CNF conversion       : 0.02
% 8.81/2.96  Main loop            : 1.86
% 8.81/2.96  Inferencing          : 0.71
% 8.81/2.96  Reduction            : 0.47
% 8.81/2.96  Demodulation         : 0.33
% 8.81/2.96  BG Simplification    : 0.11
% 8.81/2.96  Subsumption          : 0.47
% 8.81/2.96  Abstraction          : 0.13
% 8.81/2.96  MUC search           : 0.00
% 8.81/2.96  Cooper               : 0.00
% 8.81/2.96  Total                : 2.23
% 8.81/2.96  Index Insertion      : 0.00
% 8.81/2.96  Index Deletion       : 0.00
% 8.81/2.96  Index Matching       : 0.00
% 8.81/2.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
