%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:33 EST 2020

% Result     : Theorem 3.43s
% Output     : CNFRefutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 362 expanded)
%              Number of leaves         :   44 ( 139 expanded)
%              Depth                    :   13
%              Number of atoms          :  204 ( 786 expanded)
%              Number of equality atoms :   93 ( 355 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k3_mcart_1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_145,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_30,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_58,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_121,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_133,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_91,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_66,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_210,plain,(
    ! [C_77,A_78,B_79] :
      ( v1_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_214,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_210])).

tff(c_70,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_32,plain,(
    ! [A_13] :
      ( k1_relat_1(A_13) != k1_xboole_0
      | k1_xboole_0 = A_13
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_222,plain,
    ( k1_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_214,c_32])).

tff(c_224,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_222])).

tff(c_404,plain,(
    ! [B_134,A_135] :
      ( k1_tarski(k1_funct_1(B_134,A_135)) = k2_relat_1(B_134)
      | k1_tarski(A_135) != k1_relat_1(B_134)
      | ~ v1_funct_1(B_134)
      | ~ v1_relat_1(B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_394,plain,(
    ! [A_131,B_132,C_133] :
      ( k2_relset_1(A_131,B_132,C_133) = k2_relat_1(C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_398,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_394])).

tff(c_62,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') != k1_tarski(k1_funct_1('#skF_5','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_399,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_3')) != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_398,c_62])).

tff(c_410,plain,
    ( k1_tarski('#skF_3') != k1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_404,c_399])).

tff(c_432,plain,(
    k1_tarski('#skF_3') != k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_70,c_410])).

tff(c_273,plain,(
    ! [C_96,A_97,B_98] :
      ( v4_relat_1(C_96,A_97)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_277,plain,(
    v4_relat_1('#skF_5',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_66,c_273])).

tff(c_24,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(B_12),A_11)
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_458,plain,(
    ! [B_141,C_142,A_143] :
      ( k2_tarski(B_141,C_142) = A_143
      | k1_tarski(C_142) = A_143
      | k1_tarski(B_141) = A_143
      | k1_xboole_0 = A_143
      | ~ r1_tarski(A_143,k2_tarski(B_141,C_142)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_478,plain,(
    ! [A_2,A_143] :
      ( k2_tarski(A_2,A_2) = A_143
      | k1_tarski(A_2) = A_143
      | k1_tarski(A_2) = A_143
      | k1_xboole_0 = A_143
      | ~ r1_tarski(A_143,k1_tarski(A_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_458])).

tff(c_491,plain,(
    ! [A_146,A_147] :
      ( k1_tarski(A_146) = A_147
      | k1_tarski(A_146) = A_147
      | k1_tarski(A_146) = A_147
      | k1_xboole_0 = A_147
      | ~ r1_tarski(A_147,k1_tarski(A_146)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_478])).

tff(c_510,plain,(
    ! [A_148,B_149] :
      ( k1_tarski(A_148) = k1_relat_1(B_149)
      | k1_relat_1(B_149) = k1_xboole_0
      | ~ v4_relat_1(B_149,k1_tarski(A_148))
      | ~ v1_relat_1(B_149) ) ),
    inference(resolution,[status(thm)],[c_24,c_491])).

tff(c_528,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_5')
    | k1_relat_1('#skF_5') = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_277,c_510])).

tff(c_538,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_5')
    | k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_528])).

tff(c_540,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_432,c_538])).

tff(c_541,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_551,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_541,c_26])).

tff(c_30,plain,(
    ! [A_13] :
      ( k2_relat_1(A_13) != k1_xboole_0
      | k1_xboole_0 = A_13
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_221,plain,
    ( k2_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_214,c_30])).

tff(c_223,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_543,plain,(
    k2_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_223])).

tff(c_588,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_551,c_543])).

tff(c_589,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_600,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_589,c_589,c_28])).

tff(c_598,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_589,c_589,c_26])).

tff(c_42,plain,(
    ! [B_22,A_21] :
      ( k1_tarski(k1_funct_1(B_22,A_21)) = k2_relat_1(B_22)
      | k1_tarski(A_21) != k1_relat_1(B_22)
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_853,plain,(
    ! [A_209,B_210,C_211] :
      ( k2_relset_1(A_209,B_210,C_211) = k2_relat_1(C_211)
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1(A_209,B_210))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_856,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_853])).

tff(c_858,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_598,c_856])).

tff(c_885,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_3')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_858,c_62])).

tff(c_892,plain,
    ( k2_relat_1('#skF_5') != '#skF_5'
    | k1_tarski('#skF_3') != k1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_885])).

tff(c_894,plain,(
    k1_tarski('#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_70,c_600,c_598,c_892])).

tff(c_54,plain,(
    ! [A_34] :
      ( r2_hidden('#skF_2'(A_34),A_34)
      | k1_xboole_0 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_597,plain,(
    ! [A_34] :
      ( r2_hidden('#skF_2'(A_34),A_34)
      | A_34 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_589,c_54])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_599,plain,(
    ! [A_1] : r1_tarski('#skF_5',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_589,c_4])).

tff(c_704,plain,(
    ! [B_169,A_170] :
      ( v4_relat_1(B_169,A_170)
      | ~ r1_tarski(k1_relat_1(B_169),A_170)
      | ~ v1_relat_1(B_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_707,plain,(
    ! [A_170] :
      ( v4_relat_1('#skF_5',A_170)
      | ~ r1_tarski('#skF_5',A_170)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_600,c_704])).

tff(c_712,plain,(
    ! [A_170] : v4_relat_1('#skF_5',A_170) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_599,c_707])).

tff(c_36,plain,(
    ! [A_14,B_15] : k1_relat_1('#skF_1'(A_14,B_15)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_40,plain,(
    ! [A_14,B_15] : v1_relat_1('#skF_1'(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_137,plain,(
    ! [A_71] :
      ( k1_relat_1(A_71) != k1_xboole_0
      | k1_xboole_0 = A_71
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_140,plain,(
    ! [A_14,B_15] :
      ( k1_relat_1('#skF_1'(A_14,B_15)) != k1_xboole_0
      | '#skF_1'(A_14,B_15) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_137])).

tff(c_142,plain,(
    ! [A_14,B_15] :
      ( k1_xboole_0 != A_14
      | '#skF_1'(A_14,B_15) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_140])).

tff(c_594,plain,(
    ! [A_14,B_15] :
      ( A_14 != '#skF_5'
      | '#skF_1'(A_14,B_15) = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_589,c_589,c_142])).

tff(c_731,plain,(
    ! [B_178,A_179] :
      ( r1_tarski(k1_relat_1(B_178),A_179)
      | ~ v4_relat_1(B_178,A_179)
      | ~ v1_relat_1(B_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_744,plain,(
    ! [A_14,A_179,B_15] :
      ( r1_tarski(A_14,A_179)
      | ~ v4_relat_1('#skF_1'(A_14,B_15),A_179)
      | ~ v1_relat_1('#skF_1'(A_14,B_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_731])).

tff(c_751,plain,(
    ! [A_180,A_181,B_182] :
      ( r1_tarski(A_180,A_181)
      | ~ v4_relat_1('#skF_1'(A_180,B_182),A_181) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_744])).

tff(c_757,plain,(
    ! [A_14,A_181] :
      ( r1_tarski(A_14,A_181)
      | ~ v4_relat_1('#skF_5',A_181)
      | A_14 != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_594,c_751])).

tff(c_761,plain,(
    ! [A_181] : r1_tarski('#skF_5',A_181) ),
    inference(demodulation,[status(thm),theory(equality)],[c_712,c_757])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_602,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_589,c_64])).

tff(c_68,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_60,plain,(
    ! [D_51,C_50,A_48,B_49] :
      ( r2_hidden(k1_funct_1(D_51,C_50),k2_relset_1(A_48,B_49,D_51))
      | k1_xboole_0 = B_49
      | ~ r2_hidden(C_50,A_48)
      | ~ m1_subset_1(D_51,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ v1_funct_2(D_51,A_48,B_49)
      | ~ v1_funct_1(D_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_978,plain,(
    ! [D_227,C_228,A_229,B_230] :
      ( r2_hidden(k1_funct_1(D_227,C_228),k2_relset_1(A_229,B_230,D_227))
      | B_230 = '#skF_5'
      | ~ r2_hidden(C_228,A_229)
      | ~ m1_subset_1(D_227,k1_zfmisc_1(k2_zfmisc_1(A_229,B_230)))
      | ~ v1_funct_2(D_227,A_229,B_230)
      | ~ v1_funct_1(D_227) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_589,c_60])).

tff(c_992,plain,(
    ! [C_228] :
      ( r2_hidden(k1_funct_1('#skF_5',C_228),'#skF_5')
      | '#skF_5' = '#skF_4'
      | ~ r2_hidden(C_228,k1_tarski('#skF_3'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4')))
      | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_858,c_978])).

tff(c_1002,plain,(
    ! [C_228] :
      ( r2_hidden(k1_funct_1('#skF_5',C_228),'#skF_5')
      | '#skF_5' = '#skF_4'
      | ~ r2_hidden(C_228,k1_tarski('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_992])).

tff(c_1006,plain,(
    ! [C_231] :
      ( r2_hidden(k1_funct_1('#skF_5',C_231),'#skF_5')
      | ~ r2_hidden(C_231,k1_tarski('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_602,c_1002])).

tff(c_44,plain,(
    ! [B_24,A_23] :
      ( ~ r1_tarski(B_24,A_23)
      | ~ r2_hidden(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1017,plain,(
    ! [C_231] :
      ( ~ r1_tarski('#skF_5',k1_funct_1('#skF_5',C_231))
      | ~ r2_hidden(C_231,k1_tarski('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1006,c_44])).

tff(c_1028,plain,(
    ! [C_232] : ~ r2_hidden(C_232,k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_761,c_1017])).

tff(c_1032,plain,(
    k1_tarski('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_597,c_1028])).

tff(c_1036,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_894,c_1032])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:19:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.43/1.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/1.76  
% 3.73/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/1.77  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k3_mcart_1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 3.73/1.77  
% 3.73/1.77  %Foreground sorts:
% 3.73/1.77  
% 3.73/1.77  
% 3.73/1.77  %Background operators:
% 3.73/1.77  
% 3.73/1.77  
% 3.73/1.77  %Foreground operators:
% 3.73/1.77  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.73/1.77  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 3.73/1.77  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.73/1.77  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.73/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.73/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.73/1.77  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.73/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.73/1.77  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.73/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.73/1.77  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.73/1.77  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.73/1.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.73/1.77  tff('#skF_5', type, '#skF_5': $i).
% 3.73/1.77  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.73/1.77  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.73/1.77  tff('#skF_3', type, '#skF_3': $i).
% 3.73/1.77  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.73/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.73/1.77  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.73/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.73/1.77  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.73/1.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.73/1.77  tff('#skF_4', type, '#skF_4': $i).
% 3.73/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.73/1.77  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.73/1.77  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.73/1.77  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.73/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.73/1.77  
% 3.80/1.78  tff(f_145, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 3.80/1.78  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.80/1.78  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.80/1.78  tff(f_86, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.80/1.78  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.80/1.78  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.80/1.78  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.80/1.78  tff(f_30, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.80/1.78  tff(f_49, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.80/1.78  tff(f_58, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.80/1.78  tff(f_121, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 3.80/1.78  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.80/1.78  tff(f_78, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 3.80/1.78  tff(f_133, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 3.80/1.78  tff(f_91, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.80/1.78  tff(c_66, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.80/1.78  tff(c_210, plain, (![C_77, A_78, B_79]: (v1_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.80/1.78  tff(c_214, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_210])).
% 3.80/1.78  tff(c_70, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.80/1.78  tff(c_32, plain, (![A_13]: (k1_relat_1(A_13)!=k1_xboole_0 | k1_xboole_0=A_13 | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.80/1.78  tff(c_222, plain, (k1_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_214, c_32])).
% 3.80/1.78  tff(c_224, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_222])).
% 3.80/1.78  tff(c_404, plain, (![B_134, A_135]: (k1_tarski(k1_funct_1(B_134, A_135))=k2_relat_1(B_134) | k1_tarski(A_135)!=k1_relat_1(B_134) | ~v1_funct_1(B_134) | ~v1_relat_1(B_134))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.80/1.78  tff(c_394, plain, (![A_131, B_132, C_133]: (k2_relset_1(A_131, B_132, C_133)=k2_relat_1(C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.80/1.78  tff(c_398, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_394])).
% 3.80/1.78  tff(c_62, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')!=k1_tarski(k1_funct_1('#skF_5', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.80/1.78  tff(c_399, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_398, c_62])).
% 3.80/1.78  tff(c_410, plain, (k1_tarski('#skF_3')!=k1_relat_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_404, c_399])).
% 3.80/1.78  tff(c_432, plain, (k1_tarski('#skF_3')!=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_214, c_70, c_410])).
% 3.80/1.78  tff(c_273, plain, (![C_96, A_97, B_98]: (v4_relat_1(C_96, A_97) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.80/1.78  tff(c_277, plain, (v4_relat_1('#skF_5', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_66, c_273])).
% 3.80/1.78  tff(c_24, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(B_12), A_11) | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.80/1.78  tff(c_6, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.80/1.78  tff(c_458, plain, (![B_141, C_142, A_143]: (k2_tarski(B_141, C_142)=A_143 | k1_tarski(C_142)=A_143 | k1_tarski(B_141)=A_143 | k1_xboole_0=A_143 | ~r1_tarski(A_143, k2_tarski(B_141, C_142)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.80/1.78  tff(c_478, plain, (![A_2, A_143]: (k2_tarski(A_2, A_2)=A_143 | k1_tarski(A_2)=A_143 | k1_tarski(A_2)=A_143 | k1_xboole_0=A_143 | ~r1_tarski(A_143, k1_tarski(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_458])).
% 3.80/1.78  tff(c_491, plain, (![A_146, A_147]: (k1_tarski(A_146)=A_147 | k1_tarski(A_146)=A_147 | k1_tarski(A_146)=A_147 | k1_xboole_0=A_147 | ~r1_tarski(A_147, k1_tarski(A_146)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_478])).
% 3.80/1.78  tff(c_510, plain, (![A_148, B_149]: (k1_tarski(A_148)=k1_relat_1(B_149) | k1_relat_1(B_149)=k1_xboole_0 | ~v4_relat_1(B_149, k1_tarski(A_148)) | ~v1_relat_1(B_149))), inference(resolution, [status(thm)], [c_24, c_491])).
% 3.80/1.78  tff(c_528, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_5') | k1_relat_1('#skF_5')=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_277, c_510])).
% 3.80/1.78  tff(c_538, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_5') | k1_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_214, c_528])).
% 3.80/1.78  tff(c_540, plain, $false, inference(negUnitSimplification, [status(thm)], [c_224, c_432, c_538])).
% 3.80/1.78  tff(c_541, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_222])).
% 3.80/1.78  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.80/1.78  tff(c_551, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_541, c_541, c_26])).
% 3.80/1.78  tff(c_30, plain, (![A_13]: (k2_relat_1(A_13)!=k1_xboole_0 | k1_xboole_0=A_13 | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.80/1.78  tff(c_221, plain, (k2_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_214, c_30])).
% 3.80/1.78  tff(c_223, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_221])).
% 3.80/1.78  tff(c_543, plain, (k2_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_541, c_223])).
% 3.80/1.78  tff(c_588, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_551, c_543])).
% 3.80/1.78  tff(c_589, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_221])).
% 3.80/1.78  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.80/1.78  tff(c_600, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_589, c_589, c_28])).
% 3.80/1.78  tff(c_598, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_589, c_589, c_26])).
% 3.80/1.78  tff(c_42, plain, (![B_22, A_21]: (k1_tarski(k1_funct_1(B_22, A_21))=k2_relat_1(B_22) | k1_tarski(A_21)!=k1_relat_1(B_22) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.80/1.78  tff(c_853, plain, (![A_209, B_210, C_211]: (k2_relset_1(A_209, B_210, C_211)=k2_relat_1(C_211) | ~m1_subset_1(C_211, k1_zfmisc_1(k2_zfmisc_1(A_209, B_210))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.80/1.78  tff(c_856, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_853])).
% 3.80/1.78  tff(c_858, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_598, c_856])).
% 3.80/1.78  tff(c_885, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_858, c_62])).
% 3.80/1.78  tff(c_892, plain, (k2_relat_1('#skF_5')!='#skF_5' | k1_tarski('#skF_3')!=k1_relat_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_42, c_885])).
% 3.80/1.78  tff(c_894, plain, (k1_tarski('#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_214, c_70, c_600, c_598, c_892])).
% 3.80/1.78  tff(c_54, plain, (![A_34]: (r2_hidden('#skF_2'(A_34), A_34) | k1_xboole_0=A_34)), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.80/1.78  tff(c_597, plain, (![A_34]: (r2_hidden('#skF_2'(A_34), A_34) | A_34='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_589, c_54])).
% 3.80/1.78  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.80/1.78  tff(c_599, plain, (![A_1]: (r1_tarski('#skF_5', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_589, c_4])).
% 3.80/1.78  tff(c_704, plain, (![B_169, A_170]: (v4_relat_1(B_169, A_170) | ~r1_tarski(k1_relat_1(B_169), A_170) | ~v1_relat_1(B_169))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.80/1.78  tff(c_707, plain, (![A_170]: (v4_relat_1('#skF_5', A_170) | ~r1_tarski('#skF_5', A_170) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_600, c_704])).
% 3.80/1.78  tff(c_712, plain, (![A_170]: (v4_relat_1('#skF_5', A_170))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_599, c_707])).
% 3.80/1.78  tff(c_36, plain, (![A_14, B_15]: (k1_relat_1('#skF_1'(A_14, B_15))=A_14)), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.80/1.78  tff(c_40, plain, (![A_14, B_15]: (v1_relat_1('#skF_1'(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.80/1.78  tff(c_137, plain, (![A_71]: (k1_relat_1(A_71)!=k1_xboole_0 | k1_xboole_0=A_71 | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.80/1.78  tff(c_140, plain, (![A_14, B_15]: (k1_relat_1('#skF_1'(A_14, B_15))!=k1_xboole_0 | '#skF_1'(A_14, B_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_137])).
% 3.80/1.78  tff(c_142, plain, (![A_14, B_15]: (k1_xboole_0!=A_14 | '#skF_1'(A_14, B_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_140])).
% 3.80/1.78  tff(c_594, plain, (![A_14, B_15]: (A_14!='#skF_5' | '#skF_1'(A_14, B_15)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_589, c_589, c_142])).
% 3.80/1.78  tff(c_731, plain, (![B_178, A_179]: (r1_tarski(k1_relat_1(B_178), A_179) | ~v4_relat_1(B_178, A_179) | ~v1_relat_1(B_178))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.80/1.78  tff(c_744, plain, (![A_14, A_179, B_15]: (r1_tarski(A_14, A_179) | ~v4_relat_1('#skF_1'(A_14, B_15), A_179) | ~v1_relat_1('#skF_1'(A_14, B_15)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_731])).
% 3.80/1.78  tff(c_751, plain, (![A_180, A_181, B_182]: (r1_tarski(A_180, A_181) | ~v4_relat_1('#skF_1'(A_180, B_182), A_181))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_744])).
% 3.80/1.78  tff(c_757, plain, (![A_14, A_181]: (r1_tarski(A_14, A_181) | ~v4_relat_1('#skF_5', A_181) | A_14!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_594, c_751])).
% 3.80/1.78  tff(c_761, plain, (![A_181]: (r1_tarski('#skF_5', A_181))), inference(demodulation, [status(thm), theory('equality')], [c_712, c_757])).
% 3.80/1.78  tff(c_64, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.80/1.78  tff(c_602, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_589, c_64])).
% 3.80/1.78  tff(c_68, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.80/1.78  tff(c_60, plain, (![D_51, C_50, A_48, B_49]: (r2_hidden(k1_funct_1(D_51, C_50), k2_relset_1(A_48, B_49, D_51)) | k1_xboole_0=B_49 | ~r2_hidden(C_50, A_48) | ~m1_subset_1(D_51, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | ~v1_funct_2(D_51, A_48, B_49) | ~v1_funct_1(D_51))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.80/1.78  tff(c_978, plain, (![D_227, C_228, A_229, B_230]: (r2_hidden(k1_funct_1(D_227, C_228), k2_relset_1(A_229, B_230, D_227)) | B_230='#skF_5' | ~r2_hidden(C_228, A_229) | ~m1_subset_1(D_227, k1_zfmisc_1(k2_zfmisc_1(A_229, B_230))) | ~v1_funct_2(D_227, A_229, B_230) | ~v1_funct_1(D_227))), inference(demodulation, [status(thm), theory('equality')], [c_589, c_60])).
% 3.80/1.78  tff(c_992, plain, (![C_228]: (r2_hidden(k1_funct_1('#skF_5', C_228), '#skF_5') | '#skF_5'='#skF_4' | ~r2_hidden(C_228, k1_tarski('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'))) | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4') | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_858, c_978])).
% 3.80/1.78  tff(c_1002, plain, (![C_228]: (r2_hidden(k1_funct_1('#skF_5', C_228), '#skF_5') | '#skF_5'='#skF_4' | ~r2_hidden(C_228, k1_tarski('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_992])).
% 3.80/1.78  tff(c_1006, plain, (![C_231]: (r2_hidden(k1_funct_1('#skF_5', C_231), '#skF_5') | ~r2_hidden(C_231, k1_tarski('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_602, c_1002])).
% 3.80/1.78  tff(c_44, plain, (![B_24, A_23]: (~r1_tarski(B_24, A_23) | ~r2_hidden(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.80/1.78  tff(c_1017, plain, (![C_231]: (~r1_tarski('#skF_5', k1_funct_1('#skF_5', C_231)) | ~r2_hidden(C_231, k1_tarski('#skF_3')))), inference(resolution, [status(thm)], [c_1006, c_44])).
% 3.80/1.78  tff(c_1028, plain, (![C_232]: (~r2_hidden(C_232, k1_tarski('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_761, c_1017])).
% 3.80/1.78  tff(c_1032, plain, (k1_tarski('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_597, c_1028])).
% 3.80/1.78  tff(c_1036, plain, $false, inference(negUnitSimplification, [status(thm)], [c_894, c_1032])).
% 3.80/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.78  
% 3.80/1.78  Inference rules
% 3.80/1.78  ----------------------
% 3.80/1.78  #Ref     : 0
% 3.80/1.78  #Sup     : 194
% 3.80/1.78  #Fact    : 0
% 3.80/1.78  #Define  : 0
% 3.80/1.78  #Split   : 4
% 3.80/1.78  #Chain   : 0
% 3.80/1.78  #Close   : 0
% 3.80/1.78  
% 3.80/1.79  Ordering : KBO
% 3.80/1.79  
% 3.80/1.79  Simplification rules
% 3.80/1.79  ----------------------
% 3.80/1.79  #Subsume      : 19
% 3.80/1.79  #Demod        : 171
% 3.80/1.79  #Tautology    : 116
% 3.80/1.79  #SimpNegUnit  : 18
% 3.80/1.79  #BackRed      : 38
% 3.80/1.79  
% 3.80/1.79  #Partial instantiations: 0
% 3.80/1.79  #Strategies tried      : 1
% 3.80/1.79  
% 3.80/1.79  Timing (in seconds)
% 3.80/1.79  ----------------------
% 3.80/1.79  Preprocessing        : 0.50
% 3.80/1.79  Parsing              : 0.29
% 3.80/1.79  CNF conversion       : 0.03
% 3.80/1.79  Main loop            : 0.47
% 3.80/1.79  Inferencing          : 0.17
% 3.80/1.79  Reduction            : 0.16
% 3.80/1.79  Demodulation         : 0.11
% 3.80/1.79  BG Simplification    : 0.03
% 3.80/1.79  Subsumption          : 0.07
% 3.80/1.79  Abstraction          : 0.02
% 3.80/1.79  MUC search           : 0.00
% 3.80/1.79  Cooper               : 0.00
% 3.80/1.79  Total                : 1.01
% 3.80/1.79  Index Insertion      : 0.00
% 3.80/1.79  Index Deletion       : 0.00
% 3.80/1.79  Index Matching       : 0.00
% 3.80/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
