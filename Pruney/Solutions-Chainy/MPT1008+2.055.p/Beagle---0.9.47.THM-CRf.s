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

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 296 expanded)
%              Number of leaves         :   43 ( 116 expanded)
%              Depth                    :   13
%              Number of atoms          :  202 ( 652 expanded)
%              Number of equality atoms :  110 ( 310 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_mcart_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_149,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_60,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_69,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_125,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_137,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_95,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_220,plain,(
    ! [C_90,A_91,B_92] :
      ( v1_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_224,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_220])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_38,plain,(
    ! [A_14] :
      ( k1_relat_1(A_14) != k1_xboole_0
      | k1_xboole_0 = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_232,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_224,c_38])).

tff(c_245,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_232])).

tff(c_318,plain,(
    ! [B_132,A_133] :
      ( k1_tarski(k1_funct_1(B_132,A_133)) = k2_relat_1(B_132)
      | k1_tarski(A_133) != k1_relat_1(B_132)
      | ~ v1_funct_1(B_132)
      | ~ v1_relat_1(B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_298,plain,(
    ! [A_111,B_112,C_113] :
      ( k2_relset_1(A_111,B_112,C_113) = k2_relat_1(C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_302,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_298])).

tff(c_66,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') != k1_tarski(k1_funct_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_303,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_66])).

tff(c_324,plain,
    ( k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_303])).

tff(c_352,plain,(
    k1_tarski('#skF_2') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_74,c_324])).

tff(c_251,plain,(
    ! [C_98,A_99,B_100] :
      ( v4_relat_1(C_98,A_99)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_255,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_70,c_251])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k1_relat_1(B_13),A_12)
      | ~ v4_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [A_3,B_4] : k1_enumset1(A_3,A_3,B_4) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_414,plain,(
    ! [A_153,B_154,C_155,D_156] :
      ( k1_enumset1(A_153,B_154,C_155) = D_156
      | k2_tarski(A_153,C_155) = D_156
      | k2_tarski(B_154,C_155) = D_156
      | k2_tarski(A_153,B_154) = D_156
      | k1_tarski(C_155) = D_156
      | k1_tarski(B_154) = D_156
      | k1_tarski(A_153) = D_156
      | k1_xboole_0 = D_156
      | ~ r1_tarski(D_156,k1_enumset1(A_153,B_154,C_155)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_442,plain,(
    ! [A_3,B_4,D_156] :
      ( k1_enumset1(A_3,A_3,B_4) = D_156
      | k2_tarski(A_3,B_4) = D_156
      | k2_tarski(A_3,B_4) = D_156
      | k2_tarski(A_3,A_3) = D_156
      | k1_tarski(B_4) = D_156
      | k1_tarski(A_3) = D_156
      | k1_tarski(A_3) = D_156
      | k1_xboole_0 = D_156
      | ~ r1_tarski(D_156,k2_tarski(A_3,B_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_414])).

tff(c_537,plain,(
    ! [A_181,B_182,D_183] :
      ( k2_tarski(A_181,B_182) = D_183
      | k2_tarski(A_181,B_182) = D_183
      | k2_tarski(A_181,B_182) = D_183
      | k1_tarski(A_181) = D_183
      | k1_tarski(B_182) = D_183
      | k1_tarski(A_181) = D_183
      | k1_tarski(A_181) = D_183
      | k1_xboole_0 = D_183
      | ~ r1_tarski(D_183,k2_tarski(A_181,B_182)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6,c_442])).

tff(c_582,plain,(
    ! [A_191,B_192,B_193] :
      ( k2_tarski(A_191,B_192) = k1_relat_1(B_193)
      | k1_tarski(B_192) = k1_relat_1(B_193)
      | k1_tarski(A_191) = k1_relat_1(B_193)
      | k1_relat_1(B_193) = k1_xboole_0
      | ~ v4_relat_1(B_193,k2_tarski(A_191,B_192))
      | ~ v1_relat_1(B_193) ) ),
    inference(resolution,[status(thm)],[c_30,c_537])).

tff(c_589,plain,(
    ! [A_2,B_193] :
      ( k2_tarski(A_2,A_2) = k1_relat_1(B_193)
      | k1_tarski(A_2) = k1_relat_1(B_193)
      | k1_tarski(A_2) = k1_relat_1(B_193)
      | k1_relat_1(B_193) = k1_xboole_0
      | ~ v4_relat_1(B_193,k1_tarski(A_2))
      | ~ v1_relat_1(B_193) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_582])).

tff(c_594,plain,(
    ! [A_194,B_195] :
      ( k1_tarski(A_194) = k1_relat_1(B_195)
      | k1_tarski(A_194) = k1_relat_1(B_195)
      | k1_tarski(A_194) = k1_relat_1(B_195)
      | k1_relat_1(B_195) = k1_xboole_0
      | ~ v4_relat_1(B_195,k1_tarski(A_194))
      | ~ v1_relat_1(B_195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_589])).

tff(c_604,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_255,c_594])).

tff(c_610,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_604])).

tff(c_612,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_245,c_352,c_610])).

tff(c_613,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_232])).

tff(c_32,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_623,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_613,c_613,c_32])).

tff(c_36,plain,(
    ! [A_14] :
      ( k2_relat_1(A_14) != k1_xboole_0
      | k1_xboole_0 = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_231,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_224,c_36])).

tff(c_233,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_231])).

tff(c_615,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_613,c_233])).

tff(c_671,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_623,c_615])).

tff(c_672,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_231])).

tff(c_34,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_680,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_672,c_672,c_34])).

tff(c_673,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_231])).

tff(c_694,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_672,c_673])).

tff(c_849,plain,(
    ! [B_242,A_243] :
      ( k1_tarski(k1_funct_1(B_242,A_243)) = k2_relat_1(B_242)
      | k1_tarski(A_243) != k1_relat_1(B_242)
      | ~ v1_funct_1(B_242)
      | ~ v1_relat_1(B_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_833,plain,(
    ! [A_234,B_235,C_236] :
      ( k2_relset_1(A_234,B_235,C_236) = k2_relat_1(C_236)
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(A_234,B_235))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_836,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_833])).

tff(c_838,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_694,c_836])).

tff(c_839,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_838,c_66])).

tff(c_855,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_849,c_839])).

tff(c_882,plain,(
    k1_tarski('#skF_2') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_74,c_680,c_694,c_855])).

tff(c_58,plain,(
    ! [A_29] :
      ( r2_hidden('#skF_1'(A_29),A_29)
      | k1_xboole_0 = A_29 ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_679,plain,(
    ! [A_29] :
      ( r2_hidden('#skF_1'(A_29),A_29)
      | A_29 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_672,c_58])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_683,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_672,c_2])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_686,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_672,c_68])).

tff(c_72,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_64,plain,(
    ! [D_50,C_49,A_47,B_48] :
      ( r2_hidden(k1_funct_1(D_50,C_49),k2_relset_1(A_47,B_48,D_50))
      | k1_xboole_0 = B_48
      | ~ r2_hidden(C_49,A_47)
      | ~ m1_subset_1(D_50,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48)))
      | ~ v1_funct_2(D_50,A_47,B_48)
      | ~ v1_funct_1(D_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_911,plain,(
    ! [D_253,C_254,A_255,B_256] :
      ( r2_hidden(k1_funct_1(D_253,C_254),k2_relset_1(A_255,B_256,D_253))
      | B_256 = '#skF_4'
      | ~ r2_hidden(C_254,A_255)
      | ~ m1_subset_1(D_253,k1_zfmisc_1(k2_zfmisc_1(A_255,B_256)))
      | ~ v1_funct_2(D_253,A_255,B_256)
      | ~ v1_funct_1(D_253) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_672,c_64])).

tff(c_921,plain,(
    ! [C_254] :
      ( r2_hidden(k1_funct_1('#skF_4',C_254),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_254,k1_tarski('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3')))
      | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_838,c_911])).

tff(c_926,plain,(
    ! [C_254] :
      ( r2_hidden(k1_funct_1('#skF_4',C_254),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_254,k1_tarski('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_921])).

tff(c_928,plain,(
    ! [C_257] :
      ( r2_hidden(k1_funct_1('#skF_4',C_257),'#skF_4')
      | ~ r2_hidden(C_257,k1_tarski('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_686,c_926])).

tff(c_48,plain,(
    ! [B_19,A_18] :
      ( ~ r1_tarski(B_19,A_18)
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_935,plain,(
    ! [C_257] :
      ( ~ r1_tarski('#skF_4',k1_funct_1('#skF_4',C_257))
      | ~ r2_hidden(C_257,k1_tarski('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_928,c_48])).

tff(c_943,plain,(
    ! [C_258] : ~ r2_hidden(C_258,k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_683,c_935])).

tff(c_947,plain,(
    k1_tarski('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_679,c_943])).

tff(c_951,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_882,c_947])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n023.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 20:55:50 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.66  
% 3.52/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.66  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_mcart_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.52/1.66  
% 3.52/1.66  %Foreground sorts:
% 3.52/1.66  
% 3.52/1.66  
% 3.52/1.66  %Background operators:
% 3.52/1.66  
% 3.52/1.66  
% 3.52/1.66  %Foreground operators:
% 3.52/1.66  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.52/1.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.52/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.52/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.52/1.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.52/1.66  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.52/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.52/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.52/1.66  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.52/1.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.52/1.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.52/1.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.52/1.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.52/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.52/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.52/1.66  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.52/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.52/1.66  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.52/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.52/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.52/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.52/1.66  tff('#skF_4', type, '#skF_4': $i).
% 3.52/1.66  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.52/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.52/1.66  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.52/1.66  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 3.52/1.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.52/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.52/1.66  
% 3.72/1.68  tff(f_149, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 3.72/1.68  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.72/1.68  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.72/1.68  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.72/1.68  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.72/1.68  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.72/1.68  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.72/1.68  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.72/1.68  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.72/1.68  tff(f_60, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 3.72/1.68  tff(f_69, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.72/1.68  tff(f_125, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_mcart_1)).
% 3.72/1.68  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.72/1.68  tff(f_137, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 3.72/1.68  tff(f_95, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.72/1.68  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.72/1.68  tff(c_220, plain, (![C_90, A_91, B_92]: (v1_relat_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.72/1.68  tff(c_224, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_220])).
% 3.72/1.68  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.72/1.68  tff(c_38, plain, (![A_14]: (k1_relat_1(A_14)!=k1_xboole_0 | k1_xboole_0=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.72/1.68  tff(c_232, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_224, c_38])).
% 3.72/1.68  tff(c_245, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_232])).
% 3.72/1.68  tff(c_318, plain, (![B_132, A_133]: (k1_tarski(k1_funct_1(B_132, A_133))=k2_relat_1(B_132) | k1_tarski(A_133)!=k1_relat_1(B_132) | ~v1_funct_1(B_132) | ~v1_relat_1(B_132))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.72/1.68  tff(c_298, plain, (![A_111, B_112, C_113]: (k2_relset_1(A_111, B_112, C_113)=k2_relat_1(C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.72/1.68  tff(c_302, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_298])).
% 3.72/1.68  tff(c_66, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')!=k1_tarski(k1_funct_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.72/1.68  tff(c_303, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_302, c_66])).
% 3.72/1.68  tff(c_324, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_318, c_303])).
% 3.72/1.68  tff(c_352, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_224, c_74, c_324])).
% 3.72/1.68  tff(c_251, plain, (![C_98, A_99, B_100]: (v4_relat_1(C_98, A_99) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.72/1.68  tff(c_255, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_70, c_251])).
% 3.72/1.68  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.72/1.68  tff(c_30, plain, (![B_13, A_12]: (r1_tarski(k1_relat_1(B_13), A_12) | ~v4_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.72/1.68  tff(c_6, plain, (![A_3, B_4]: (k1_enumset1(A_3, A_3, B_4)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.72/1.68  tff(c_414, plain, (![A_153, B_154, C_155, D_156]: (k1_enumset1(A_153, B_154, C_155)=D_156 | k2_tarski(A_153, C_155)=D_156 | k2_tarski(B_154, C_155)=D_156 | k2_tarski(A_153, B_154)=D_156 | k1_tarski(C_155)=D_156 | k1_tarski(B_154)=D_156 | k1_tarski(A_153)=D_156 | k1_xboole_0=D_156 | ~r1_tarski(D_156, k1_enumset1(A_153, B_154, C_155)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.72/1.68  tff(c_442, plain, (![A_3, B_4, D_156]: (k1_enumset1(A_3, A_3, B_4)=D_156 | k2_tarski(A_3, B_4)=D_156 | k2_tarski(A_3, B_4)=D_156 | k2_tarski(A_3, A_3)=D_156 | k1_tarski(B_4)=D_156 | k1_tarski(A_3)=D_156 | k1_tarski(A_3)=D_156 | k1_xboole_0=D_156 | ~r1_tarski(D_156, k2_tarski(A_3, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_414])).
% 3.72/1.68  tff(c_537, plain, (![A_181, B_182, D_183]: (k2_tarski(A_181, B_182)=D_183 | k2_tarski(A_181, B_182)=D_183 | k2_tarski(A_181, B_182)=D_183 | k1_tarski(A_181)=D_183 | k1_tarski(B_182)=D_183 | k1_tarski(A_181)=D_183 | k1_tarski(A_181)=D_183 | k1_xboole_0=D_183 | ~r1_tarski(D_183, k2_tarski(A_181, B_182)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6, c_442])).
% 3.72/1.68  tff(c_582, plain, (![A_191, B_192, B_193]: (k2_tarski(A_191, B_192)=k1_relat_1(B_193) | k1_tarski(B_192)=k1_relat_1(B_193) | k1_tarski(A_191)=k1_relat_1(B_193) | k1_relat_1(B_193)=k1_xboole_0 | ~v4_relat_1(B_193, k2_tarski(A_191, B_192)) | ~v1_relat_1(B_193))), inference(resolution, [status(thm)], [c_30, c_537])).
% 3.72/1.68  tff(c_589, plain, (![A_2, B_193]: (k2_tarski(A_2, A_2)=k1_relat_1(B_193) | k1_tarski(A_2)=k1_relat_1(B_193) | k1_tarski(A_2)=k1_relat_1(B_193) | k1_relat_1(B_193)=k1_xboole_0 | ~v4_relat_1(B_193, k1_tarski(A_2)) | ~v1_relat_1(B_193))), inference(superposition, [status(thm), theory('equality')], [c_4, c_582])).
% 3.72/1.68  tff(c_594, plain, (![A_194, B_195]: (k1_tarski(A_194)=k1_relat_1(B_195) | k1_tarski(A_194)=k1_relat_1(B_195) | k1_tarski(A_194)=k1_relat_1(B_195) | k1_relat_1(B_195)=k1_xboole_0 | ~v4_relat_1(B_195, k1_tarski(A_194)) | ~v1_relat_1(B_195))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_589])).
% 3.72/1.68  tff(c_604, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_255, c_594])).
% 3.72/1.68  tff(c_610, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_224, c_604])).
% 3.72/1.68  tff(c_612, plain, $false, inference(negUnitSimplification, [status(thm)], [c_245, c_352, c_610])).
% 3.72/1.68  tff(c_613, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_232])).
% 3.72/1.68  tff(c_32, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.72/1.68  tff(c_623, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_613, c_613, c_32])).
% 3.72/1.68  tff(c_36, plain, (![A_14]: (k2_relat_1(A_14)!=k1_xboole_0 | k1_xboole_0=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.72/1.68  tff(c_231, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_224, c_36])).
% 3.72/1.68  tff(c_233, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_231])).
% 3.72/1.68  tff(c_615, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_613, c_233])).
% 3.72/1.68  tff(c_671, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_623, c_615])).
% 3.72/1.68  tff(c_672, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_231])).
% 3.72/1.68  tff(c_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.72/1.68  tff(c_680, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_672, c_672, c_34])).
% 3.72/1.68  tff(c_673, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_231])).
% 3.72/1.68  tff(c_694, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_672, c_673])).
% 3.72/1.68  tff(c_849, plain, (![B_242, A_243]: (k1_tarski(k1_funct_1(B_242, A_243))=k2_relat_1(B_242) | k1_tarski(A_243)!=k1_relat_1(B_242) | ~v1_funct_1(B_242) | ~v1_relat_1(B_242))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.72/1.68  tff(c_833, plain, (![A_234, B_235, C_236]: (k2_relset_1(A_234, B_235, C_236)=k2_relat_1(C_236) | ~m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1(A_234, B_235))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.72/1.68  tff(c_836, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_833])).
% 3.72/1.68  tff(c_838, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_694, c_836])).
% 3.72/1.68  tff(c_839, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_838, c_66])).
% 3.72/1.68  tff(c_855, plain, (k2_relat_1('#skF_4')!='#skF_4' | k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_849, c_839])).
% 3.72/1.68  tff(c_882, plain, (k1_tarski('#skF_2')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_224, c_74, c_680, c_694, c_855])).
% 3.72/1.68  tff(c_58, plain, (![A_29]: (r2_hidden('#skF_1'(A_29), A_29) | k1_xboole_0=A_29)), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.72/1.68  tff(c_679, plain, (![A_29]: (r2_hidden('#skF_1'(A_29), A_29) | A_29='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_672, c_58])).
% 3.72/1.68  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.72/1.68  tff(c_683, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_672, c_2])).
% 3.72/1.68  tff(c_68, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.72/1.68  tff(c_686, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_672, c_68])).
% 3.72/1.68  tff(c_72, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.72/1.68  tff(c_64, plain, (![D_50, C_49, A_47, B_48]: (r2_hidden(k1_funct_1(D_50, C_49), k2_relset_1(A_47, B_48, D_50)) | k1_xboole_0=B_48 | ~r2_hidden(C_49, A_47) | ~m1_subset_1(D_50, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))) | ~v1_funct_2(D_50, A_47, B_48) | ~v1_funct_1(D_50))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.72/1.68  tff(c_911, plain, (![D_253, C_254, A_255, B_256]: (r2_hidden(k1_funct_1(D_253, C_254), k2_relset_1(A_255, B_256, D_253)) | B_256='#skF_4' | ~r2_hidden(C_254, A_255) | ~m1_subset_1(D_253, k1_zfmisc_1(k2_zfmisc_1(A_255, B_256))) | ~v1_funct_2(D_253, A_255, B_256) | ~v1_funct_1(D_253))), inference(demodulation, [status(thm), theory('equality')], [c_672, c_64])).
% 3.72/1.68  tff(c_921, plain, (![C_254]: (r2_hidden(k1_funct_1('#skF_4', C_254), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_254, k1_tarski('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3') | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_838, c_911])).
% 3.72/1.68  tff(c_926, plain, (![C_254]: (r2_hidden(k1_funct_1('#skF_4', C_254), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_254, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_921])).
% 3.72/1.68  tff(c_928, plain, (![C_257]: (r2_hidden(k1_funct_1('#skF_4', C_257), '#skF_4') | ~r2_hidden(C_257, k1_tarski('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_686, c_926])).
% 3.72/1.68  tff(c_48, plain, (![B_19, A_18]: (~r1_tarski(B_19, A_18) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.72/1.68  tff(c_935, plain, (![C_257]: (~r1_tarski('#skF_4', k1_funct_1('#skF_4', C_257)) | ~r2_hidden(C_257, k1_tarski('#skF_2')))), inference(resolution, [status(thm)], [c_928, c_48])).
% 3.72/1.68  tff(c_943, plain, (![C_258]: (~r2_hidden(C_258, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_683, c_935])).
% 3.72/1.68  tff(c_947, plain, (k1_tarski('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_679, c_943])).
% 3.72/1.68  tff(c_951, plain, $false, inference(negUnitSimplification, [status(thm)], [c_882, c_947])).
% 3.72/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/1.68  
% 3.72/1.68  Inference rules
% 3.72/1.68  ----------------------
% 3.72/1.68  #Ref     : 0
% 3.72/1.68  #Sup     : 185
% 3.72/1.68  #Fact    : 0
% 3.72/1.68  #Define  : 0
% 3.72/1.68  #Split   : 2
% 3.72/1.68  #Chain   : 0
% 3.72/1.68  #Close   : 0
% 3.72/1.68  
% 3.72/1.68  Ordering : KBO
% 3.72/1.68  
% 3.72/1.68  Simplification rules
% 3.72/1.68  ----------------------
% 3.72/1.68  #Subsume      : 17
% 3.72/1.68  #Demod        : 195
% 3.72/1.68  #Tautology    : 109
% 3.72/1.68  #SimpNegUnit  : 8
% 3.72/1.68  #BackRed      : 29
% 3.72/1.68  
% 3.72/1.68  #Partial instantiations: 0
% 3.72/1.68  #Strategies tried      : 1
% 3.72/1.68  
% 3.72/1.68  Timing (in seconds)
% 3.72/1.68  ----------------------
% 3.72/1.69  Preprocessing        : 0.35
% 3.72/1.69  Parsing              : 0.19
% 3.72/1.69  CNF conversion       : 0.02
% 3.72/1.69  Main loop            : 0.49
% 3.72/1.69  Inferencing          : 0.18
% 3.72/1.69  Reduction            : 0.16
% 3.72/1.69  Demodulation         : 0.12
% 3.72/1.69  BG Simplification    : 0.02
% 3.72/1.69  Subsumption          : 0.09
% 3.72/1.69  Abstraction          : 0.02
% 3.72/1.69  MUC search           : 0.00
% 3.72/1.69  Cooper               : 0.00
% 3.72/1.69  Total                : 0.88
% 3.72/1.69  Index Insertion      : 0.00
% 3.72/1.69  Index Deletion       : 0.00
% 3.72/1.69  Index Matching       : 0.00
% 3.72/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
