%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:15 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 309 expanded)
%              Number of leaves         :   44 ( 122 expanded)
%              Depth                    :   11
%              Number of atoms          :  135 ( 728 expanded)
%              Number of equality atoms :   53 ( 314 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_100,axiom,(
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

tff(f_74,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
    <=> ( r2_hidden(A,C)
        & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_28,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_30,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_32,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_36,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_38,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E,F,G,H] : ~ v1_xboole_0(k6_enumset1(A,B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_subset_1)).

tff(c_52,plain,(
    k1_funct_1('#skF_4','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_54,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',k1_tarski('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_79,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_83,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_79])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_58,plain,(
    v1_funct_2('#skF_4','#skF_1',k1_tarski('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_124,plain,(
    ! [A_96,B_97,C_98] :
      ( k1_relset_1(A_96,B_97,C_98) = k1_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_128,plain,(
    k1_relset_1('#skF_1',k1_tarski('#skF_2'),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_124])).

tff(c_173,plain,(
    ! [B_124,A_125,C_126] :
      ( k1_xboole_0 = B_124
      | k1_relset_1(A_125,B_124,C_126) = A_125
      | ~ v1_funct_2(C_126,A_125,B_124)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_125,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_176,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | k1_relset_1('#skF_1',k1_tarski('#skF_2'),'#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_56,c_173])).

tff(c_179,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_128,c_176])).

tff(c_180,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_179])).

tff(c_157,plain,(
    ! [B_116,A_117] :
      ( r2_hidden(k4_tarski(B_116,k1_funct_1(A_117,B_116)),A_117)
      | ~ r2_hidden(B_116,k1_relat_1(A_117))
      | ~ v1_funct_1(A_117)
      | ~ v1_relat_1(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_26,plain,(
    ! [C_44,A_41,B_42] :
      ( r2_hidden(C_44,A_41)
      | ~ r2_hidden(C_44,B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_256,plain,(
    ! [B_168,A_169,A_170] :
      ( r2_hidden(k4_tarski(B_168,k1_funct_1(A_169,B_168)),A_170)
      | ~ m1_subset_1(A_169,k1_zfmisc_1(A_170))
      | ~ r2_hidden(B_168,k1_relat_1(A_169))
      | ~ v1_funct_1(A_169)
      | ~ v1_relat_1(A_169) ) ),
    inference(resolution,[status(thm)],[c_157,c_26])).

tff(c_20,plain,(
    ! [D_32,B_30,A_29,C_31] :
      ( D_32 = B_30
      | ~ r2_hidden(k4_tarski(A_29,B_30),k2_zfmisc_1(C_31,k1_tarski(D_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_287,plain,(
    ! [A_181,B_182,D_183,C_184] :
      ( k1_funct_1(A_181,B_182) = D_183
      | ~ m1_subset_1(A_181,k1_zfmisc_1(k2_zfmisc_1(C_184,k1_tarski(D_183))))
      | ~ r2_hidden(B_182,k1_relat_1(A_181))
      | ~ v1_funct_1(A_181)
      | ~ v1_relat_1(A_181) ) ),
    inference(resolution,[status(thm)],[c_256,c_20])).

tff(c_289,plain,(
    ! [B_182] :
      ( k1_funct_1('#skF_4',B_182) = '#skF_2'
      | ~ r2_hidden(B_182,k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_56,c_287])).

tff(c_293,plain,(
    ! [B_185] :
      ( k1_funct_1('#skF_4',B_185) = '#skF_2'
      | ~ r2_hidden(B_185,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_60,c_180,c_289])).

tff(c_307,plain,(
    k1_funct_1('#skF_4','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_54,c_293])).

tff(c_314,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_307])).

tff(c_315,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_319,plain,(
    v1_funct_2('#skF_4','#skF_1',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_58])).

tff(c_318,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_56])).

tff(c_42,plain,(
    ! [C_58,A_56] :
      ( k1_xboole_0 = C_58
      | ~ v1_funct_2(C_58,A_56,k1_xboole_0)
      | k1_xboole_0 = A_56
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_358,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_4','#skF_1',k1_xboole_0)
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_318,c_42])).

tff(c_372,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_358])).

tff(c_377,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_372])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_388,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_2])).

tff(c_381,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_315])).

tff(c_4,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_6,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_8,plain,(
    ! [A_4,B_5,C_6] : k2_enumset1(A_4,A_4,B_5,C_6) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9,D_10] : k3_enumset1(A_7,A_7,B_8,C_9,D_10) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12,plain,(
    ! [D_14,E_15,B_12,A_11,C_13] : k4_enumset1(A_11,A_11,B_12,C_13,D_14,E_15) = k3_enumset1(A_11,B_12,C_13,D_14,E_15) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_14,plain,(
    ! [C_18,B_17,A_16,D_19,E_20,F_21] : k5_enumset1(A_16,A_16,B_17,C_18,D_19,E_20,F_21) = k4_enumset1(A_16,B_17,C_18,D_19,E_20,F_21) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_470,plain,(
    ! [E_205,B_209,F_206,C_204,A_203,D_208,G_207] : k6_enumset1(A_203,A_203,B_209,C_204,D_208,E_205,F_206,G_207) = k5_enumset1(A_203,B_209,C_204,D_208,E_205,F_206,G_207) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_24,plain,(
    ! [D_36,G_39,F_38,E_37,A_33,B_34,H_40,C_35] : ~ v1_xboole_0(k6_enumset1(A_33,B_34,C_35,D_36,E_37,F_38,G_39,H_40)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_481,plain,(
    ! [E_216,F_214,C_211,G_215,D_212,A_210,B_213] : ~ v1_xboole_0(k5_enumset1(A_210,B_213,C_211,D_212,E_216,F_214,G_215)) ),
    inference(superposition,[status(thm),theory(equality)],[c_470,c_24])).

tff(c_484,plain,(
    ! [C_222,E_219,D_221,F_217,A_220,B_218] : ~ v1_xboole_0(k4_enumset1(A_220,B_218,C_222,D_221,E_219,F_217)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_481])).

tff(c_487,plain,(
    ! [E_227,D_226,A_224,B_225,C_223] : ~ v1_xboole_0(k3_enumset1(A_224,B_225,C_223,D_226,E_227)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_484])).

tff(c_492,plain,(
    ! [A_231,B_232,C_233,D_234] : ~ v1_xboole_0(k2_enumset1(A_231,B_232,C_233,D_234)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_487])).

tff(c_495,plain,(
    ! [A_235,B_236,C_237] : ~ v1_xboole_0(k1_enumset1(A_235,B_236,C_237)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_492])).

tff(c_498,plain,(
    ! [A_238,B_239] : ~ v1_xboole_0(k2_tarski(A_238,B_239)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_495])).

tff(c_501,plain,(
    ! [A_240] : ~ v1_xboole_0(k1_tarski(A_240)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_498])).

tff(c_503,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_381,c_501])).

tff(c_506,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_503])).

tff(c_507,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_372])).

tff(c_519,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_507,c_2])).

tff(c_512,plain,(
    k1_tarski('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_507,c_315])).

tff(c_581,plain,(
    ! [E_251,D_254,B_255,C_250,F_252,G_253,A_249] : k6_enumset1(A_249,A_249,B_255,C_250,D_254,E_251,F_252,G_253) = k5_enumset1(A_249,B_255,C_250,D_254,E_251,F_252,G_253) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_592,plain,(
    ! [F_260,B_259,G_257,A_261,C_256,D_262,E_258] : ~ v1_xboole_0(k5_enumset1(A_261,B_259,C_256,D_262,E_258,F_260,G_257)) ),
    inference(superposition,[status(thm),theory(equality)],[c_581,c_24])).

tff(c_595,plain,(
    ! [D_267,A_266,C_268,B_264,E_265,F_263] : ~ v1_xboole_0(k4_enumset1(A_266,B_264,C_268,D_267,E_265,F_263)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_592])).

tff(c_598,plain,(
    ! [C_269,E_273,D_272,A_270,B_271] : ~ v1_xboole_0(k3_enumset1(A_270,B_271,C_269,D_272,E_273)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_595])).

tff(c_612,plain,(
    ! [A_277,B_278,C_279,D_280] : ~ v1_xboole_0(k2_enumset1(A_277,B_278,C_279,D_280)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_598])).

tff(c_615,plain,(
    ! [A_281,B_282,C_283] : ~ v1_xboole_0(k1_enumset1(A_281,B_282,C_283)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_612])).

tff(c_618,plain,(
    ! [A_284,B_285] : ~ v1_xboole_0(k2_tarski(A_284,B_285)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_615])).

tff(c_621,plain,(
    ! [A_286] : ~ v1_xboole_0(k1_tarski(A_286)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_618])).

tff(c_623,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_512,c_621])).

tff(c_626,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_623])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:48:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.58  
% 3.17/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.58  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.17/1.58  
% 3.17/1.58  %Foreground sorts:
% 3.17/1.58  
% 3.17/1.58  
% 3.17/1.58  %Background operators:
% 3.17/1.58  
% 3.17/1.58  
% 3.17/1.58  %Foreground operators:
% 3.17/1.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.17/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.17/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.17/1.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.17/1.58  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.17/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.17/1.58  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.17/1.58  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.17/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.17/1.58  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.17/1.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.17/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.17/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.17/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.17/1.58  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.17/1.58  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.17/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.17/1.58  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.17/1.58  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.17/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.17/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.17/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.17/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.17/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.17/1.58  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.17/1.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.17/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.17/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.17/1.58  
% 3.17/1.60  tff(f_111, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 3.17/1.60  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.17/1.60  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.17/1.60  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.17/1.60  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 3.17/1.60  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.17/1.60  tff(f_46, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 3.17/1.60  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.17/1.60  tff(f_28, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.17/1.60  tff(f_30, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.17/1.60  tff(f_32, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.17/1.60  tff(f_34, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.17/1.60  tff(f_36, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 3.17/1.60  tff(f_38, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 3.17/1.60  tff(f_40, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 3.17/1.60  tff(f_49, axiom, (![A, B, C, D, E, F, G, H]: ~v1_xboole_0(k6_enumset1(A, B, C, D, E, F, G, H))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_subset_1)).
% 3.17/1.60  tff(c_52, plain, (k1_funct_1('#skF_4', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.17/1.60  tff(c_54, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.17/1.60  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', k1_tarski('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.17/1.60  tff(c_79, plain, (![C_62, A_63, B_64]: (v1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.17/1.60  tff(c_83, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_79])).
% 3.17/1.60  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.17/1.60  tff(c_58, plain, (v1_funct_2('#skF_4', '#skF_1', k1_tarski('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.17/1.60  tff(c_124, plain, (![A_96, B_97, C_98]: (k1_relset_1(A_96, B_97, C_98)=k1_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.17/1.60  tff(c_128, plain, (k1_relset_1('#skF_1', k1_tarski('#skF_2'), '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_124])).
% 3.17/1.60  tff(c_173, plain, (![B_124, A_125, C_126]: (k1_xboole_0=B_124 | k1_relset_1(A_125, B_124, C_126)=A_125 | ~v1_funct_2(C_126, A_125, B_124) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_125, B_124))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.17/1.60  tff(c_176, plain, (k1_tarski('#skF_2')=k1_xboole_0 | k1_relset_1('#skF_1', k1_tarski('#skF_2'), '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_56, c_173])).
% 3.17/1.60  tff(c_179, plain, (k1_tarski('#skF_2')=k1_xboole_0 | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_128, c_176])).
% 3.17/1.60  tff(c_180, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(splitLeft, [status(thm)], [c_179])).
% 3.17/1.60  tff(c_157, plain, (![B_116, A_117]: (r2_hidden(k4_tarski(B_116, k1_funct_1(A_117, B_116)), A_117) | ~r2_hidden(B_116, k1_relat_1(A_117)) | ~v1_funct_1(A_117) | ~v1_relat_1(A_117))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.17/1.60  tff(c_26, plain, (![C_44, A_41, B_42]: (r2_hidden(C_44, A_41) | ~r2_hidden(C_44, B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.17/1.60  tff(c_256, plain, (![B_168, A_169, A_170]: (r2_hidden(k4_tarski(B_168, k1_funct_1(A_169, B_168)), A_170) | ~m1_subset_1(A_169, k1_zfmisc_1(A_170)) | ~r2_hidden(B_168, k1_relat_1(A_169)) | ~v1_funct_1(A_169) | ~v1_relat_1(A_169))), inference(resolution, [status(thm)], [c_157, c_26])).
% 3.17/1.60  tff(c_20, plain, (![D_32, B_30, A_29, C_31]: (D_32=B_30 | ~r2_hidden(k4_tarski(A_29, B_30), k2_zfmisc_1(C_31, k1_tarski(D_32))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.17/1.60  tff(c_287, plain, (![A_181, B_182, D_183, C_184]: (k1_funct_1(A_181, B_182)=D_183 | ~m1_subset_1(A_181, k1_zfmisc_1(k2_zfmisc_1(C_184, k1_tarski(D_183)))) | ~r2_hidden(B_182, k1_relat_1(A_181)) | ~v1_funct_1(A_181) | ~v1_relat_1(A_181))), inference(resolution, [status(thm)], [c_256, c_20])).
% 3.17/1.60  tff(c_289, plain, (![B_182]: (k1_funct_1('#skF_4', B_182)='#skF_2' | ~r2_hidden(B_182, k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_287])).
% 3.17/1.60  tff(c_293, plain, (![B_185]: (k1_funct_1('#skF_4', B_185)='#skF_2' | ~r2_hidden(B_185, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_60, c_180, c_289])).
% 3.17/1.60  tff(c_307, plain, (k1_funct_1('#skF_4', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_54, c_293])).
% 3.17/1.60  tff(c_314, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_307])).
% 3.17/1.60  tff(c_315, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_179])).
% 3.17/1.60  tff(c_319, plain, (v1_funct_2('#skF_4', '#skF_1', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_315, c_58])).
% 3.17/1.60  tff(c_318, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_315, c_56])).
% 3.17/1.60  tff(c_42, plain, (![C_58, A_56]: (k1_xboole_0=C_58 | ~v1_funct_2(C_58, A_56, k1_xboole_0) | k1_xboole_0=A_56 | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.17/1.60  tff(c_358, plain, (k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_4', '#skF_1', k1_xboole_0) | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_318, c_42])).
% 3.17/1.60  tff(c_372, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_319, c_358])).
% 3.17/1.60  tff(c_377, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_372])).
% 3.17/1.60  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.17/1.60  tff(c_388, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_377, c_2])).
% 3.17/1.60  tff(c_381, plain, (k1_tarski('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_377, c_315])).
% 3.17/1.60  tff(c_4, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.17/1.60  tff(c_6, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.17/1.60  tff(c_8, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.17/1.60  tff(c_10, plain, (![A_7, B_8, C_9, D_10]: (k3_enumset1(A_7, A_7, B_8, C_9, D_10)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.17/1.60  tff(c_12, plain, (![D_14, E_15, B_12, A_11, C_13]: (k4_enumset1(A_11, A_11, B_12, C_13, D_14, E_15)=k3_enumset1(A_11, B_12, C_13, D_14, E_15))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.17/1.60  tff(c_14, plain, (![C_18, B_17, A_16, D_19, E_20, F_21]: (k5_enumset1(A_16, A_16, B_17, C_18, D_19, E_20, F_21)=k4_enumset1(A_16, B_17, C_18, D_19, E_20, F_21))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.17/1.60  tff(c_470, plain, (![E_205, B_209, F_206, C_204, A_203, D_208, G_207]: (k6_enumset1(A_203, A_203, B_209, C_204, D_208, E_205, F_206, G_207)=k5_enumset1(A_203, B_209, C_204, D_208, E_205, F_206, G_207))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.17/1.60  tff(c_24, plain, (![D_36, G_39, F_38, E_37, A_33, B_34, H_40, C_35]: (~v1_xboole_0(k6_enumset1(A_33, B_34, C_35, D_36, E_37, F_38, G_39, H_40)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.17/1.60  tff(c_481, plain, (![E_216, F_214, C_211, G_215, D_212, A_210, B_213]: (~v1_xboole_0(k5_enumset1(A_210, B_213, C_211, D_212, E_216, F_214, G_215)))), inference(superposition, [status(thm), theory('equality')], [c_470, c_24])).
% 3.17/1.60  tff(c_484, plain, (![C_222, E_219, D_221, F_217, A_220, B_218]: (~v1_xboole_0(k4_enumset1(A_220, B_218, C_222, D_221, E_219, F_217)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_481])).
% 3.17/1.60  tff(c_487, plain, (![E_227, D_226, A_224, B_225, C_223]: (~v1_xboole_0(k3_enumset1(A_224, B_225, C_223, D_226, E_227)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_484])).
% 3.17/1.60  tff(c_492, plain, (![A_231, B_232, C_233, D_234]: (~v1_xboole_0(k2_enumset1(A_231, B_232, C_233, D_234)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_487])).
% 3.17/1.60  tff(c_495, plain, (![A_235, B_236, C_237]: (~v1_xboole_0(k1_enumset1(A_235, B_236, C_237)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_492])).
% 3.17/1.60  tff(c_498, plain, (![A_238, B_239]: (~v1_xboole_0(k2_tarski(A_238, B_239)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_495])).
% 3.17/1.60  tff(c_501, plain, (![A_240]: (~v1_xboole_0(k1_tarski(A_240)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_498])).
% 3.17/1.60  tff(c_503, plain, (~v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_381, c_501])).
% 3.17/1.60  tff(c_506, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_388, c_503])).
% 3.17/1.60  tff(c_507, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_372])).
% 3.17/1.60  tff(c_519, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_507, c_2])).
% 3.17/1.60  tff(c_512, plain, (k1_tarski('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_507, c_315])).
% 3.17/1.60  tff(c_581, plain, (![E_251, D_254, B_255, C_250, F_252, G_253, A_249]: (k6_enumset1(A_249, A_249, B_255, C_250, D_254, E_251, F_252, G_253)=k5_enumset1(A_249, B_255, C_250, D_254, E_251, F_252, G_253))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.17/1.60  tff(c_592, plain, (![F_260, B_259, G_257, A_261, C_256, D_262, E_258]: (~v1_xboole_0(k5_enumset1(A_261, B_259, C_256, D_262, E_258, F_260, G_257)))), inference(superposition, [status(thm), theory('equality')], [c_581, c_24])).
% 3.17/1.60  tff(c_595, plain, (![D_267, A_266, C_268, B_264, E_265, F_263]: (~v1_xboole_0(k4_enumset1(A_266, B_264, C_268, D_267, E_265, F_263)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_592])).
% 3.17/1.60  tff(c_598, plain, (![C_269, E_273, D_272, A_270, B_271]: (~v1_xboole_0(k3_enumset1(A_270, B_271, C_269, D_272, E_273)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_595])).
% 3.17/1.60  tff(c_612, plain, (![A_277, B_278, C_279, D_280]: (~v1_xboole_0(k2_enumset1(A_277, B_278, C_279, D_280)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_598])).
% 3.17/1.60  tff(c_615, plain, (![A_281, B_282, C_283]: (~v1_xboole_0(k1_enumset1(A_281, B_282, C_283)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_612])).
% 3.17/1.60  tff(c_618, plain, (![A_284, B_285]: (~v1_xboole_0(k2_tarski(A_284, B_285)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_615])).
% 3.17/1.60  tff(c_621, plain, (![A_286]: (~v1_xboole_0(k1_tarski(A_286)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_618])).
% 3.17/1.60  tff(c_623, plain, (~v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_512, c_621])).
% 3.17/1.60  tff(c_626, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_519, c_623])).
% 3.17/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.60  
% 3.17/1.60  Inference rules
% 3.17/1.60  ----------------------
% 3.17/1.60  #Ref     : 0
% 3.17/1.60  #Sup     : 131
% 3.17/1.60  #Fact    : 0
% 3.17/1.60  #Define  : 0
% 3.17/1.60  #Split   : 3
% 3.17/1.60  #Chain   : 0
% 3.17/1.60  #Close   : 0
% 3.17/1.60  
% 3.17/1.60  Ordering : KBO
% 3.17/1.60  
% 3.17/1.60  Simplification rules
% 3.17/1.60  ----------------------
% 3.17/1.60  #Subsume      : 9
% 3.17/1.60  #Demod        : 91
% 3.17/1.60  #Tautology    : 57
% 3.17/1.60  #SimpNegUnit  : 2
% 3.17/1.60  #BackRed      : 26
% 3.17/1.60  
% 3.17/1.60  #Partial instantiations: 0
% 3.17/1.60  #Strategies tried      : 1
% 3.17/1.60  
% 3.17/1.60  Timing (in seconds)
% 3.17/1.60  ----------------------
% 3.17/1.60  Preprocessing        : 0.39
% 3.17/1.61  Parsing              : 0.21
% 3.17/1.61  CNF conversion       : 0.02
% 3.17/1.61  Main loop            : 0.37
% 3.17/1.61  Inferencing          : 0.14
% 3.17/1.61  Reduction            : 0.11
% 3.17/1.61  Demodulation         : 0.08
% 3.17/1.61  BG Simplification    : 0.02
% 3.17/1.61  Subsumption          : 0.06
% 3.17/1.61  Abstraction          : 0.02
% 3.17/1.61  MUC search           : 0.00
% 3.17/1.61  Cooper               : 0.00
% 3.17/1.61  Total                : 0.80
% 3.17/1.61  Index Insertion      : 0.00
% 3.17/1.61  Index Deletion       : 0.00
% 3.17/1.61  Index Matching       : 0.00
% 3.17/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
