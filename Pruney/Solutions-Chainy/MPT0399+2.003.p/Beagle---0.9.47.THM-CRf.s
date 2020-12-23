%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:32 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 199 expanded)
%              Number of leaves         :   45 (  81 expanded)
%              Depth                    :   11
%              Number of atoms          :  118 ( 317 expanded)
%              Number of equality atoms :   34 (  67 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_64,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_68,axiom,(
    ! [A] : v1_xboole_0(k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_subset_1)).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_93,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_55,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_56,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_54,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_66,axiom,(
    ! [A] : m1_subset_1(k1_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_subset_1)).

tff(f_40,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_42,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_71,axiom,(
    ! [A,B,C,D,E,F,G,H] : ~ v1_xboole_0(k6_enumset1(A,B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_subset_1)).

tff(c_38,plain,(
    ! [A_37] : k1_subset_1(A_37) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_42,plain,(
    ! [A_39] : v1_xboole_0(k1_subset_1(A_39)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_61,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42])).

tff(c_60,plain,(
    r1_setfam_1('#skF_3',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_52,plain,(
    ! [A_48,B_49] :
      ( r2_hidden('#skF_1'(A_48,B_49),A_48)
      | r1_setfam_1(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_373,plain,(
    ! [A_122,B_123,C_124] :
      ( r2_hidden('#skF_2'(A_122,B_123,C_124),B_123)
      | ~ r2_hidden(C_124,A_122)
      | ~ r1_setfam_1(A_122,B_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( ~ v1_xboole_0(B_5)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_378,plain,(
    ! [B_125,C_126,A_127] :
      ( ~ v1_xboole_0(B_125)
      | ~ r2_hidden(C_126,A_127)
      | ~ r1_setfam_1(A_127,B_125) ) ),
    inference(resolution,[status(thm)],[c_373,c_10])).

tff(c_388,plain,(
    ! [B_128,A_129,B_130] :
      ( ~ v1_xboole_0(B_128)
      | ~ r1_setfam_1(A_129,B_128)
      | r1_setfam_1(A_129,B_130) ) ),
    inference(resolution,[status(thm)],[c_52,c_378])).

tff(c_394,plain,(
    ! [B_130] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | r1_setfam_1('#skF_3',B_130) ) ),
    inference(resolution,[status(thm)],[c_60,c_388])).

tff(c_399,plain,(
    ! [B_130] : r1_setfam_1('#skF_3',B_130) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_394])).

tff(c_56,plain,(
    ! [A_62,B_63] :
      ( r2_hidden(A_62,B_63)
      | v1_xboole_0(B_63)
      | ~ m1_subset_1(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_418,plain,(
    ! [B_132,B_133,A_134] :
      ( ~ v1_xboole_0(B_132)
      | ~ r1_setfam_1(B_133,B_132)
      | v1_xboole_0(B_133)
      | ~ m1_subset_1(A_134,B_133) ) ),
    inference(resolution,[status(thm)],[c_56,c_378])).

tff(c_425,plain,(
    ! [B_130,A_134] :
      ( ~ v1_xboole_0(B_130)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_134,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_399,c_418])).

tff(c_428,plain,(
    ! [A_134] : ~ m1_subset_1(A_134,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_425])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_28,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_121,plain,(
    ! [A_80,B_81] :
      ( r1_tarski(k3_tarski(A_80),k3_tarski(B_81))
      | ~ r1_setfam_1(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_127,plain,(
    ! [A_80] :
      ( r1_tarski(k3_tarski(A_80),k1_xboole_0)
      | ~ r1_setfam_1(A_80,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_121])).

tff(c_134,plain,(
    ! [B_83,A_84] :
      ( B_83 = A_84
      | ~ r1_tarski(B_83,A_84)
      | ~ r1_tarski(A_84,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_136,plain,(
    ! [A_80] :
      ( k3_tarski(A_80) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,k3_tarski(A_80))
      | ~ r1_setfam_1(A_80,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_127,c_134])).

tff(c_172,plain,(
    ! [A_86] :
      ( k3_tarski(A_86) = k1_xboole_0
      | ~ r1_setfam_1(A_86,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_136])).

tff(c_181,plain,(
    k3_tarski('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_172])).

tff(c_26,plain,(
    ! [A_34] : r1_tarski(A_34,k1_zfmisc_1(k3_tarski(A_34))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_194,plain,(
    r1_tarski('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_26])).

tff(c_200,plain,(
    r1_tarski('#skF_3',k1_tarski(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_194])).

tff(c_211,plain,(
    ! [B_88,A_89] :
      ( k1_tarski(B_88) = A_89
      | k1_xboole_0 = A_89
      | ~ r1_tarski(A_89,k1_tarski(B_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_214,plain,
    ( k1_tarski(k1_xboole_0) = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_200,c_211])).

tff(c_225,plain,(
    k1_tarski(k1_xboole_0) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_214])).

tff(c_40,plain,(
    ! [A_38] : m1_subset_1(k1_subset_1(A_38),k1_zfmisc_1(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_83,plain,(
    ! [A_67] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_67)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40])).

tff(c_85,plain,(
    m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_83])).

tff(c_231,plain,(
    m1_subset_1(k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_85])).

tff(c_430,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_428,c_231])).

tff(c_431,plain,(
    ! [B_130] :
      ( ~ v1_xboole_0(B_130)
      | v1_xboole_0('#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_425])).

tff(c_432,plain,(
    ! [B_130] : ~ v1_xboole_0(B_130) ),
    inference(splitLeft,[status(thm)],[c_431])).

tff(c_437,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_432,c_61])).

tff(c_438,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_431])).

tff(c_12,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_14,plain,(
    ! [A_7,B_8] : k1_enumset1(A_7,A_7,B_8) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_16,plain,(
    ! [A_9,B_10,C_11] : k2_enumset1(A_9,A_9,B_10,C_11) = k1_enumset1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_18,plain,(
    ! [A_12,B_13,C_14,D_15] : k3_enumset1(A_12,A_12,B_13,C_14,D_15) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_20,plain,(
    ! [C_18,B_17,A_16,D_19,E_20] : k4_enumset1(A_16,A_16,B_17,C_18,D_19,E_20) = k3_enumset1(A_16,B_17,C_18,D_19,E_20) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_22,plain,(
    ! [A_21,B_22,D_24,C_23,F_26,E_25] : k5_enumset1(A_21,A_21,B_22,C_23,D_24,E_25,F_26) = k4_enumset1(A_21,B_22,C_23,D_24,E_25,F_26) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_600,plain,(
    ! [C_170,D_171,A_175,B_173,G_174,F_169,E_172] : k6_enumset1(A_175,A_175,B_173,C_170,D_171,E_172,F_169,G_174) = k5_enumset1(A_175,B_173,C_170,D_171,E_172,F_169,G_174) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_44,plain,(
    ! [E_44,H_47,C_42,G_46,F_45,A_40,D_43,B_41] : ~ v1_xboole_0(k6_enumset1(A_40,B_41,C_42,D_43,E_44,F_45,G_46,H_47)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_611,plain,(
    ! [B_178,A_177,E_176,G_181,D_180,C_179,F_182] : ~ v1_xboole_0(k5_enumset1(A_177,B_178,C_179,D_180,E_176,F_182,G_181)) ),
    inference(superposition,[status(thm),theory(equality)],[c_600,c_44])).

tff(c_614,plain,(
    ! [E_188,D_184,C_185,A_183,B_187,F_186] : ~ v1_xboole_0(k4_enumset1(A_183,B_187,C_185,D_184,E_188,F_186)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_611])).

tff(c_617,plain,(
    ! [A_191,C_193,D_192,B_189,E_190] : ~ v1_xboole_0(k3_enumset1(A_191,B_189,C_193,D_192,E_190)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_614])).

tff(c_620,plain,(
    ! [A_194,B_195,C_196,D_197] : ~ v1_xboole_0(k2_enumset1(A_194,B_195,C_196,D_197)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_617])).

tff(c_623,plain,(
    ! [A_198,B_199,C_200] : ~ v1_xboole_0(k1_enumset1(A_198,B_199,C_200)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_620])).

tff(c_627,plain,(
    ! [A_204,B_205] : ~ v1_xboole_0(k2_tarski(A_204,B_205)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_623])).

tff(c_630,plain,(
    ! [A_206] : ~ v1_xboole_0(k1_tarski(A_206)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_627])).

tff(c_632,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_630])).

tff(c_635,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_438,c_632])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:07:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.46  
% 2.52/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.46  %$ r2_hidden > r1_tarski > r1_setfam_1 > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 2.52/1.46  
% 2.52/1.46  %Foreground sorts:
% 2.52/1.46  
% 2.52/1.46  
% 2.52/1.46  %Background operators:
% 2.52/1.46  
% 2.52/1.46  
% 2.52/1.46  %Foreground operators:
% 2.52/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.52/1.46  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.52/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.52/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.52/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.52/1.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.52/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.52/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.52/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.52/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.52/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.52/1.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.52/1.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.52/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.52/1.46  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.52/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.52/1.46  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.52/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.52/1.46  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.52/1.46  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.52/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.52/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.52/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.52/1.46  
% 2.94/1.48  tff(f_64, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.94/1.48  tff(f_68, axiom, (![A]: v1_xboole_0(k1_subset_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc13_subset_1)).
% 2.94/1.48  tff(f_98, negated_conjecture, ~(![A]: (r1_setfam_1(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_setfam_1)).
% 2.94/1.48  tff(f_83, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_setfam_1)).
% 2.94/1.48  tff(f_38, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 2.94/1.48  tff(f_93, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.94/1.48  tff(f_55, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 2.94/1.48  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.94/1.48  tff(f_56, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.94/1.48  tff(f_87, axiom, (![A, B]: (r1_setfam_1(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_setfam_1)).
% 2.94/1.48  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.94/1.48  tff(f_54, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 2.94/1.48  tff(f_62, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 2.94/1.48  tff(f_66, axiom, (![A]: m1_subset_1(k1_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 2.94/1.48  tff(f_40, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.94/1.48  tff(f_42, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.94/1.48  tff(f_44, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.94/1.48  tff(f_46, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.94/1.48  tff(f_48, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.94/1.48  tff(f_50, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 2.94/1.48  tff(f_52, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 2.94/1.48  tff(f_71, axiom, (![A, B, C, D, E, F, G, H]: ~v1_xboole_0(k6_enumset1(A, B, C, D, E, F, G, H))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_subset_1)).
% 2.94/1.48  tff(c_38, plain, (![A_37]: (k1_subset_1(A_37)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.94/1.48  tff(c_42, plain, (![A_39]: (v1_xboole_0(k1_subset_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.94/1.48  tff(c_61, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_42])).
% 2.94/1.48  tff(c_60, plain, (r1_setfam_1('#skF_3', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.94/1.48  tff(c_52, plain, (![A_48, B_49]: (r2_hidden('#skF_1'(A_48, B_49), A_48) | r1_setfam_1(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.94/1.48  tff(c_373, plain, (![A_122, B_123, C_124]: (r2_hidden('#skF_2'(A_122, B_123, C_124), B_123) | ~r2_hidden(C_124, A_122) | ~r1_setfam_1(A_122, B_123))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.94/1.48  tff(c_10, plain, (![B_5, A_4]: (~v1_xboole_0(B_5) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.94/1.48  tff(c_378, plain, (![B_125, C_126, A_127]: (~v1_xboole_0(B_125) | ~r2_hidden(C_126, A_127) | ~r1_setfam_1(A_127, B_125))), inference(resolution, [status(thm)], [c_373, c_10])).
% 2.94/1.48  tff(c_388, plain, (![B_128, A_129, B_130]: (~v1_xboole_0(B_128) | ~r1_setfam_1(A_129, B_128) | r1_setfam_1(A_129, B_130))), inference(resolution, [status(thm)], [c_52, c_378])).
% 2.94/1.48  tff(c_394, plain, (![B_130]: (~v1_xboole_0(k1_xboole_0) | r1_setfam_1('#skF_3', B_130))), inference(resolution, [status(thm)], [c_60, c_388])).
% 2.94/1.48  tff(c_399, plain, (![B_130]: (r1_setfam_1('#skF_3', B_130))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_394])).
% 2.94/1.48  tff(c_56, plain, (![A_62, B_63]: (r2_hidden(A_62, B_63) | v1_xboole_0(B_63) | ~m1_subset_1(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.94/1.48  tff(c_418, plain, (![B_132, B_133, A_134]: (~v1_xboole_0(B_132) | ~r1_setfam_1(B_133, B_132) | v1_xboole_0(B_133) | ~m1_subset_1(A_134, B_133))), inference(resolution, [status(thm)], [c_56, c_378])).
% 2.94/1.48  tff(c_425, plain, (![B_130, A_134]: (~v1_xboole_0(B_130) | v1_xboole_0('#skF_3') | ~m1_subset_1(A_134, '#skF_3'))), inference(resolution, [status(thm)], [c_399, c_418])).
% 2.94/1.48  tff(c_428, plain, (![A_134]: (~m1_subset_1(A_134, '#skF_3'))), inference(splitLeft, [status(thm)], [c_425])).
% 2.94/1.48  tff(c_58, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.94/1.48  tff(c_28, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.94/1.48  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.94/1.48  tff(c_30, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.94/1.48  tff(c_121, plain, (![A_80, B_81]: (r1_tarski(k3_tarski(A_80), k3_tarski(B_81)) | ~r1_setfam_1(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.94/1.48  tff(c_127, plain, (![A_80]: (r1_tarski(k3_tarski(A_80), k1_xboole_0) | ~r1_setfam_1(A_80, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_121])).
% 2.94/1.48  tff(c_134, plain, (![B_83, A_84]: (B_83=A_84 | ~r1_tarski(B_83, A_84) | ~r1_tarski(A_84, B_83))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.94/1.48  tff(c_136, plain, (![A_80]: (k3_tarski(A_80)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k3_tarski(A_80)) | ~r1_setfam_1(A_80, k1_xboole_0))), inference(resolution, [status(thm)], [c_127, c_134])).
% 2.94/1.48  tff(c_172, plain, (![A_86]: (k3_tarski(A_86)=k1_xboole_0 | ~r1_setfam_1(A_86, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_136])).
% 2.94/1.48  tff(c_181, plain, (k3_tarski('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_60, c_172])).
% 2.94/1.48  tff(c_26, plain, (![A_34]: (r1_tarski(A_34, k1_zfmisc_1(k3_tarski(A_34))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.94/1.48  tff(c_194, plain, (r1_tarski('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_181, c_26])).
% 2.94/1.48  tff(c_200, plain, (r1_tarski('#skF_3', k1_tarski(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_194])).
% 2.94/1.48  tff(c_211, plain, (![B_88, A_89]: (k1_tarski(B_88)=A_89 | k1_xboole_0=A_89 | ~r1_tarski(A_89, k1_tarski(B_88)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.94/1.48  tff(c_214, plain, (k1_tarski(k1_xboole_0)='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_200, c_211])).
% 2.94/1.48  tff(c_225, plain, (k1_tarski(k1_xboole_0)='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_58, c_214])).
% 2.94/1.48  tff(c_40, plain, (![A_38]: (m1_subset_1(k1_subset_1(A_38), k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.94/1.48  tff(c_83, plain, (![A_67]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_67)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40])).
% 2.94/1.48  tff(c_85, plain, (m1_subset_1(k1_xboole_0, k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_83])).
% 2.94/1.48  tff(c_231, plain, (m1_subset_1(k1_xboole_0, '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_225, c_85])).
% 2.94/1.48  tff(c_430, plain, $false, inference(negUnitSimplification, [status(thm)], [c_428, c_231])).
% 2.94/1.48  tff(c_431, plain, (![B_130]: (~v1_xboole_0(B_130) | v1_xboole_0('#skF_3'))), inference(splitRight, [status(thm)], [c_425])).
% 2.94/1.48  tff(c_432, plain, (![B_130]: (~v1_xboole_0(B_130))), inference(splitLeft, [status(thm)], [c_431])).
% 2.94/1.48  tff(c_437, plain, $false, inference(negUnitSimplification, [status(thm)], [c_432, c_61])).
% 2.94/1.48  tff(c_438, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_431])).
% 2.94/1.48  tff(c_12, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.94/1.48  tff(c_14, plain, (![A_7, B_8]: (k1_enumset1(A_7, A_7, B_8)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.94/1.48  tff(c_16, plain, (![A_9, B_10, C_11]: (k2_enumset1(A_9, A_9, B_10, C_11)=k1_enumset1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.94/1.48  tff(c_18, plain, (![A_12, B_13, C_14, D_15]: (k3_enumset1(A_12, A_12, B_13, C_14, D_15)=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.94/1.48  tff(c_20, plain, (![C_18, B_17, A_16, D_19, E_20]: (k4_enumset1(A_16, A_16, B_17, C_18, D_19, E_20)=k3_enumset1(A_16, B_17, C_18, D_19, E_20))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.94/1.48  tff(c_22, plain, (![A_21, B_22, D_24, C_23, F_26, E_25]: (k5_enumset1(A_21, A_21, B_22, C_23, D_24, E_25, F_26)=k4_enumset1(A_21, B_22, C_23, D_24, E_25, F_26))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.94/1.48  tff(c_600, plain, (![C_170, D_171, A_175, B_173, G_174, F_169, E_172]: (k6_enumset1(A_175, A_175, B_173, C_170, D_171, E_172, F_169, G_174)=k5_enumset1(A_175, B_173, C_170, D_171, E_172, F_169, G_174))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.94/1.48  tff(c_44, plain, (![E_44, H_47, C_42, G_46, F_45, A_40, D_43, B_41]: (~v1_xboole_0(k6_enumset1(A_40, B_41, C_42, D_43, E_44, F_45, G_46, H_47)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.94/1.48  tff(c_611, plain, (![B_178, A_177, E_176, G_181, D_180, C_179, F_182]: (~v1_xboole_0(k5_enumset1(A_177, B_178, C_179, D_180, E_176, F_182, G_181)))), inference(superposition, [status(thm), theory('equality')], [c_600, c_44])).
% 2.94/1.48  tff(c_614, plain, (![E_188, D_184, C_185, A_183, B_187, F_186]: (~v1_xboole_0(k4_enumset1(A_183, B_187, C_185, D_184, E_188, F_186)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_611])).
% 2.94/1.48  tff(c_617, plain, (![A_191, C_193, D_192, B_189, E_190]: (~v1_xboole_0(k3_enumset1(A_191, B_189, C_193, D_192, E_190)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_614])).
% 2.94/1.48  tff(c_620, plain, (![A_194, B_195, C_196, D_197]: (~v1_xboole_0(k2_enumset1(A_194, B_195, C_196, D_197)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_617])).
% 2.94/1.48  tff(c_623, plain, (![A_198, B_199, C_200]: (~v1_xboole_0(k1_enumset1(A_198, B_199, C_200)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_620])).
% 2.94/1.48  tff(c_627, plain, (![A_204, B_205]: (~v1_xboole_0(k2_tarski(A_204, B_205)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_623])).
% 2.94/1.48  tff(c_630, plain, (![A_206]: (~v1_xboole_0(k1_tarski(A_206)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_627])).
% 2.94/1.48  tff(c_632, plain, (~v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_225, c_630])).
% 2.94/1.48  tff(c_635, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_438, c_632])).
% 2.94/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.48  
% 2.94/1.48  Inference rules
% 2.94/1.48  ----------------------
% 2.94/1.48  #Ref     : 0
% 2.94/1.48  #Sup     : 123
% 2.94/1.48  #Fact    : 0
% 2.94/1.48  #Define  : 0
% 2.94/1.48  #Split   : 3
% 2.94/1.48  #Chain   : 0
% 2.94/1.48  #Close   : 0
% 2.94/1.48  
% 2.94/1.48  Ordering : KBO
% 2.94/1.48  
% 2.94/1.48  Simplification rules
% 2.94/1.48  ----------------------
% 2.94/1.48  #Subsume      : 26
% 2.94/1.48  #Demod        : 60
% 2.94/1.48  #Tautology    : 66
% 2.94/1.48  #SimpNegUnit  : 9
% 2.94/1.48  #BackRed      : 7
% 2.94/1.48  
% 2.94/1.48  #Partial instantiations: 0
% 2.94/1.48  #Strategies tried      : 1
% 2.94/1.48  
% 2.94/1.48  Timing (in seconds)
% 2.94/1.48  ----------------------
% 2.94/1.48  Preprocessing        : 0.34
% 2.94/1.48  Parsing              : 0.18
% 2.94/1.48  CNF conversion       : 0.02
% 2.94/1.48  Main loop            : 0.30
% 2.94/1.48  Inferencing          : 0.11
% 2.94/1.48  Reduction            : 0.09
% 2.94/1.48  Demodulation         : 0.06
% 2.94/1.48  BG Simplification    : 0.02
% 2.94/1.48  Subsumption          : 0.05
% 2.94/1.48  Abstraction          : 0.01
% 2.94/1.48  MUC search           : 0.00
% 2.94/1.48  Cooper               : 0.00
% 2.94/1.48  Total                : 0.68
% 2.94/1.48  Index Insertion      : 0.00
% 2.94/1.48  Index Deletion       : 0.00
% 2.94/1.48  Index Matching       : 0.00
% 2.94/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
