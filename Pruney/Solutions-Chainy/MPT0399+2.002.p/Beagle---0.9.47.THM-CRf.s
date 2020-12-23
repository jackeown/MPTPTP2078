%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:32 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 237 expanded)
%              Number of leaves         :   45 (  93 expanded)
%              Depth                    :   10
%              Number of atoms          :  129 ( 393 expanded)
%              Number of equality atoms :   37 (  82 expanded)
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_63,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_setfam_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_61,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_78,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_80,axiom,(
    ! [A] : m1_subset_1(k1_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_43,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_83,axiom,(
    ! [A,B,C,D,E,F,G,H] : ~ v1_xboole_0(k6_enumset1(A,B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_subset_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_66,plain,(
    r1_setfam_1('#skF_3',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_60,plain,(
    ! [A_49,B_50] :
      ( r2_hidden('#skF_1'(A_49,B_50),A_49)
      | r1_setfam_1(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_446,plain,(
    ! [A_131,B_132,C_133] :
      ( r2_hidden('#skF_2'(A_131,B_132,C_133),B_132)
      | ~ r2_hidden(C_133,A_131)
      | ~ r1_setfam_1(A_131,B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_12,plain,(
    ! [B_5,A_4] :
      ( ~ v1_xboole_0(B_5)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_464,plain,(
    ! [B_139,C_140,A_141] :
      ( ~ v1_xboole_0(B_139)
      | ~ r2_hidden(C_140,A_141)
      | ~ r1_setfam_1(A_141,B_139) ) ),
    inference(resolution,[status(thm)],[c_446,c_12])).

tff(c_474,plain,(
    ! [B_142,A_143,B_144] :
      ( ~ v1_xboole_0(B_142)
      | ~ r1_setfam_1(A_143,B_142)
      | r1_setfam_1(A_143,B_144) ) ),
    inference(resolution,[status(thm)],[c_60,c_464])).

tff(c_480,plain,(
    ! [B_144] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | r1_setfam_1('#skF_3',B_144) ) ),
    inference(resolution,[status(thm)],[c_66,c_474])).

tff(c_485,plain,(
    ! [B_144] : r1_setfam_1('#skF_3',B_144) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_480])).

tff(c_42,plain,(
    ! [B_38,A_37] :
      ( r2_hidden(B_38,A_37)
      | ~ m1_subset_1(B_38,A_37)
      | v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_513,plain,(
    ! [B_152,A_153,B_154] :
      ( ~ v1_xboole_0(B_152)
      | ~ r1_setfam_1(A_153,B_152)
      | ~ m1_subset_1(B_154,A_153)
      | v1_xboole_0(A_153) ) ),
    inference(resolution,[status(thm)],[c_42,c_464])).

tff(c_520,plain,(
    ! [B_144,B_154] :
      ( ~ v1_xboole_0(B_144)
      | ~ m1_subset_1(B_154,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_485,c_513])).

tff(c_523,plain,(
    ! [B_154] : ~ m1_subset_1(B_154,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_520])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_36,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_38,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_177,plain,(
    ! [A_88,B_89] :
      ( r1_tarski(k3_tarski(A_88),k3_tarski(B_89))
      | ~ r1_setfam_1(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_188,plain,(
    ! [A_90] :
      ( r1_tarski(k3_tarski(A_90),k1_xboole_0)
      | ~ r1_setfam_1(A_90,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_177])).

tff(c_10,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_131,plain,(
    ! [B_77,A_78] :
      ( B_77 = A_78
      | ~ r1_tarski(B_77,A_78)
      | ~ r1_tarski(A_78,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_139,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_131])).

tff(c_202,plain,(
    ! [A_91] :
      ( k3_tarski(A_91) = k1_xboole_0
      | ~ r1_setfam_1(A_91,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_188,c_139])).

tff(c_211,plain,(
    k3_tarski('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_66,c_202])).

tff(c_34,plain,(
    ! [A_36] : r1_tarski(A_36,k1_zfmisc_1(k3_tarski(A_36))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_233,plain,(
    r1_tarski('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_34])).

tff(c_239,plain,(
    r1_tarski('#skF_3',k1_tarski(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_233])).

tff(c_275,plain,(
    ! [B_98,A_99] :
      ( k1_tarski(B_98) = A_99
      | k1_xboole_0 = A_99
      | ~ r1_tarski(A_99,k1_tarski(B_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_278,plain,
    ( k1_tarski(k1_xboole_0) = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_239,c_275])).

tff(c_289,plain,(
    k1_tarski(k1_xboole_0) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_278])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_243,plain,
    ( k1_tarski(k1_xboole_0) = '#skF_3'
    | ~ r1_tarski(k1_tarski(k1_xboole_0),'#skF_3') ),
    inference(resolution,[status(thm)],[c_239,c_4])).

tff(c_274,plain,(
    ~ r1_tarski(k1_tarski(k1_xboole_0),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_243])).

tff(c_294,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_274])).

tff(c_300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_294])).

tff(c_301,plain,(
    k1_tarski(k1_xboole_0) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_243])).

tff(c_48,plain,(
    ! [A_39] : k1_subset_1(A_39) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_50,plain,(
    ! [A_40] : m1_subset_1(k1_subset_1(A_40),k1_zfmisc_1(A_40)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_88,plain,(
    ! [A_66] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_66)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50])).

tff(c_90,plain,(
    m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_88])).

tff(c_304,plain,(
    m1_subset_1(k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_90])).

tff(c_525,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_523,c_304])).

tff(c_526,plain,(
    ! [B_144] :
      ( ~ v1_xboole_0(B_144)
      | v1_xboole_0('#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_520])).

tff(c_527,plain,(
    ! [B_144] : ~ v1_xboole_0(B_144) ),
    inference(splitLeft,[status(thm)],[c_526])).

tff(c_535,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_527,c_2])).

tff(c_536,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_526])).

tff(c_14,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [A_7,B_8] : k1_enumset1(A_7,A_7,B_8) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [A_9,B_10,C_11] : k2_enumset1(A_9,A_9,B_10,C_11) = k1_enumset1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [A_12,B_13,C_14,D_15] : k3_enumset1(A_12,A_12,B_13,C_14,D_15) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    ! [C_18,B_17,A_16,D_19,E_20] : k4_enumset1(A_16,A_16,B_17,C_18,D_19,E_20) = k3_enumset1(A_16,B_17,C_18,D_19,E_20) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_24,plain,(
    ! [A_21,B_22,D_24,C_23,F_26,E_25] : k5_enumset1(A_21,A_21,B_22,C_23,D_24,E_25,F_26) = k4_enumset1(A_21,B_22,C_23,D_24,E_25,F_26) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_537,plain,(
    ! [B_159,D_157,F_155,A_161,C_156,G_160,E_158] : k6_enumset1(A_161,A_161,B_159,C_156,D_157,E_158,F_155,G_160) = k5_enumset1(A_161,B_159,C_156,D_157,E_158,F_155,G_160) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_52,plain,(
    ! [D_44,F_46,C_43,H_48,A_41,B_42,G_47,E_45] : ~ v1_xboole_0(k6_enumset1(A_41,B_42,C_43,D_44,E_45,F_46,G_47,H_48)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_553,plain,(
    ! [A_163,D_162,G_165,F_166,B_164,E_167,C_168] : ~ v1_xboole_0(k5_enumset1(A_163,B_164,C_168,D_162,E_167,F_166,G_165)) ),
    inference(superposition,[status(thm),theory(equality)],[c_537,c_52])).

tff(c_556,plain,(
    ! [C_171,D_170,E_174,A_169,F_172,B_173] : ~ v1_xboole_0(k4_enumset1(A_169,B_173,C_171,D_170,E_174,F_172)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_553])).

tff(c_559,plain,(
    ! [A_177,D_178,B_175,E_176,C_179] : ~ v1_xboole_0(k3_enumset1(A_177,B_175,C_179,D_178,E_176)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_556])).

tff(c_562,plain,(
    ! [A_180,B_181,C_182,D_183] : ~ v1_xboole_0(k2_enumset1(A_180,B_181,C_182,D_183)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_559])).

tff(c_565,plain,(
    ! [A_184,B_185,C_186] : ~ v1_xboole_0(k1_enumset1(A_184,B_185,C_186)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_562])).

tff(c_568,plain,(
    ! [A_187,B_188] : ~ v1_xboole_0(k2_tarski(A_187,B_188)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_565])).

tff(c_571,plain,(
    ! [A_189] : ~ v1_xboole_0(k1_tarski(A_189)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_568])).

tff(c_573,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_571])).

tff(c_576,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_536,c_573])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.16/0.36  % Computer   : n008.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 10:42:30 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.40  
% 2.76/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.40  %$ r2_hidden > r1_tarski > r1_setfam_1 > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 2.76/1.40  
% 2.76/1.40  %Foreground sorts:
% 2.76/1.40  
% 2.76/1.40  
% 2.76/1.40  %Background operators:
% 2.76/1.40  
% 2.76/1.40  
% 2.76/1.40  %Foreground operators:
% 2.76/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.40  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.76/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.76/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.76/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.76/1.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.76/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.76/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.76/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.76/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.76/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.76/1.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.76/1.40  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.76/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.76/1.40  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.76/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.40  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.76/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.40  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.76/1.40  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.76/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.76/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.76/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.76/1.40  
% 2.76/1.42  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.76/1.42  tff(f_104, negated_conjecture, ~(![A]: (r1_setfam_1(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_setfam_1)).
% 2.76/1.42  tff(f_95, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 2.76/1.42  tff(f_39, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_boole)).
% 2.76/1.42  tff(f_76, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.76/1.42  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.76/1.42  tff(f_62, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 2.76/1.42  tff(f_63, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.76/1.42  tff(f_99, axiom, (![A, B]: (r1_setfam_1(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_setfam_1)).
% 2.76/1.42  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.76/1.42  tff(f_61, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 2.76/1.42  tff(f_59, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.76/1.42  tff(f_78, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.76/1.42  tff(f_80, axiom, (![A]: m1_subset_1(k1_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 2.76/1.42  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.76/1.42  tff(f_43, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.76/1.42  tff(f_45, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.76/1.42  tff(f_47, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.76/1.42  tff(f_49, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.76/1.42  tff(f_51, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 2.76/1.42  tff(f_53, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 2.76/1.42  tff(f_83, axiom, (![A, B, C, D, E, F, G, H]: ~v1_xboole_0(k6_enumset1(A, B, C, D, E, F, G, H))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_subset_1)).
% 2.76/1.42  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.76/1.42  tff(c_66, plain, (r1_setfam_1('#skF_3', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.76/1.42  tff(c_60, plain, (![A_49, B_50]: (r2_hidden('#skF_1'(A_49, B_50), A_49) | r1_setfam_1(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.76/1.42  tff(c_446, plain, (![A_131, B_132, C_133]: (r2_hidden('#skF_2'(A_131, B_132, C_133), B_132) | ~r2_hidden(C_133, A_131) | ~r1_setfam_1(A_131, B_132))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.76/1.42  tff(c_12, plain, (![B_5, A_4]: (~v1_xboole_0(B_5) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.76/1.42  tff(c_464, plain, (![B_139, C_140, A_141]: (~v1_xboole_0(B_139) | ~r2_hidden(C_140, A_141) | ~r1_setfam_1(A_141, B_139))), inference(resolution, [status(thm)], [c_446, c_12])).
% 2.76/1.42  tff(c_474, plain, (![B_142, A_143, B_144]: (~v1_xboole_0(B_142) | ~r1_setfam_1(A_143, B_142) | r1_setfam_1(A_143, B_144))), inference(resolution, [status(thm)], [c_60, c_464])).
% 2.76/1.42  tff(c_480, plain, (![B_144]: (~v1_xboole_0(k1_xboole_0) | r1_setfam_1('#skF_3', B_144))), inference(resolution, [status(thm)], [c_66, c_474])).
% 2.76/1.42  tff(c_485, plain, (![B_144]: (r1_setfam_1('#skF_3', B_144))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_480])).
% 2.76/1.42  tff(c_42, plain, (![B_38, A_37]: (r2_hidden(B_38, A_37) | ~m1_subset_1(B_38, A_37) | v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.76/1.42  tff(c_513, plain, (![B_152, A_153, B_154]: (~v1_xboole_0(B_152) | ~r1_setfam_1(A_153, B_152) | ~m1_subset_1(B_154, A_153) | v1_xboole_0(A_153))), inference(resolution, [status(thm)], [c_42, c_464])).
% 2.76/1.42  tff(c_520, plain, (![B_144, B_154]: (~v1_xboole_0(B_144) | ~m1_subset_1(B_154, '#skF_3') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_485, c_513])).
% 2.76/1.42  tff(c_523, plain, (![B_154]: (~m1_subset_1(B_154, '#skF_3'))), inference(splitLeft, [status(thm)], [c_520])).
% 2.76/1.42  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.76/1.42  tff(c_64, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.76/1.42  tff(c_36, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.76/1.42  tff(c_38, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.76/1.42  tff(c_177, plain, (![A_88, B_89]: (r1_tarski(k3_tarski(A_88), k3_tarski(B_89)) | ~r1_setfam_1(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.76/1.42  tff(c_188, plain, (![A_90]: (r1_tarski(k3_tarski(A_90), k1_xboole_0) | ~r1_setfam_1(A_90, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_177])).
% 2.76/1.42  tff(c_10, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.76/1.42  tff(c_131, plain, (![B_77, A_78]: (B_77=A_78 | ~r1_tarski(B_77, A_78) | ~r1_tarski(A_78, B_77))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.76/1.42  tff(c_139, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_131])).
% 2.76/1.42  tff(c_202, plain, (![A_91]: (k3_tarski(A_91)=k1_xboole_0 | ~r1_setfam_1(A_91, k1_xboole_0))), inference(resolution, [status(thm)], [c_188, c_139])).
% 2.76/1.42  tff(c_211, plain, (k3_tarski('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_66, c_202])).
% 2.76/1.42  tff(c_34, plain, (![A_36]: (r1_tarski(A_36, k1_zfmisc_1(k3_tarski(A_36))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.76/1.42  tff(c_233, plain, (r1_tarski('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_211, c_34])).
% 2.76/1.42  tff(c_239, plain, (r1_tarski('#skF_3', k1_tarski(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_233])).
% 2.76/1.42  tff(c_275, plain, (![B_98, A_99]: (k1_tarski(B_98)=A_99 | k1_xboole_0=A_99 | ~r1_tarski(A_99, k1_tarski(B_98)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.76/1.42  tff(c_278, plain, (k1_tarski(k1_xboole_0)='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_239, c_275])).
% 2.76/1.42  tff(c_289, plain, (k1_tarski(k1_xboole_0)='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_64, c_278])).
% 2.76/1.42  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.76/1.42  tff(c_243, plain, (k1_tarski(k1_xboole_0)='#skF_3' | ~r1_tarski(k1_tarski(k1_xboole_0), '#skF_3')), inference(resolution, [status(thm)], [c_239, c_4])).
% 2.76/1.42  tff(c_274, plain, (~r1_tarski(k1_tarski(k1_xboole_0), '#skF_3')), inference(splitLeft, [status(thm)], [c_243])).
% 2.76/1.42  tff(c_294, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_289, c_274])).
% 2.76/1.42  tff(c_300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_294])).
% 2.76/1.42  tff(c_301, plain, (k1_tarski(k1_xboole_0)='#skF_3'), inference(splitRight, [status(thm)], [c_243])).
% 2.76/1.42  tff(c_48, plain, (![A_39]: (k1_subset_1(A_39)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.76/1.42  tff(c_50, plain, (![A_40]: (m1_subset_1(k1_subset_1(A_40), k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.76/1.42  tff(c_88, plain, (![A_66]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_66)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50])).
% 2.76/1.42  tff(c_90, plain, (m1_subset_1(k1_xboole_0, k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36, c_88])).
% 2.76/1.42  tff(c_304, plain, (m1_subset_1(k1_xboole_0, '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_301, c_90])).
% 2.76/1.42  tff(c_525, plain, $false, inference(negUnitSimplification, [status(thm)], [c_523, c_304])).
% 2.76/1.42  tff(c_526, plain, (![B_144]: (~v1_xboole_0(B_144) | v1_xboole_0('#skF_3'))), inference(splitRight, [status(thm)], [c_520])).
% 2.76/1.42  tff(c_527, plain, (![B_144]: (~v1_xboole_0(B_144))), inference(splitLeft, [status(thm)], [c_526])).
% 2.76/1.42  tff(c_535, plain, $false, inference(negUnitSimplification, [status(thm)], [c_527, c_2])).
% 2.76/1.42  tff(c_536, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_526])).
% 2.76/1.42  tff(c_14, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.76/1.42  tff(c_16, plain, (![A_7, B_8]: (k1_enumset1(A_7, A_7, B_8)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.76/1.42  tff(c_18, plain, (![A_9, B_10, C_11]: (k2_enumset1(A_9, A_9, B_10, C_11)=k1_enumset1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.76/1.42  tff(c_20, plain, (![A_12, B_13, C_14, D_15]: (k3_enumset1(A_12, A_12, B_13, C_14, D_15)=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.76/1.42  tff(c_22, plain, (![C_18, B_17, A_16, D_19, E_20]: (k4_enumset1(A_16, A_16, B_17, C_18, D_19, E_20)=k3_enumset1(A_16, B_17, C_18, D_19, E_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.76/1.42  tff(c_24, plain, (![A_21, B_22, D_24, C_23, F_26, E_25]: (k5_enumset1(A_21, A_21, B_22, C_23, D_24, E_25, F_26)=k4_enumset1(A_21, B_22, C_23, D_24, E_25, F_26))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.76/1.42  tff(c_537, plain, (![B_159, D_157, F_155, A_161, C_156, G_160, E_158]: (k6_enumset1(A_161, A_161, B_159, C_156, D_157, E_158, F_155, G_160)=k5_enumset1(A_161, B_159, C_156, D_157, E_158, F_155, G_160))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.76/1.42  tff(c_52, plain, (![D_44, F_46, C_43, H_48, A_41, B_42, G_47, E_45]: (~v1_xboole_0(k6_enumset1(A_41, B_42, C_43, D_44, E_45, F_46, G_47, H_48)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.76/1.42  tff(c_553, plain, (![A_163, D_162, G_165, F_166, B_164, E_167, C_168]: (~v1_xboole_0(k5_enumset1(A_163, B_164, C_168, D_162, E_167, F_166, G_165)))), inference(superposition, [status(thm), theory('equality')], [c_537, c_52])).
% 2.76/1.42  tff(c_556, plain, (![C_171, D_170, E_174, A_169, F_172, B_173]: (~v1_xboole_0(k4_enumset1(A_169, B_173, C_171, D_170, E_174, F_172)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_553])).
% 2.76/1.42  tff(c_559, plain, (![A_177, D_178, B_175, E_176, C_179]: (~v1_xboole_0(k3_enumset1(A_177, B_175, C_179, D_178, E_176)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_556])).
% 2.76/1.42  tff(c_562, plain, (![A_180, B_181, C_182, D_183]: (~v1_xboole_0(k2_enumset1(A_180, B_181, C_182, D_183)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_559])).
% 2.76/1.42  tff(c_565, plain, (![A_184, B_185, C_186]: (~v1_xboole_0(k1_enumset1(A_184, B_185, C_186)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_562])).
% 2.76/1.42  tff(c_568, plain, (![A_187, B_188]: (~v1_xboole_0(k2_tarski(A_187, B_188)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_565])).
% 2.76/1.42  tff(c_571, plain, (![A_189]: (~v1_xboole_0(k1_tarski(A_189)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_568])).
% 2.76/1.42  tff(c_573, plain, (~v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_301, c_571])).
% 2.76/1.42  tff(c_576, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_536, c_573])).
% 2.76/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.42  
% 2.76/1.42  Inference rules
% 2.76/1.42  ----------------------
% 2.76/1.42  #Ref     : 0
% 2.76/1.42  #Sup     : 106
% 2.76/1.42  #Fact    : 0
% 2.76/1.42  #Define  : 0
% 2.76/1.42  #Split   : 3
% 2.76/1.42  #Chain   : 0
% 2.76/1.42  #Close   : 0
% 2.76/1.42  
% 2.76/1.42  Ordering : KBO
% 2.76/1.42  
% 2.76/1.42  Simplification rules
% 2.76/1.42  ----------------------
% 2.76/1.42  #Subsume      : 15
% 2.76/1.42  #Demod        : 50
% 2.76/1.42  #Tautology    : 67
% 2.76/1.42  #SimpNegUnit  : 12
% 2.76/1.42  #BackRed      : 13
% 2.76/1.42  
% 2.76/1.42  #Partial instantiations: 0
% 2.76/1.42  #Strategies tried      : 1
% 2.76/1.42  
% 2.76/1.42  Timing (in seconds)
% 2.76/1.42  ----------------------
% 2.76/1.43  Preprocessing        : 0.33
% 2.76/1.43  Parsing              : 0.18
% 2.76/1.43  CNF conversion       : 0.02
% 2.76/1.43  Main loop            : 0.29
% 2.76/1.43  Inferencing          : 0.10
% 2.76/1.43  Reduction            : 0.09
% 2.76/1.43  Demodulation         : 0.06
% 2.76/1.43  BG Simplification    : 0.02
% 2.76/1.43  Subsumption          : 0.06
% 2.76/1.43  Abstraction          : 0.01
% 2.76/1.43  MUC search           : 0.00
% 2.76/1.43  Cooper               : 0.00
% 2.76/1.43  Total                : 0.67
% 2.76/1.43  Index Insertion      : 0.00
% 2.76/1.43  Index Deletion       : 0.00
% 2.76/1.43  Index Matching       : 0.00
% 2.76/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
