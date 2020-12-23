%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:28 EST 2020

% Result     : Theorem 13.53s
% Output     : CNFRefutation 13.73s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 228 expanded)
%              Number of leaves         :   53 ( 100 expanded)
%              Depth                    :   14
%              Number of atoms          :  200 ( 431 expanded)
%              Number of equality atoms :   41 (  93 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_2 > #skF_4 > #skF_13 > #skF_5 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_9 > #skF_12 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_172,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_81,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_52,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_127,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_155,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k2_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relat_1)).

tff(f_135,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_121,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

tff(f_87,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_123,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_162,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k2_relat_1(A),k2_relat_1(B)),k2_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B)
        & ! [D] :
            ( ( r1_tarski(A,D)
              & r1_tarski(C,D) )
           => r1_tarski(B,D) ) )
     => B = k2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

tff(f_89,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_139,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_146,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k1_relat_1(A),k1_relat_1(B)),k1_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_94,plain,(
    v1_relat_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_30,plain,(
    ! [A_19] : r1_tarski(k1_xboole_0,A_19) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_139,plain,(
    ! [A_96,B_97] :
      ( k4_xboole_0(A_96,B_97) = k1_xboole_0
      | ~ r1_tarski(A_96,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_155,plain,(
    ! [A_19] : k4_xboole_0(k1_xboole_0,A_19) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_139])).

tff(c_96,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_10,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_103,plain,(
    ! [A_82] :
      ( v1_relat_1(A_82)
      | ~ v1_xboole_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_107,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_103])).

tff(c_86,plain,(
    ! [A_72,B_73] :
      ( r2_hidden('#skF_11'(A_72,B_73),k1_relat_1(B_73))
      | ~ r2_hidden(A_72,k2_relat_1(B_73))
      | ~ v1_relat_1(B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_931,plain,(
    ! [C_173,A_174] :
      ( r2_hidden(k4_tarski(C_173,'#skF_10'(A_174,k1_relat_1(A_174),C_173)),A_174)
      | ~ r2_hidden(C_173,k1_relat_1(A_174)) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_42,plain,(
    ! [D_34,A_29] : r2_hidden(D_34,k2_tarski(A_29,D_34)) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_330,plain,(
    ! [C_125,A_126,D_127] :
      ( r2_hidden(C_125,k1_relat_1(A_126))
      | ~ r2_hidden(k4_tarski(C_125,D_127),A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_340,plain,(
    ! [C_125,A_29,D_127] : r2_hidden(C_125,k1_relat_1(k2_tarski(A_29,k4_tarski(C_125,D_127)))) ),
    inference(resolution,[status(thm)],[c_42,c_330])).

tff(c_64,plain,(
    ! [A_39,B_40] :
      ( r2_hidden('#skF_6'(A_39,B_40),B_40)
      | ~ r2_hidden(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_34,plain,(
    ! [A_23] : r1_xboole_0(A_23,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_290,plain,(
    ! [A_118,B_119,C_120] :
      ( ~ r1_xboole_0(A_118,B_119)
      | ~ r2_hidden(C_120,B_119)
      | ~ r2_hidden(C_120,A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_294,plain,(
    ! [C_121,A_122] :
      ( ~ r2_hidden(C_121,k1_xboole_0)
      | ~ r2_hidden(C_121,A_122) ) ),
    inference(resolution,[status(thm)],[c_34,c_290])).

tff(c_456,plain,(
    ! [A_143,A_144] :
      ( ~ r2_hidden('#skF_6'(A_143,k1_xboole_0),A_144)
      | ~ r2_hidden(A_143,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_64,c_294])).

tff(c_473,plain,(
    ! [A_143] : ~ r2_hidden(A_143,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_340,c_456])).

tff(c_951,plain,(
    ! [C_175] : ~ r2_hidden(C_175,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_931,c_473])).

tff(c_959,plain,(
    ! [A_72] :
      ( ~ r2_hidden(A_72,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_86,c_951])).

tff(c_1015,plain,(
    ! [A_176] : ~ r2_hidden(A_176,k2_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_959])).

tff(c_1040,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_1015])).

tff(c_92,plain,(
    r1_tarski('#skF_12','#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_153,plain,(
    k4_xboole_0('#skF_12','#skF_13') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_92,c_139])).

tff(c_66,plain,(
    ! [A_46,B_47] : k6_subset_1(A_46,B_47) = k4_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_88,plain,(
    ! [A_75,B_77] :
      ( r1_tarski(k6_subset_1(k2_relat_1(A_75),k2_relat_1(B_77)),k2_relat_1(k6_subset_1(A_75,B_77)))
      | ~ v1_relat_1(B_77)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_1225,plain,(
    ! [A_185,B_186] :
      ( r1_tarski(k4_xboole_0(k2_relat_1(A_185),k2_relat_1(B_186)),k2_relat_1(k4_xboole_0(A_185,B_186)))
      | ~ v1_relat_1(B_186)
      | ~ v1_relat_1(A_185) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_66,c_88])).

tff(c_1264,plain,
    ( r1_tarski(k4_xboole_0(k2_relat_1('#skF_12'),k2_relat_1('#skF_13')),k2_relat_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_13')
    | ~ v1_relat_1('#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_1225])).

tff(c_1281,plain,(
    r1_tarski(k4_xboole_0(k2_relat_1('#skF_12'),k2_relat_1('#skF_13')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_1040,c_1264])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | k4_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_213,plain,(
    ! [B_111,A_112] :
      ( B_111 = A_112
      | ~ r1_tarski(B_111,A_112)
      | ~ r1_tarski(A_112,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_227,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | k4_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_213])).

tff(c_1291,plain,
    ( k4_xboole_0(k2_relat_1('#skF_12'),k2_relat_1('#skF_13')) = k1_xboole_0
    | k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_relat_1('#skF_12'),k2_relat_1('#skF_13'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1281,c_227])).

tff(c_1305,plain,(
    k4_xboole_0(k2_relat_1('#skF_12'),k2_relat_1('#skF_13')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_1291])).

tff(c_16,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_26,plain,(
    ! [C_17,A_15,B_16] :
      ( r1_tarski(C_17,'#skF_3'(A_15,B_16,C_17))
      | k2_xboole_0(A_15,C_17) = B_16
      | ~ r1_tarski(C_17,B_16)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3106,plain,(
    ! [B_247,A_248,C_249] :
      ( ~ r1_tarski(B_247,'#skF_3'(A_248,B_247,C_249))
      | k2_xboole_0(A_248,C_249) = B_247
      | ~ r1_tarski(C_249,B_247)
      | ~ r1_tarski(A_248,B_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3114,plain,(
    ! [A_15,B_16] :
      ( k2_xboole_0(A_15,B_16) = B_16
      | ~ r1_tarski(B_16,B_16)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(resolution,[status(thm)],[c_26,c_3106])).

tff(c_3151,plain,(
    ! [A_250,B_251] :
      ( k2_xboole_0(A_250,B_251) = B_251
      | ~ r1_tarski(A_250,B_251) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_3114])).

tff(c_3655,plain,(
    ! [A_259,B_260] :
      ( k2_xboole_0(A_259,B_260) = B_260
      | k4_xboole_0(A_259,B_260) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_3151])).

tff(c_3709,plain,(
    k2_xboole_0(k2_relat_1('#skF_12'),k2_relat_1('#skF_13')) = k2_relat_1('#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_1305,c_3655])).

tff(c_36,plain,(
    ! [A_24,B_25] : r1_tarski(A_24,k2_xboole_0(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3906,plain,(
    r1_tarski(k2_relat_1('#skF_12'),k2_relat_1('#skF_13')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3709,c_36])).

tff(c_272,plain,(
    ! [A_117] :
      ( k2_xboole_0(k1_relat_1(A_117),k2_relat_1(A_117)) = k3_relat_1(A_117)
      | ~ v1_relat_1(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_22,plain,(
    ! [A_12,C_14,B_13] :
      ( r1_tarski(A_12,k2_xboole_0(C_14,B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_278,plain,(
    ! [A_12,A_117] :
      ( r1_tarski(A_12,k3_relat_1(A_117))
      | ~ r1_tarski(A_12,k2_relat_1(A_117))
      | ~ v1_relat_1(A_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_22])).

tff(c_983,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_951])).

tff(c_84,plain,(
    ! [A_69,B_71] :
      ( r1_tarski(k6_subset_1(k1_relat_1(A_69),k1_relat_1(B_71)),k1_relat_1(k6_subset_1(A_69,B_71)))
      | ~ v1_relat_1(B_71)
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1477,plain,(
    ! [A_193,B_194] :
      ( r1_tarski(k4_xboole_0(k1_relat_1(A_193),k1_relat_1(B_194)),k1_relat_1(k4_xboole_0(A_193,B_194)))
      | ~ v1_relat_1(B_194)
      | ~ v1_relat_1(A_193) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_66,c_84])).

tff(c_1522,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1('#skF_12'),k1_relat_1('#skF_13')),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_13')
    | ~ v1_relat_1('#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_1477])).

tff(c_1542,plain,(
    r1_tarski(k4_xboole_0(k1_relat_1('#skF_12'),k1_relat_1('#skF_13')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_983,c_1522])).

tff(c_1552,plain,
    ( k4_xboole_0(k1_relat_1('#skF_12'),k1_relat_1('#skF_13')) = k1_xboole_0
    | k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_relat_1('#skF_12'),k1_relat_1('#skF_13'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1542,c_227])).

tff(c_1566,plain,(
    k4_xboole_0(k1_relat_1('#skF_12'),k1_relat_1('#skF_13')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_1552])).

tff(c_3707,plain,(
    k2_xboole_0(k1_relat_1('#skF_12'),k1_relat_1('#skF_13')) = k1_relat_1('#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_1566,c_3655])).

tff(c_3839,plain,(
    r1_tarski(k1_relat_1('#skF_12'),k1_relat_1('#skF_13')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3707,c_36])).

tff(c_284,plain,(
    ! [A_117] :
      ( r1_tarski(k1_relat_1(A_117),k3_relat_1(A_117))
      | ~ v1_relat_1(A_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_36])).

tff(c_38,plain,(
    ! [A_26,C_28,B_27] :
      ( r1_tarski(k2_xboole_0(A_26,C_28),B_27)
      | ~ r1_tarski(C_28,B_27)
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_628,plain,(
    ! [A_157,B_158] :
      ( k2_xboole_0(A_157,B_158) = A_157
      | ~ r1_tarski(k2_xboole_0(A_157,B_158),A_157) ) ),
    inference(resolution,[status(thm)],[c_36,c_213])).

tff(c_632,plain,(
    ! [B_27,C_28] :
      ( k2_xboole_0(B_27,C_28) = B_27
      | ~ r1_tarski(C_28,B_27)
      | ~ r1_tarski(B_27,B_27) ) ),
    inference(resolution,[status(thm)],[c_38,c_628])).

tff(c_649,plain,(
    ! [B_159,C_160] :
      ( k2_xboole_0(B_159,C_160) = B_159
      | ~ r1_tarski(C_160,B_159) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_632])).

tff(c_1874,plain,(
    ! [A_212] :
      ( k2_xboole_0(k3_relat_1(A_212),k1_relat_1(A_212)) = k3_relat_1(A_212)
      | ~ v1_relat_1(A_212) ) ),
    inference(resolution,[status(thm)],[c_284,c_649])).

tff(c_34958,plain,(
    ! [A_43058,A_43059] :
      ( r1_tarski(A_43058,k3_relat_1(A_43059))
      | ~ r1_tarski(A_43058,k1_relat_1(A_43059))
      | ~ v1_relat_1(A_43059) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1874,c_22])).

tff(c_82,plain,(
    ! [A_68] :
      ( k2_xboole_0(k1_relat_1(A_68),k2_relat_1(A_68)) = k3_relat_1(A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_502,plain,(
    ! [A_146,C_147,B_148] :
      ( r1_tarski(k2_xboole_0(A_146,C_147),B_148)
      | ~ r1_tarski(C_147,B_148)
      | ~ r1_tarski(A_146,B_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_15543,plain,(
    ! [A_27423,B_27424] :
      ( r1_tarski(k3_relat_1(A_27423),B_27424)
      | ~ r1_tarski(k2_relat_1(A_27423),B_27424)
      | ~ r1_tarski(k1_relat_1(A_27423),B_27424)
      | ~ v1_relat_1(A_27423) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_502])).

tff(c_90,plain,(
    ~ r1_tarski(k3_relat_1('#skF_12'),k3_relat_1('#skF_13')) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_15643,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_12'),k3_relat_1('#skF_13'))
    | ~ r1_tarski(k1_relat_1('#skF_12'),k3_relat_1('#skF_13'))
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_15543,c_90])).

tff(c_15684,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_12'),k3_relat_1('#skF_13'))
    | ~ r1_tarski(k1_relat_1('#skF_12'),k3_relat_1('#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_15643])).

tff(c_15710,plain,(
    ~ r1_tarski(k1_relat_1('#skF_12'),k3_relat_1('#skF_13')) ),
    inference(splitLeft,[status(thm)],[c_15684])).

tff(c_34961,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_12'),k1_relat_1('#skF_13'))
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_34958,c_15710])).

tff(c_35004,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_3839,c_34961])).

tff(c_35005,plain,(
    ~ r1_tarski(k2_relat_1('#skF_12'),k3_relat_1('#skF_13')) ),
    inference(splitRight,[status(thm)],[c_15684])).

tff(c_35009,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_12'),k2_relat_1('#skF_13'))
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_278,c_35005])).

tff(c_35019,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_3906,c_35009])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:11:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.53/5.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.53/5.42  
% 13.53/5.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.53/5.42  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_2 > #skF_4 > #skF_13 > #skF_5 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_9 > #skF_12 > #skF_10
% 13.53/5.42  
% 13.53/5.42  %Foreground sorts:
% 13.53/5.42  
% 13.53/5.42  
% 13.53/5.42  %Background operators:
% 13.53/5.42  
% 13.53/5.42  
% 13.53/5.42  %Foreground operators:
% 13.53/5.42  tff('#skF_11', type, '#skF_11': ($i * $i) > $i).
% 13.53/5.42  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 13.53/5.42  tff('#skF_2', type, '#skF_2': $i > $i).
% 13.53/5.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.53/5.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.53/5.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.53/5.42  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 13.53/5.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.53/5.42  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 13.53/5.42  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 13.53/5.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.53/5.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.53/5.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.53/5.42  tff('#skF_13', type, '#skF_13': $i).
% 13.53/5.42  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 13.53/5.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.53/5.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 13.53/5.42  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 13.53/5.42  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 13.53/5.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.53/5.42  tff(k3_tarski, type, k3_tarski: $i > $i).
% 13.53/5.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.53/5.42  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 13.53/5.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.53/5.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.53/5.42  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 13.53/5.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.53/5.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.53/5.42  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 13.53/5.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.53/5.42  tff('#skF_12', type, '#skF_12': $i).
% 13.53/5.42  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 13.53/5.42  
% 13.73/5.44  tff(f_172, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 13.73/5.44  tff(f_81, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 13.73/5.44  tff(f_62, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 13.73/5.44  tff(f_52, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 13.73/5.44  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 13.73/5.44  tff(f_127, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 13.73/5.44  tff(f_155, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k2_relat_1(B)) & (![C]: ~r2_hidden(C, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relat_1)).
% 13.73/5.44  tff(f_135, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 13.73/5.44  tff(f_104, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 13.73/5.44  tff(f_121, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 13.73/5.44  tff(f_87, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 13.73/5.44  tff(f_44, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 13.73/5.44  tff(f_123, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 13.73/5.44  tff(f_162, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k2_relat_1(A), k2_relat_1(B)), k2_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_relat_1)).
% 13.73/5.44  tff(f_58, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.73/5.44  tff(f_79, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(C, B)) & (![D]: ((r1_tarski(A, D) & r1_tarski(C, D)) => r1_tarski(B, D)))) => (B = k2_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_xboole_1)).
% 13.73/5.44  tff(f_89, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 13.73/5.44  tff(f_139, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 13.73/5.44  tff(f_66, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 13.73/5.44  tff(f_146, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k1_relat_1(A), k1_relat_1(B)), k1_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_relat_1)).
% 13.73/5.44  tff(f_95, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 13.73/5.44  tff(c_94, plain, (v1_relat_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_172])).
% 13.73/5.44  tff(c_30, plain, (![A_19]: (r1_tarski(k1_xboole_0, A_19))), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.73/5.44  tff(c_139, plain, (![A_96, B_97]: (k4_xboole_0(A_96, B_97)=k1_xboole_0 | ~r1_tarski(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_62])).
% 13.73/5.44  tff(c_155, plain, (![A_19]: (k4_xboole_0(k1_xboole_0, A_19)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_139])).
% 13.73/5.44  tff(c_96, plain, (v1_relat_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_172])).
% 13.73/5.44  tff(c_10, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_52])).
% 13.73/5.44  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 13.73/5.44  tff(c_103, plain, (![A_82]: (v1_relat_1(A_82) | ~v1_xboole_0(A_82))), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.73/5.44  tff(c_107, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_103])).
% 13.73/5.44  tff(c_86, plain, (![A_72, B_73]: (r2_hidden('#skF_11'(A_72, B_73), k1_relat_1(B_73)) | ~r2_hidden(A_72, k2_relat_1(B_73)) | ~v1_relat_1(B_73))), inference(cnfTransformation, [status(thm)], [f_155])).
% 13.73/5.44  tff(c_931, plain, (![C_173, A_174]: (r2_hidden(k4_tarski(C_173, '#skF_10'(A_174, k1_relat_1(A_174), C_173)), A_174) | ~r2_hidden(C_173, k1_relat_1(A_174)))), inference(cnfTransformation, [status(thm)], [f_135])).
% 13.73/5.44  tff(c_42, plain, (![D_34, A_29]: (r2_hidden(D_34, k2_tarski(A_29, D_34)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 13.73/5.44  tff(c_330, plain, (![C_125, A_126, D_127]: (r2_hidden(C_125, k1_relat_1(A_126)) | ~r2_hidden(k4_tarski(C_125, D_127), A_126))), inference(cnfTransformation, [status(thm)], [f_135])).
% 13.73/5.44  tff(c_340, plain, (![C_125, A_29, D_127]: (r2_hidden(C_125, k1_relat_1(k2_tarski(A_29, k4_tarski(C_125, D_127)))))), inference(resolution, [status(thm)], [c_42, c_330])).
% 13.73/5.44  tff(c_64, plain, (![A_39, B_40]: (r2_hidden('#skF_6'(A_39, B_40), B_40) | ~r2_hidden(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_121])).
% 13.73/5.44  tff(c_34, plain, (![A_23]: (r1_xboole_0(A_23, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.73/5.44  tff(c_290, plain, (![A_118, B_119, C_120]: (~r1_xboole_0(A_118, B_119) | ~r2_hidden(C_120, B_119) | ~r2_hidden(C_120, A_118))), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.73/5.44  tff(c_294, plain, (![C_121, A_122]: (~r2_hidden(C_121, k1_xboole_0) | ~r2_hidden(C_121, A_122))), inference(resolution, [status(thm)], [c_34, c_290])).
% 13.73/5.44  tff(c_456, plain, (![A_143, A_144]: (~r2_hidden('#skF_6'(A_143, k1_xboole_0), A_144) | ~r2_hidden(A_143, k1_xboole_0))), inference(resolution, [status(thm)], [c_64, c_294])).
% 13.73/5.44  tff(c_473, plain, (![A_143]: (~r2_hidden(A_143, k1_xboole_0))), inference(resolution, [status(thm)], [c_340, c_456])).
% 13.73/5.44  tff(c_951, plain, (![C_175]: (~r2_hidden(C_175, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_931, c_473])).
% 13.73/5.44  tff(c_959, plain, (![A_72]: (~r2_hidden(A_72, k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_86, c_951])).
% 13.73/5.44  tff(c_1015, plain, (![A_176]: (~r2_hidden(A_176, k2_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_959])).
% 13.73/5.44  tff(c_1040, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_1015])).
% 13.73/5.44  tff(c_92, plain, (r1_tarski('#skF_12', '#skF_13')), inference(cnfTransformation, [status(thm)], [f_172])).
% 13.73/5.44  tff(c_153, plain, (k4_xboole_0('#skF_12', '#skF_13')=k1_xboole_0), inference(resolution, [status(thm)], [c_92, c_139])).
% 13.73/5.44  tff(c_66, plain, (![A_46, B_47]: (k6_subset_1(A_46, B_47)=k4_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_123])).
% 13.73/5.44  tff(c_88, plain, (![A_75, B_77]: (r1_tarski(k6_subset_1(k2_relat_1(A_75), k2_relat_1(B_77)), k2_relat_1(k6_subset_1(A_75, B_77))) | ~v1_relat_1(B_77) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_162])).
% 13.73/5.44  tff(c_1225, plain, (![A_185, B_186]: (r1_tarski(k4_xboole_0(k2_relat_1(A_185), k2_relat_1(B_186)), k2_relat_1(k4_xboole_0(A_185, B_186))) | ~v1_relat_1(B_186) | ~v1_relat_1(A_185))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_66, c_88])).
% 13.73/5.44  tff(c_1264, plain, (r1_tarski(k4_xboole_0(k2_relat_1('#skF_12'), k2_relat_1('#skF_13')), k2_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_13') | ~v1_relat_1('#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_153, c_1225])).
% 13.73/5.44  tff(c_1281, plain, (r1_tarski(k4_xboole_0(k2_relat_1('#skF_12'), k2_relat_1('#skF_13')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_1040, c_1264])).
% 13.73/5.44  tff(c_18, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | k4_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 13.73/5.44  tff(c_213, plain, (![B_111, A_112]: (B_111=A_112 | ~r1_tarski(B_111, A_112) | ~r1_tarski(A_112, B_111))), inference(cnfTransformation, [status(thm)], [f_58])).
% 13.73/5.44  tff(c_227, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | k4_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_213])).
% 13.73/5.44  tff(c_1291, plain, (k4_xboole_0(k2_relat_1('#skF_12'), k2_relat_1('#skF_13'))=k1_xboole_0 | k4_xboole_0(k1_xboole_0, k4_xboole_0(k2_relat_1('#skF_12'), k2_relat_1('#skF_13')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_1281, c_227])).
% 13.73/5.44  tff(c_1305, plain, (k4_xboole_0(k2_relat_1('#skF_12'), k2_relat_1('#skF_13'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_155, c_1291])).
% 13.73/5.44  tff(c_16, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_58])).
% 13.73/5.44  tff(c_26, plain, (![C_17, A_15, B_16]: (r1_tarski(C_17, '#skF_3'(A_15, B_16, C_17)) | k2_xboole_0(A_15, C_17)=B_16 | ~r1_tarski(C_17, B_16) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_79])).
% 13.73/5.44  tff(c_3106, plain, (![B_247, A_248, C_249]: (~r1_tarski(B_247, '#skF_3'(A_248, B_247, C_249)) | k2_xboole_0(A_248, C_249)=B_247 | ~r1_tarski(C_249, B_247) | ~r1_tarski(A_248, B_247))), inference(cnfTransformation, [status(thm)], [f_79])).
% 13.73/5.44  tff(c_3114, plain, (![A_15, B_16]: (k2_xboole_0(A_15, B_16)=B_16 | ~r1_tarski(B_16, B_16) | ~r1_tarski(A_15, B_16))), inference(resolution, [status(thm)], [c_26, c_3106])).
% 13.73/5.44  tff(c_3151, plain, (![A_250, B_251]: (k2_xboole_0(A_250, B_251)=B_251 | ~r1_tarski(A_250, B_251))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_3114])).
% 13.73/5.44  tff(c_3655, plain, (![A_259, B_260]: (k2_xboole_0(A_259, B_260)=B_260 | k4_xboole_0(A_259, B_260)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_3151])).
% 13.73/5.44  tff(c_3709, plain, (k2_xboole_0(k2_relat_1('#skF_12'), k2_relat_1('#skF_13'))=k2_relat_1('#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_1305, c_3655])).
% 13.73/5.44  tff(c_36, plain, (![A_24, B_25]: (r1_tarski(A_24, k2_xboole_0(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.73/5.44  tff(c_3906, plain, (r1_tarski(k2_relat_1('#skF_12'), k2_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_3709, c_36])).
% 13.73/5.44  tff(c_272, plain, (![A_117]: (k2_xboole_0(k1_relat_1(A_117), k2_relat_1(A_117))=k3_relat_1(A_117) | ~v1_relat_1(A_117))), inference(cnfTransformation, [status(thm)], [f_139])).
% 13.73/5.44  tff(c_22, plain, (![A_12, C_14, B_13]: (r1_tarski(A_12, k2_xboole_0(C_14, B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_66])).
% 13.73/5.44  tff(c_278, plain, (![A_12, A_117]: (r1_tarski(A_12, k3_relat_1(A_117)) | ~r1_tarski(A_12, k2_relat_1(A_117)) | ~v1_relat_1(A_117))), inference(superposition, [status(thm), theory('equality')], [c_272, c_22])).
% 13.73/5.44  tff(c_983, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_951])).
% 13.73/5.44  tff(c_84, plain, (![A_69, B_71]: (r1_tarski(k6_subset_1(k1_relat_1(A_69), k1_relat_1(B_71)), k1_relat_1(k6_subset_1(A_69, B_71))) | ~v1_relat_1(B_71) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_146])).
% 13.73/5.44  tff(c_1477, plain, (![A_193, B_194]: (r1_tarski(k4_xboole_0(k1_relat_1(A_193), k1_relat_1(B_194)), k1_relat_1(k4_xboole_0(A_193, B_194))) | ~v1_relat_1(B_194) | ~v1_relat_1(A_193))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_66, c_84])).
% 13.73/5.44  tff(c_1522, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_12'), k1_relat_1('#skF_13')), k1_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_13') | ~v1_relat_1('#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_153, c_1477])).
% 13.73/5.44  tff(c_1542, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_12'), k1_relat_1('#skF_13')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_983, c_1522])).
% 13.73/5.44  tff(c_1552, plain, (k4_xboole_0(k1_relat_1('#skF_12'), k1_relat_1('#skF_13'))=k1_xboole_0 | k4_xboole_0(k1_xboole_0, k4_xboole_0(k1_relat_1('#skF_12'), k1_relat_1('#skF_13')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_1542, c_227])).
% 13.73/5.44  tff(c_1566, plain, (k4_xboole_0(k1_relat_1('#skF_12'), k1_relat_1('#skF_13'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_155, c_1552])).
% 13.73/5.44  tff(c_3707, plain, (k2_xboole_0(k1_relat_1('#skF_12'), k1_relat_1('#skF_13'))=k1_relat_1('#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_1566, c_3655])).
% 13.73/5.44  tff(c_3839, plain, (r1_tarski(k1_relat_1('#skF_12'), k1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_3707, c_36])).
% 13.73/5.44  tff(c_284, plain, (![A_117]: (r1_tarski(k1_relat_1(A_117), k3_relat_1(A_117)) | ~v1_relat_1(A_117))), inference(superposition, [status(thm), theory('equality')], [c_272, c_36])).
% 13.73/5.44  tff(c_38, plain, (![A_26, C_28, B_27]: (r1_tarski(k2_xboole_0(A_26, C_28), B_27) | ~r1_tarski(C_28, B_27) | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_95])).
% 13.73/5.44  tff(c_628, plain, (![A_157, B_158]: (k2_xboole_0(A_157, B_158)=A_157 | ~r1_tarski(k2_xboole_0(A_157, B_158), A_157))), inference(resolution, [status(thm)], [c_36, c_213])).
% 13.73/5.44  tff(c_632, plain, (![B_27, C_28]: (k2_xboole_0(B_27, C_28)=B_27 | ~r1_tarski(C_28, B_27) | ~r1_tarski(B_27, B_27))), inference(resolution, [status(thm)], [c_38, c_628])).
% 13.73/5.44  tff(c_649, plain, (![B_159, C_160]: (k2_xboole_0(B_159, C_160)=B_159 | ~r1_tarski(C_160, B_159))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_632])).
% 13.73/5.44  tff(c_1874, plain, (![A_212]: (k2_xboole_0(k3_relat_1(A_212), k1_relat_1(A_212))=k3_relat_1(A_212) | ~v1_relat_1(A_212))), inference(resolution, [status(thm)], [c_284, c_649])).
% 13.73/5.44  tff(c_34958, plain, (![A_43058, A_43059]: (r1_tarski(A_43058, k3_relat_1(A_43059)) | ~r1_tarski(A_43058, k1_relat_1(A_43059)) | ~v1_relat_1(A_43059))), inference(superposition, [status(thm), theory('equality')], [c_1874, c_22])).
% 13.73/5.44  tff(c_82, plain, (![A_68]: (k2_xboole_0(k1_relat_1(A_68), k2_relat_1(A_68))=k3_relat_1(A_68) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_139])).
% 13.73/5.44  tff(c_502, plain, (![A_146, C_147, B_148]: (r1_tarski(k2_xboole_0(A_146, C_147), B_148) | ~r1_tarski(C_147, B_148) | ~r1_tarski(A_146, B_148))), inference(cnfTransformation, [status(thm)], [f_95])).
% 13.73/5.44  tff(c_15543, plain, (![A_27423, B_27424]: (r1_tarski(k3_relat_1(A_27423), B_27424) | ~r1_tarski(k2_relat_1(A_27423), B_27424) | ~r1_tarski(k1_relat_1(A_27423), B_27424) | ~v1_relat_1(A_27423))), inference(superposition, [status(thm), theory('equality')], [c_82, c_502])).
% 13.73/5.44  tff(c_90, plain, (~r1_tarski(k3_relat_1('#skF_12'), k3_relat_1('#skF_13'))), inference(cnfTransformation, [status(thm)], [f_172])).
% 13.73/5.44  tff(c_15643, plain, (~r1_tarski(k2_relat_1('#skF_12'), k3_relat_1('#skF_13')) | ~r1_tarski(k1_relat_1('#skF_12'), k3_relat_1('#skF_13')) | ~v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_15543, c_90])).
% 13.73/5.44  tff(c_15684, plain, (~r1_tarski(k2_relat_1('#skF_12'), k3_relat_1('#skF_13')) | ~r1_tarski(k1_relat_1('#skF_12'), k3_relat_1('#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_15643])).
% 13.73/5.44  tff(c_15710, plain, (~r1_tarski(k1_relat_1('#skF_12'), k3_relat_1('#skF_13'))), inference(splitLeft, [status(thm)], [c_15684])).
% 13.73/5.44  tff(c_34961, plain, (~r1_tarski(k1_relat_1('#skF_12'), k1_relat_1('#skF_13')) | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_34958, c_15710])).
% 13.73/5.44  tff(c_35004, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_3839, c_34961])).
% 13.73/5.44  tff(c_35005, plain, (~r1_tarski(k2_relat_1('#skF_12'), k3_relat_1('#skF_13'))), inference(splitRight, [status(thm)], [c_15684])).
% 13.73/5.44  tff(c_35009, plain, (~r1_tarski(k2_relat_1('#skF_12'), k2_relat_1('#skF_13')) | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_278, c_35005])).
% 13.73/5.44  tff(c_35019, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_3906, c_35009])).
% 13.73/5.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.73/5.44  
% 13.73/5.44  Inference rules
% 13.73/5.44  ----------------------
% 13.73/5.44  #Ref     : 0
% 13.73/5.44  #Sup     : 7139
% 13.73/5.44  #Fact    : 16
% 13.73/5.44  #Define  : 0
% 13.73/5.44  #Split   : 11
% 13.73/5.44  #Chain   : 0
% 13.73/5.44  #Close   : 0
% 13.73/5.44  
% 13.73/5.44  Ordering : KBO
% 13.73/5.44  
% 13.73/5.44  Simplification rules
% 13.73/5.44  ----------------------
% 13.73/5.44  #Subsume      : 1530
% 13.73/5.44  #Demod        : 5337
% 13.73/5.44  #Tautology    : 3582
% 13.73/5.44  #SimpNegUnit  : 25
% 13.73/5.44  #BackRed      : 4
% 13.73/5.44  
% 13.73/5.44  #Partial instantiations: 24432
% 13.73/5.44  #Strategies tried      : 1
% 13.73/5.44  
% 13.73/5.44  Timing (in seconds)
% 13.73/5.44  ----------------------
% 13.73/5.44  Preprocessing        : 0.36
% 13.73/5.44  Parsing              : 0.18
% 13.73/5.44  CNF conversion       : 0.03
% 13.73/5.44  Main loop            : 4.31
% 13.73/5.44  Inferencing          : 1.15
% 13.73/5.44  Reduction            : 1.68
% 13.73/5.44  Demodulation         : 1.32
% 13.73/5.44  BG Simplification    : 0.09
% 13.73/5.44  Subsumption          : 1.18
% 13.73/5.44  Abstraction          : 0.12
% 13.73/5.44  MUC search           : 0.00
% 13.73/5.44  Cooper               : 0.00
% 13.73/5.44  Total                : 4.72
% 13.73/5.44  Index Insertion      : 0.00
% 13.73/5.44  Index Deletion       : 0.00
% 13.73/5.44  Index Matching       : 0.00
% 13.73/5.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
