%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:56 EST 2020

% Result     : Theorem 15.84s
% Output     : CNFRefutation 15.84s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 378 expanded)
%              Number of leaves         :   37 ( 139 expanded)
%              Depth                    :   22
%              Number of atoms          :  147 ( 524 expanded)
%              Number of equality atoms :   60 ( 204 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_111,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_94,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_96,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_92,plain,
    ( ~ r2_hidden('#skF_6','#skF_7')
    | r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_108,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_36,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_3'(A_12,B_13),B_13)
      | r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_48,plain,(
    ! [A_25,B_26] : r1_xboole_0(k4_xboole_0(A_25,B_26),B_26) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_146,plain,(
    ! [A_64,B_65] :
      ( k4_xboole_0(A_64,B_65) = A_64
      | ~ r1_xboole_0(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_150,plain,(
    ! [A_25,B_26] : k4_xboole_0(k4_xboole_0(A_25,B_26),B_26) = k4_xboole_0(A_25,B_26) ),
    inference(resolution,[status(thm)],[c_48,c_146])).

tff(c_215,plain,(
    ! [A_85,B_86] :
      ( k4_xboole_0(A_85,k1_tarski(B_86)) = A_85
      | r2_hidden(B_86,A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_44,plain,(
    ! [A_21,B_22] : r1_tarski(k4_xboole_0(A_21,B_22),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_230,plain,(
    ! [A_87,B_88] :
      ( r1_tarski(A_87,A_87)
      | r2_hidden(B_88,A_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_44])).

tff(c_248,plain,(
    r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_230,c_108])).

tff(c_42,plain,(
    ! [A_19,B_20] :
      ( k3_xboole_0(A_19,B_20) = A_19
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_276,plain,(
    k3_xboole_0('#skF_7','#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_248,c_42])).

tff(c_249,plain,(
    ! [A_89,B_90] : k4_xboole_0(A_89,k4_xboole_0(A_89,B_90)) = k3_xboole_0(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_320,plain,(
    ! [A_95,B_96] : r1_xboole_0(k3_xboole_0(A_95,B_96),k4_xboole_0(A_95,B_96)) ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_48])).

tff(c_326,plain,(
    r1_xboole_0('#skF_7',k4_xboole_0('#skF_7','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_320])).

tff(c_50,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(A_27,B_28) = A_27
      | ~ r1_xboole_0(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_343,plain,(
    k4_xboole_0('#skF_7',k4_xboole_0('#skF_7','#skF_7')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_326,c_50])).

tff(c_46,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k4_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_350,plain,(
    k3_xboole_0('#skF_7',k4_xboole_0('#skF_7','#skF_7')) = k4_xboole_0('#skF_7','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_46])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_151,plain,(
    ! [A_66,B_67] :
      ( k3_xboole_0(A_66,B_67) = A_66
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_503,plain,(
    ! [A_112,B_113] : k3_xboole_0(k4_xboole_0(A_112,B_113),A_112) = k4_xboole_0(A_112,B_113) ),
    inference(resolution,[status(thm)],[c_44,c_151])).

tff(c_338,plain,(
    ! [A_1,B_2] : r1_xboole_0(k3_xboole_0(A_1,B_2),k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_320])).

tff(c_512,plain,(
    ! [A_112,B_113] : r1_xboole_0(k4_xboole_0(A_112,B_113),k4_xboole_0(A_112,k4_xboole_0(A_112,B_113))) ),
    inference(superposition,[status(thm),theory(equality)],[c_503,c_338])).

tff(c_588,plain,(
    ! [A_116,B_117] : r1_xboole_0(k4_xboole_0(A_116,B_117),k3_xboole_0(A_116,B_117)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_512])).

tff(c_612,plain,(
    ! [A_1,B_2] : r1_xboole_0(k4_xboole_0(A_1,B_2),k3_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_588])).

tff(c_1040,plain,(
    r1_xboole_0(k4_xboole_0(k4_xboole_0('#skF_7','#skF_7'),'#skF_7'),k4_xboole_0('#skF_7','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_612])).

tff(c_1076,plain,(
    r1_xboole_0(k4_xboole_0('#skF_7','#skF_7'),k4_xboole_0('#skF_7','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_1040])).

tff(c_34,plain,(
    ! [A_12,B_13,C_16] :
      ( ~ r1_xboole_0(A_12,B_13)
      | ~ r2_hidden(C_16,B_13)
      | ~ r2_hidden(C_16,A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1091,plain,(
    ! [C_16] : ~ r2_hidden(C_16,k4_xboole_0('#skF_7','#skF_7')) ),
    inference(resolution,[status(thm)],[c_1076,c_34])).

tff(c_1093,plain,(
    ! [C_142] : ~ r2_hidden(C_142,k4_xboole_0('#skF_7','#skF_7')) ),
    inference(resolution,[status(thm)],[c_1076,c_34])).

tff(c_1117,plain,(
    ! [A_143] : r1_xboole_0(A_143,k4_xboole_0('#skF_7','#skF_7')) ),
    inference(resolution,[status(thm)],[c_36,c_1093])).

tff(c_1124,plain,(
    ! [A_143] : k4_xboole_0(A_143,k4_xboole_0('#skF_7','#skF_7')) = A_143 ),
    inference(resolution,[status(thm)],[c_1117,c_50])).

tff(c_1134,plain,(
    ! [A_145] : k4_xboole_0(A_145,k4_xboole_0('#skF_7','#skF_7')) = A_145 ),
    inference(resolution,[status(thm)],[c_1117,c_50])).

tff(c_155,plain,(
    ! [A_21,B_22] : k3_xboole_0(k4_xboole_0(A_21,B_22),A_21) = k4_xboole_0(A_21,B_22) ),
    inference(resolution,[status(thm)],[c_44,c_151])).

tff(c_1165,plain,(
    ! [A_145] : k4_xboole_0(A_145,k4_xboole_0('#skF_7','#skF_7')) = k3_xboole_0(A_145,A_145) ),
    inference(superposition,[status(thm),theory(equality)],[c_1134,c_155])).

tff(c_1237,plain,(
    ! [A_150] : k3_xboole_0(A_150,A_150) = A_150 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1124,c_1165])).

tff(c_40,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1258,plain,(
    ! [A_150] : k5_xboole_0(A_150,A_150) = k4_xboole_0(A_150,A_150) ),
    inference(superposition,[status(thm),theory(equality)],[c_1237,c_40])).

tff(c_469,plain,(
    ! [A_107,B_108] : k5_xboole_0(A_107,k3_xboole_0(A_107,B_108)) = k4_xboole_0(A_107,B_108) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_831,plain,(
    ! [A_131,B_132] : k5_xboole_0(A_131,k3_xboole_0(B_132,A_131)) = k4_xboole_0(A_131,B_132) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_469])).

tff(c_844,plain,(
    ! [A_21,B_22] : k5_xboole_0(A_21,k4_xboole_0(A_21,B_22)) = k4_xboole_0(A_21,k4_xboole_0(A_21,B_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_831])).

tff(c_864,plain,(
    ! [A_21,B_22] : k5_xboole_0(A_21,k4_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_844])).

tff(c_3501,plain,(
    ! [A_212] : k5_xboole_0(A_212,A_212) = k3_xboole_0(A_212,k4_xboole_0('#skF_7','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1134,c_864])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3601,plain,(
    ! [D_8,A_212] :
      ( r2_hidden(D_8,k4_xboole_0('#skF_7','#skF_7'))
      | ~ r2_hidden(D_8,k5_xboole_0(A_212,A_212)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3501,c_6])).

tff(c_3656,plain,(
    ! [D_8,A_212] :
      ( r2_hidden(D_8,k4_xboole_0('#skF_7','#skF_7'))
      | ~ r2_hidden(D_8,k4_xboole_0(A_212,A_212)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1258,c_3601])).

tff(c_3662,plain,(
    ! [D_213,A_214] : ~ r2_hidden(D_213,k4_xboole_0(A_214,A_214)) ),
    inference(negUnitSimplification,[status(thm)],[c_1091,c_3656])).

tff(c_3707,plain,(
    ! [A_215,A_216] : r1_xboole_0(A_215,k4_xboole_0(A_216,A_216)) ),
    inference(resolution,[status(thm)],[c_36,c_3662])).

tff(c_3725,plain,(
    ! [A_215,A_216] : k4_xboole_0(A_215,k4_xboole_0(A_216,A_216)) = A_215 ),
    inference(resolution,[status(thm)],[c_3707,c_50])).

tff(c_88,plain,(
    ! [A_46,B_47] :
      ( k4_xboole_0(A_46,k1_tarski(B_47)) = A_46
      | r2_hidden(B_47,A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_11037,plain,(
    ! [A_12913,B_12914] :
      ( k4_xboole_0(A_12913,A_12913) = k3_xboole_0(A_12913,k1_tarski(B_12914))
      | r2_hidden(B_12914,A_12913) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_249])).

tff(c_287,plain,(
    ! [A_91,B_92] : r1_tarski(k3_xboole_0(A_91,B_92),A_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_44])).

tff(c_1746,plain,(
    ! [A_175,B_176] : k3_xboole_0(k3_xboole_0(A_175,B_176),A_175) = k3_xboole_0(A_175,B_176) ),
    inference(resolution,[status(thm)],[c_287,c_42])).

tff(c_484,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_469])).

tff(c_1769,plain,(
    ! [A_175,B_176] : k5_xboole_0(A_175,k3_xboole_0(A_175,B_176)) = k4_xboole_0(A_175,k3_xboole_0(A_175,B_176)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1746,c_484])).

tff(c_2097,plain,(
    ! [A_181,B_182] : k4_xboole_0(A_181,k3_xboole_0(A_181,B_182)) = k4_xboole_0(A_181,B_182) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1769])).

tff(c_2166,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2097])).

tff(c_11115,plain,(
    ! [B_12914,A_12913] :
      ( k4_xboole_0(k1_tarski(B_12914),k4_xboole_0(A_12913,A_12913)) = k4_xboole_0(k1_tarski(B_12914),A_12913)
      | r2_hidden(B_12914,A_12913) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11037,c_2166])).

tff(c_58286,plain,(
    ! [B_79195,A_79196] :
      ( k4_xboole_0(k1_tarski(B_79195),A_79196) = k1_tarski(B_79195)
      | r2_hidden(B_79195,A_79196) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3725,c_11115])).

tff(c_90,plain,
    ( k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') != k1_tarski('#skF_6')
    | r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_145,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') != k1_tarski('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_58695,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_58286,c_145])).

tff(c_58880,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_58695])).

tff(c_58881,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_78,plain,(
    ! [A_36] : k2_tarski(A_36,A_36) = k1_tarski(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_58917,plain,(
    ! [A_79536,B_79537] : k1_enumset1(A_79536,A_79536,B_79537) = k2_tarski(A_79536,B_79537) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_58,plain,(
    ! [E_35,A_29,C_31] : r2_hidden(E_35,k1_enumset1(A_29,E_35,C_31)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_58935,plain,(
    ! [A_79538,B_79539] : r2_hidden(A_79538,k2_tarski(A_79538,B_79539)) ),
    inference(superposition,[status(thm),theory(equality)],[c_58917,c_58])).

tff(c_58938,plain,(
    ! [A_36] : r2_hidden(A_36,k1_tarski(A_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_58935])).

tff(c_58882,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_94,plain,
    ( k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') != k1_tarski('#skF_6')
    | k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_58962,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58882,c_94])).

tff(c_58969,plain,(
    r1_xboole_0(k1_tarski('#skF_8'),'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_58962,c_48])).

tff(c_59674,plain,(
    ! [A_79586,B_79587,C_79588] :
      ( ~ r1_xboole_0(A_79586,B_79587)
      | ~ r2_hidden(C_79588,B_79587)
      | ~ r2_hidden(C_79588,A_79586) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_59714,plain,(
    ! [C_79589] :
      ( ~ r2_hidden(C_79589,'#skF_9')
      | ~ r2_hidden(C_79589,k1_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_58969,c_59674])).

tff(c_59734,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_58938,c_59714])).

tff(c_59744,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58881,c_59734])).

tff(c_59745,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_59784,plain,(
    ! [A_79601,B_79602] : k1_enumset1(A_79601,A_79601,B_79602) = k2_tarski(A_79601,B_79602) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_56,plain,(
    ! [E_35,A_29,B_30] : r2_hidden(E_35,k1_enumset1(A_29,B_30,E_35)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_59803,plain,(
    ! [B_79605,A_79606] : r2_hidden(B_79605,k2_tarski(A_79606,B_79605)) ),
    inference(superposition,[status(thm),theory(equality)],[c_59784,c_56])).

tff(c_59806,plain,(
    ! [A_36] : r2_hidden(A_36,k1_tarski(A_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_59803])).

tff(c_59746,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_96,plain,
    ( ~ r2_hidden('#skF_6','#skF_7')
    | k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_59814,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59746,c_96])).

tff(c_59821,plain,(
    r1_xboole_0(k1_tarski('#skF_8'),'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_59814,c_48])).

tff(c_60518,plain,(
    ! [A_79663,B_79664,C_79665] :
      ( ~ r1_xboole_0(A_79663,B_79664)
      | ~ r2_hidden(C_79665,B_79664)
      | ~ r2_hidden(C_79665,A_79663) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_60549,plain,(
    ! [C_79666] :
      ( ~ r2_hidden(C_79666,'#skF_9')
      | ~ r2_hidden(C_79666,k1_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_59821,c_60518])).

tff(c_60569,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_59806,c_60549])).

tff(c_60579,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59745,c_60569])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:03:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.84/7.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.84/7.65  
% 15.84/7.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.84/7.65  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_5
% 15.84/7.65  
% 15.84/7.65  %Foreground sorts:
% 15.84/7.65  
% 15.84/7.65  
% 15.84/7.65  %Background operators:
% 15.84/7.65  
% 15.84/7.65  
% 15.84/7.65  %Foreground operators:
% 15.84/7.65  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 15.84/7.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.84/7.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.84/7.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 15.84/7.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.84/7.65  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 15.84/7.65  tff('#skF_7', type, '#skF_7': $i).
% 15.84/7.65  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 15.84/7.65  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 15.84/7.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.84/7.65  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 15.84/7.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 15.84/7.65  tff('#skF_6', type, '#skF_6': $i).
% 15.84/7.65  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 15.84/7.65  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 15.84/7.65  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 15.84/7.65  tff('#skF_9', type, '#skF_9': $i).
% 15.84/7.65  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 15.84/7.65  tff('#skF_8', type, '#skF_8': $i).
% 15.84/7.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.84/7.65  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 15.84/7.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.84/7.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.84/7.65  
% 15.84/7.67  tff(f_111, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 15.84/7.67  tff(f_61, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 15.84/7.67  tff(f_73, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 15.84/7.67  tff(f_77, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 15.84/7.67  tff(f_105, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 15.84/7.67  tff(f_69, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 15.84/7.67  tff(f_67, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 15.84/7.67  tff(f_71, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 15.84/7.67  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 15.84/7.67  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 15.84/7.67  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 15.84/7.67  tff(f_94, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 15.84/7.67  tff(f_96, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 15.84/7.67  tff(f_92, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 15.84/7.67  tff(c_92, plain, (~r2_hidden('#skF_6', '#skF_7') | r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_111])).
% 15.84/7.67  tff(c_108, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_92])).
% 15.84/7.67  tff(c_36, plain, (![A_12, B_13]: (r2_hidden('#skF_3'(A_12, B_13), B_13) | r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.84/7.67  tff(c_48, plain, (![A_25, B_26]: (r1_xboole_0(k4_xboole_0(A_25, B_26), B_26))), inference(cnfTransformation, [status(thm)], [f_73])).
% 15.84/7.67  tff(c_146, plain, (![A_64, B_65]: (k4_xboole_0(A_64, B_65)=A_64 | ~r1_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_77])).
% 15.84/7.67  tff(c_150, plain, (![A_25, B_26]: (k4_xboole_0(k4_xboole_0(A_25, B_26), B_26)=k4_xboole_0(A_25, B_26))), inference(resolution, [status(thm)], [c_48, c_146])).
% 15.84/7.67  tff(c_215, plain, (![A_85, B_86]: (k4_xboole_0(A_85, k1_tarski(B_86))=A_85 | r2_hidden(B_86, A_85))), inference(cnfTransformation, [status(thm)], [f_105])).
% 15.84/7.67  tff(c_44, plain, (![A_21, B_22]: (r1_tarski(k4_xboole_0(A_21, B_22), A_21))), inference(cnfTransformation, [status(thm)], [f_69])).
% 15.84/7.67  tff(c_230, plain, (![A_87, B_88]: (r1_tarski(A_87, A_87) | r2_hidden(B_88, A_87))), inference(superposition, [status(thm), theory('equality')], [c_215, c_44])).
% 15.84/7.67  tff(c_248, plain, (r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_230, c_108])).
% 15.84/7.67  tff(c_42, plain, (![A_19, B_20]: (k3_xboole_0(A_19, B_20)=A_19 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.84/7.67  tff(c_276, plain, (k3_xboole_0('#skF_7', '#skF_7')='#skF_7'), inference(resolution, [status(thm)], [c_248, c_42])).
% 15.84/7.67  tff(c_249, plain, (![A_89, B_90]: (k4_xboole_0(A_89, k4_xboole_0(A_89, B_90))=k3_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_71])).
% 15.84/7.67  tff(c_320, plain, (![A_95, B_96]: (r1_xboole_0(k3_xboole_0(A_95, B_96), k4_xboole_0(A_95, B_96)))), inference(superposition, [status(thm), theory('equality')], [c_249, c_48])).
% 15.84/7.67  tff(c_326, plain, (r1_xboole_0('#skF_7', k4_xboole_0('#skF_7', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_276, c_320])).
% 15.84/7.67  tff(c_50, plain, (![A_27, B_28]: (k4_xboole_0(A_27, B_28)=A_27 | ~r1_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_77])).
% 15.84/7.67  tff(c_343, plain, (k4_xboole_0('#skF_7', k4_xboole_0('#skF_7', '#skF_7'))='#skF_7'), inference(resolution, [status(thm)], [c_326, c_50])).
% 15.84/7.67  tff(c_46, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k4_xboole_0(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_71])).
% 15.84/7.67  tff(c_350, plain, (k3_xboole_0('#skF_7', k4_xboole_0('#skF_7', '#skF_7'))=k4_xboole_0('#skF_7', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_343, c_46])).
% 15.84/7.67  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 15.84/7.67  tff(c_151, plain, (![A_66, B_67]: (k3_xboole_0(A_66, B_67)=A_66 | ~r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.84/7.67  tff(c_503, plain, (![A_112, B_113]: (k3_xboole_0(k4_xboole_0(A_112, B_113), A_112)=k4_xboole_0(A_112, B_113))), inference(resolution, [status(thm)], [c_44, c_151])).
% 15.84/7.67  tff(c_338, plain, (![A_1, B_2]: (r1_xboole_0(k3_xboole_0(A_1, B_2), k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_320])).
% 15.84/7.67  tff(c_512, plain, (![A_112, B_113]: (r1_xboole_0(k4_xboole_0(A_112, B_113), k4_xboole_0(A_112, k4_xboole_0(A_112, B_113))))), inference(superposition, [status(thm), theory('equality')], [c_503, c_338])).
% 15.84/7.67  tff(c_588, plain, (![A_116, B_117]: (r1_xboole_0(k4_xboole_0(A_116, B_117), k3_xboole_0(A_116, B_117)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_512])).
% 15.84/7.67  tff(c_612, plain, (![A_1, B_2]: (r1_xboole_0(k4_xboole_0(A_1, B_2), k3_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_588])).
% 15.84/7.67  tff(c_1040, plain, (r1_xboole_0(k4_xboole_0(k4_xboole_0('#skF_7', '#skF_7'), '#skF_7'), k4_xboole_0('#skF_7', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_350, c_612])).
% 15.84/7.67  tff(c_1076, plain, (r1_xboole_0(k4_xboole_0('#skF_7', '#skF_7'), k4_xboole_0('#skF_7', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_1040])).
% 15.84/7.67  tff(c_34, plain, (![A_12, B_13, C_16]: (~r1_xboole_0(A_12, B_13) | ~r2_hidden(C_16, B_13) | ~r2_hidden(C_16, A_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.84/7.67  tff(c_1091, plain, (![C_16]: (~r2_hidden(C_16, k4_xboole_0('#skF_7', '#skF_7')))), inference(resolution, [status(thm)], [c_1076, c_34])).
% 15.84/7.67  tff(c_1093, plain, (![C_142]: (~r2_hidden(C_142, k4_xboole_0('#skF_7', '#skF_7')))), inference(resolution, [status(thm)], [c_1076, c_34])).
% 15.84/7.67  tff(c_1117, plain, (![A_143]: (r1_xboole_0(A_143, k4_xboole_0('#skF_7', '#skF_7')))), inference(resolution, [status(thm)], [c_36, c_1093])).
% 15.84/7.67  tff(c_1124, plain, (![A_143]: (k4_xboole_0(A_143, k4_xboole_0('#skF_7', '#skF_7'))=A_143)), inference(resolution, [status(thm)], [c_1117, c_50])).
% 15.84/7.67  tff(c_1134, plain, (![A_145]: (k4_xboole_0(A_145, k4_xboole_0('#skF_7', '#skF_7'))=A_145)), inference(resolution, [status(thm)], [c_1117, c_50])).
% 15.84/7.67  tff(c_155, plain, (![A_21, B_22]: (k3_xboole_0(k4_xboole_0(A_21, B_22), A_21)=k4_xboole_0(A_21, B_22))), inference(resolution, [status(thm)], [c_44, c_151])).
% 15.84/7.67  tff(c_1165, plain, (![A_145]: (k4_xboole_0(A_145, k4_xboole_0('#skF_7', '#skF_7'))=k3_xboole_0(A_145, A_145))), inference(superposition, [status(thm), theory('equality')], [c_1134, c_155])).
% 15.84/7.67  tff(c_1237, plain, (![A_150]: (k3_xboole_0(A_150, A_150)=A_150)), inference(demodulation, [status(thm), theory('equality')], [c_1124, c_1165])).
% 15.84/7.67  tff(c_40, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 15.84/7.67  tff(c_1258, plain, (![A_150]: (k5_xboole_0(A_150, A_150)=k4_xboole_0(A_150, A_150))), inference(superposition, [status(thm), theory('equality')], [c_1237, c_40])).
% 15.84/7.67  tff(c_469, plain, (![A_107, B_108]: (k5_xboole_0(A_107, k3_xboole_0(A_107, B_108))=k4_xboole_0(A_107, B_108))), inference(cnfTransformation, [status(thm)], [f_63])).
% 15.84/7.67  tff(c_831, plain, (![A_131, B_132]: (k5_xboole_0(A_131, k3_xboole_0(B_132, A_131))=k4_xboole_0(A_131, B_132))), inference(superposition, [status(thm), theory('equality')], [c_2, c_469])).
% 15.84/7.67  tff(c_844, plain, (![A_21, B_22]: (k5_xboole_0(A_21, k4_xboole_0(A_21, B_22))=k4_xboole_0(A_21, k4_xboole_0(A_21, B_22)))), inference(superposition, [status(thm), theory('equality')], [c_155, c_831])).
% 15.84/7.67  tff(c_864, plain, (![A_21, B_22]: (k5_xboole_0(A_21, k4_xboole_0(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_844])).
% 15.84/7.67  tff(c_3501, plain, (![A_212]: (k5_xboole_0(A_212, A_212)=k3_xboole_0(A_212, k4_xboole_0('#skF_7', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_1134, c_864])).
% 15.84/7.67  tff(c_6, plain, (![D_8, B_4, A_3]: (r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 15.84/7.67  tff(c_3601, plain, (![D_8, A_212]: (r2_hidden(D_8, k4_xboole_0('#skF_7', '#skF_7')) | ~r2_hidden(D_8, k5_xboole_0(A_212, A_212)))), inference(superposition, [status(thm), theory('equality')], [c_3501, c_6])).
% 15.84/7.67  tff(c_3656, plain, (![D_8, A_212]: (r2_hidden(D_8, k4_xboole_0('#skF_7', '#skF_7')) | ~r2_hidden(D_8, k4_xboole_0(A_212, A_212)))), inference(demodulation, [status(thm), theory('equality')], [c_1258, c_3601])).
% 15.84/7.67  tff(c_3662, plain, (![D_213, A_214]: (~r2_hidden(D_213, k4_xboole_0(A_214, A_214)))), inference(negUnitSimplification, [status(thm)], [c_1091, c_3656])).
% 15.84/7.67  tff(c_3707, plain, (![A_215, A_216]: (r1_xboole_0(A_215, k4_xboole_0(A_216, A_216)))), inference(resolution, [status(thm)], [c_36, c_3662])).
% 15.84/7.67  tff(c_3725, plain, (![A_215, A_216]: (k4_xboole_0(A_215, k4_xboole_0(A_216, A_216))=A_215)), inference(resolution, [status(thm)], [c_3707, c_50])).
% 15.84/7.67  tff(c_88, plain, (![A_46, B_47]: (k4_xboole_0(A_46, k1_tarski(B_47))=A_46 | r2_hidden(B_47, A_46))), inference(cnfTransformation, [status(thm)], [f_105])).
% 15.84/7.67  tff(c_11037, plain, (![A_12913, B_12914]: (k4_xboole_0(A_12913, A_12913)=k3_xboole_0(A_12913, k1_tarski(B_12914)) | r2_hidden(B_12914, A_12913))), inference(superposition, [status(thm), theory('equality')], [c_88, c_249])).
% 15.84/7.67  tff(c_287, plain, (![A_91, B_92]: (r1_tarski(k3_xboole_0(A_91, B_92), A_91))), inference(superposition, [status(thm), theory('equality')], [c_249, c_44])).
% 15.84/7.67  tff(c_1746, plain, (![A_175, B_176]: (k3_xboole_0(k3_xboole_0(A_175, B_176), A_175)=k3_xboole_0(A_175, B_176))), inference(resolution, [status(thm)], [c_287, c_42])).
% 15.84/7.67  tff(c_484, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_469])).
% 15.84/7.67  tff(c_1769, plain, (![A_175, B_176]: (k5_xboole_0(A_175, k3_xboole_0(A_175, B_176))=k4_xboole_0(A_175, k3_xboole_0(A_175, B_176)))), inference(superposition, [status(thm), theory('equality')], [c_1746, c_484])).
% 15.84/7.67  tff(c_2097, plain, (![A_181, B_182]: (k4_xboole_0(A_181, k3_xboole_0(A_181, B_182))=k4_xboole_0(A_181, B_182))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1769])).
% 15.84/7.67  tff(c_2166, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2097])).
% 15.84/7.67  tff(c_11115, plain, (![B_12914, A_12913]: (k4_xboole_0(k1_tarski(B_12914), k4_xboole_0(A_12913, A_12913))=k4_xboole_0(k1_tarski(B_12914), A_12913) | r2_hidden(B_12914, A_12913))), inference(superposition, [status(thm), theory('equality')], [c_11037, c_2166])).
% 15.84/7.67  tff(c_58286, plain, (![B_79195, A_79196]: (k4_xboole_0(k1_tarski(B_79195), A_79196)=k1_tarski(B_79195) | r2_hidden(B_79195, A_79196))), inference(demodulation, [status(thm), theory('equality')], [c_3725, c_11115])).
% 15.84/7.67  tff(c_90, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')!=k1_tarski('#skF_6') | r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_111])).
% 15.84/7.67  tff(c_145, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')!=k1_tarski('#skF_6')), inference(splitLeft, [status(thm)], [c_90])).
% 15.84/7.67  tff(c_58695, plain, (r2_hidden('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_58286, c_145])).
% 15.84/7.67  tff(c_58880, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108, c_58695])).
% 15.84/7.67  tff(c_58881, plain, (r2_hidden('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_90])).
% 15.84/7.67  tff(c_78, plain, (![A_36]: (k2_tarski(A_36, A_36)=k1_tarski(A_36))), inference(cnfTransformation, [status(thm)], [f_94])).
% 15.84/7.67  tff(c_58917, plain, (![A_79536, B_79537]: (k1_enumset1(A_79536, A_79536, B_79537)=k2_tarski(A_79536, B_79537))), inference(cnfTransformation, [status(thm)], [f_96])).
% 15.84/7.67  tff(c_58, plain, (![E_35, A_29, C_31]: (r2_hidden(E_35, k1_enumset1(A_29, E_35, C_31)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 15.84/7.67  tff(c_58935, plain, (![A_79538, B_79539]: (r2_hidden(A_79538, k2_tarski(A_79538, B_79539)))), inference(superposition, [status(thm), theory('equality')], [c_58917, c_58])).
% 15.84/7.67  tff(c_58938, plain, (![A_36]: (r2_hidden(A_36, k1_tarski(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_78, c_58935])).
% 15.84/7.67  tff(c_58882, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_90])).
% 15.84/7.67  tff(c_94, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')!=k1_tarski('#skF_6') | k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')=k1_tarski('#skF_8')), inference(cnfTransformation, [status(thm)], [f_111])).
% 15.84/7.67  tff(c_58962, plain, (k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_58882, c_94])).
% 15.84/7.67  tff(c_58969, plain, (r1_xboole_0(k1_tarski('#skF_8'), '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_58962, c_48])).
% 15.84/7.67  tff(c_59674, plain, (![A_79586, B_79587, C_79588]: (~r1_xboole_0(A_79586, B_79587) | ~r2_hidden(C_79588, B_79587) | ~r2_hidden(C_79588, A_79586))), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.84/7.67  tff(c_59714, plain, (![C_79589]: (~r2_hidden(C_79589, '#skF_9') | ~r2_hidden(C_79589, k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_58969, c_59674])).
% 15.84/7.67  tff(c_59734, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_58938, c_59714])).
% 15.84/7.67  tff(c_59744, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58881, c_59734])).
% 15.84/7.67  tff(c_59745, plain, (r2_hidden('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_92])).
% 15.84/7.67  tff(c_59784, plain, (![A_79601, B_79602]: (k1_enumset1(A_79601, A_79601, B_79602)=k2_tarski(A_79601, B_79602))), inference(cnfTransformation, [status(thm)], [f_96])).
% 15.84/7.67  tff(c_56, plain, (![E_35, A_29, B_30]: (r2_hidden(E_35, k1_enumset1(A_29, B_30, E_35)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 15.84/7.67  tff(c_59803, plain, (![B_79605, A_79606]: (r2_hidden(B_79605, k2_tarski(A_79606, B_79605)))), inference(superposition, [status(thm), theory('equality')], [c_59784, c_56])).
% 15.84/7.67  tff(c_59806, plain, (![A_36]: (r2_hidden(A_36, k1_tarski(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_78, c_59803])).
% 15.84/7.67  tff(c_59746, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_92])).
% 15.84/7.67  tff(c_96, plain, (~r2_hidden('#skF_6', '#skF_7') | k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')=k1_tarski('#skF_8')), inference(cnfTransformation, [status(thm)], [f_111])).
% 15.84/7.67  tff(c_59814, plain, (k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_59746, c_96])).
% 15.84/7.67  tff(c_59821, plain, (r1_xboole_0(k1_tarski('#skF_8'), '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_59814, c_48])).
% 15.84/7.67  tff(c_60518, plain, (![A_79663, B_79664, C_79665]: (~r1_xboole_0(A_79663, B_79664) | ~r2_hidden(C_79665, B_79664) | ~r2_hidden(C_79665, A_79663))), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.84/7.67  tff(c_60549, plain, (![C_79666]: (~r2_hidden(C_79666, '#skF_9') | ~r2_hidden(C_79666, k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_59821, c_60518])).
% 15.84/7.67  tff(c_60569, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_59806, c_60549])).
% 15.84/7.67  tff(c_60579, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59745, c_60569])).
% 15.84/7.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.84/7.67  
% 15.84/7.67  Inference rules
% 15.84/7.67  ----------------------
% 15.84/7.67  #Ref     : 0
% 15.84/7.67  #Sup     : 11926
% 15.84/7.67  #Fact    : 102
% 15.84/7.67  #Define  : 0
% 15.84/7.67  #Split   : 2
% 15.84/7.67  #Chain   : 0
% 15.84/7.67  #Close   : 0
% 15.84/7.67  
% 15.84/7.67  Ordering : KBO
% 15.84/7.67  
% 15.84/7.67  Simplification rules
% 15.84/7.67  ----------------------
% 15.84/7.67  #Subsume      : 3492
% 15.84/7.67  #Demod        : 7592
% 15.84/7.67  #Tautology    : 4611
% 15.84/7.67  #SimpNegUnit  : 677
% 15.84/7.67  #BackRed      : 22
% 15.84/7.67  
% 15.84/7.67  #Partial instantiations: 36159
% 15.84/7.67  #Strategies tried      : 1
% 15.84/7.67  
% 15.84/7.67  Timing (in seconds)
% 15.84/7.67  ----------------------
% 15.84/7.67  Preprocessing        : 0.35
% 15.84/7.67  Parsing              : 0.18
% 15.84/7.67  CNF conversion       : 0.03
% 15.84/7.67  Main loop            : 6.53
% 15.84/7.67  Inferencing          : 2.02
% 15.84/7.67  Reduction            : 2.80
% 15.84/7.67  Demodulation         : 2.36
% 15.84/7.67  BG Simplification    : 0.17
% 15.84/7.67  Subsumption          : 1.18
% 15.84/7.67  Abstraction          : 0.27
% 15.84/7.67  MUC search           : 0.00
% 15.84/7.67  Cooper               : 0.00
% 15.84/7.67  Total                : 6.93
% 15.84/7.68  Index Insertion      : 0.00
% 15.84/7.68  Index Deletion       : 0.00
% 15.84/7.68  Index Matching       : 0.00
% 15.84/7.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
