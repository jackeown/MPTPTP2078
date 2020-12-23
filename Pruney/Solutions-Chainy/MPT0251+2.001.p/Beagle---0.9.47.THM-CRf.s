%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:46 EST 2020

% Result     : Theorem 10.86s
% Output     : CNFRefutation 10.93s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 294 expanded)
%              Number of leaves         :   41 ( 114 expanded)
%              Depth                    :   19
%              Number of atoms          :  131 ( 386 expanded)
%              Number of equality atoms :   58 ( 208 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_122,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_85,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_101,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_117,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_95,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_99,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_93,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_83,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_91,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_495,plain,(
    ! [A_109,B_110] :
      ( r2_hidden('#skF_3'(A_109,B_110),B_110)
      | r1_xboole_0(A_109,B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_502,plain,(
    ! [B_110,A_109] :
      ( ~ v1_xboole_0(B_110)
      | r1_xboole_0(A_109,B_110) ) ),
    inference(resolution,[status(thm)],[c_495,c_4])).

tff(c_66,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_32,plain,(
    ! [A_26] : k2_xboole_0(A_26,k1_xboole_0) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_3'(A_12,B_13),A_12)
      | r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_46,plain,(
    ! [B_38,A_37] : k2_tarski(B_38,A_37) = k2_tarski(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_228,plain,(
    ! [A_91,B_92] : k3_tarski(k2_tarski(A_91,B_92)) = k2_xboole_0(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_334,plain,(
    ! [A_103,B_104] : k3_tarski(k2_tarski(A_103,B_104)) = k2_xboole_0(B_104,A_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_228])).

tff(c_62,plain,(
    ! [A_56,B_57] : k3_tarski(k2_tarski(A_56,B_57)) = k2_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_361,plain,(
    ! [B_105,A_106] : k2_xboole_0(B_105,A_106) = k2_xboole_0(A_106,B_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_62])).

tff(c_444,plain,(
    ! [A_107] : k2_xboole_0(k1_xboole_0,A_107) = A_107 ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_32])).

tff(c_40,plain,(
    ! [A_33,B_34] : r1_tarski(A_33,k2_xboole_0(A_33,B_34)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_162,plain,(
    ! [A_74,B_75] :
      ( k3_xboole_0(A_74,B_75) = A_74
      | ~ r1_tarski(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_169,plain,(
    ! [A_33,B_34] : k3_xboole_0(A_33,k2_xboole_0(A_33,B_34)) = A_33 ),
    inference(resolution,[status(thm)],[c_40,c_162])).

tff(c_456,plain,(
    ! [A_107] : k3_xboole_0(k1_xboole_0,A_107) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_444,c_169])).

tff(c_610,plain,(
    ! [A_128,B_129,C_130] :
      ( ~ r1_xboole_0(A_128,B_129)
      | ~ r2_hidden(C_130,k3_xboole_0(A_128,B_129)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_617,plain,(
    ! [A_107,C_130] :
      ( ~ r1_xboole_0(k1_xboole_0,A_107)
      | ~ r2_hidden(C_130,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_456,c_610])).

tff(c_835,plain,(
    ! [C_145] : ~ r2_hidden(C_145,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_617])).

tff(c_890,plain,(
    ! [B_149] : r1_xboole_0(k1_xboole_0,B_149) ),
    inference(resolution,[status(thm)],[c_18,c_835])).

tff(c_42,plain,(
    ! [A_35,B_36] :
      ( k4_xboole_0(A_35,B_36) = A_35
      | ~ r1_xboole_0(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_898,plain,(
    ! [B_149] : k4_xboole_0(k1_xboole_0,B_149) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_890,c_42])).

tff(c_413,plain,(
    ! [A_106] : k2_xboole_0(k1_xboole_0,A_106) = A_106 ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_32])).

tff(c_749,plain,(
    ! [A_139,B_140] : k4_xboole_0(k2_xboole_0(A_139,B_140),B_140) = k4_xboole_0(A_139,B_140) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_758,plain,(
    ! [A_106] : k4_xboole_0(k1_xboole_0,A_106) = k4_xboole_0(A_106,A_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_749])).

tff(c_983,plain,(
    ! [A_106] : k4_xboole_0(A_106,A_106) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_898,c_758])).

tff(c_28,plain,(
    ! [B_23] : r1_tarski(B_23,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_170,plain,(
    ! [B_23] : k3_xboole_0(B_23,B_23) = B_23 ),
    inference(resolution,[status(thm)],[c_28,c_162])).

tff(c_851,plain,(
    ! [A_146,B_147] : k5_xboole_0(A_146,k3_xboole_0(A_146,B_147)) = k4_xboole_0(A_146,B_147) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_872,plain,(
    ! [B_23] : k5_xboole_0(B_23,B_23) = k4_xboole_0(B_23,B_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_851])).

tff(c_1188,plain,(
    ! [B_23] : k5_xboole_0(B_23,B_23) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_983,c_872])).

tff(c_44,plain,(
    ! [A_35,B_36] :
      ( r1_xboole_0(A_35,B_36)
      | k4_xboole_0(A_35,B_36) != A_35 ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1538,plain,(
    ! [A_191,B_192] :
      ( ~ r1_xboole_0(A_191,B_192)
      | v1_xboole_0(k3_xboole_0(A_191,B_192)) ) ),
    inference(resolution,[status(thm)],[c_6,c_610])).

tff(c_1570,plain,(
    ! [B_193] :
      ( ~ r1_xboole_0(B_193,B_193)
      | v1_xboole_0(B_193) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_1538])).

tff(c_1590,plain,(
    ! [B_36] :
      ( v1_xboole_0(B_36)
      | k4_xboole_0(B_36,B_36) != B_36 ) ),
    inference(resolution,[status(thm)],[c_44,c_1570])).

tff(c_1610,plain,(
    ! [B_198] :
      ( v1_xboole_0(B_198)
      | k1_xboole_0 != B_198 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_983,c_1590])).

tff(c_1007,plain,(
    ! [A_154,B_155] :
      ( r2_hidden('#skF_2'(A_154,B_155),A_154)
      | r1_tarski(A_154,B_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1164,plain,(
    ! [A_162,B_163] :
      ( ~ v1_xboole_0(A_162)
      | r1_tarski(A_162,B_163) ) ),
    inference(resolution,[status(thm)],[c_1007,c_4])).

tff(c_34,plain,(
    ! [A_27,B_28] :
      ( k3_xboole_0(A_27,B_28) = A_27
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1180,plain,(
    ! [A_162,B_163] :
      ( k3_xboole_0(A_162,B_163) = A_162
      | ~ v1_xboole_0(A_162) ) ),
    inference(resolution,[status(thm)],[c_1164,c_34])).

tff(c_1782,plain,(
    ! [B_214,B_215] :
      ( k3_xboole_0(B_214,B_215) = B_214
      | k1_xboole_0 != B_214 ) ),
    inference(resolution,[status(thm)],[c_1610,c_1180])).

tff(c_30,plain,(
    ! [A_24,B_25] : k5_xboole_0(A_24,k3_xboole_0(A_24,B_25)) = k4_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1800,plain,(
    ! [B_214,B_215] :
      ( k5_xboole_0(B_214,B_214) = k4_xboole_0(B_214,B_215)
      | k1_xboole_0 != B_214 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1782,c_30])).

tff(c_1838,plain,(
    ! [B_216,B_217] :
      ( k4_xboole_0(B_216,B_217) = k1_xboole_0
      | k1_xboole_0 != B_216 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1188,c_1800])).

tff(c_36,plain,(
    ! [A_29,B_30] : k2_xboole_0(A_29,k4_xboole_0(B_30,A_29)) = k2_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1854,plain,(
    ! [B_217,B_216] :
      ( k2_xboole_0(B_217,k1_xboole_0) = k2_xboole_0(B_217,B_216)
      | k1_xboole_0 != B_216 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1838,c_36])).

tff(c_1879,plain,(
    ! [B_217] : k2_xboole_0(B_217,k1_xboole_0) = B_217 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1854])).

tff(c_219,plain,(
    ! [A_89,B_90] :
      ( r1_tarski(k1_tarski(A_89),B_90)
      | ~ r2_hidden(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_3963,plain,(
    ! [A_331,B_332] :
      ( k3_xboole_0(k1_tarski(A_331),B_332) = k1_tarski(A_331)
      | ~ r2_hidden(A_331,B_332) ) ),
    inference(resolution,[status(thm)],[c_219,c_34])).

tff(c_3999,plain,(
    ! [A_331,B_332] :
      ( k5_xboole_0(k1_tarski(A_331),k1_tarski(A_331)) = k4_xboole_0(k1_tarski(A_331),B_332)
      | ~ r2_hidden(A_331,B_332) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3963,c_30])).

tff(c_13293,plain,(
    ! [A_674,B_675] :
      ( k4_xboole_0(k1_tarski(A_674),B_675) = k1_xboole_0
      | ~ r2_hidden(A_674,B_675) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1188,c_3999])).

tff(c_13435,plain,(
    ! [B_675,A_674] :
      ( k2_xboole_0(B_675,k1_tarski(A_674)) = k2_xboole_0(B_675,k1_xboole_0)
      | ~ r2_hidden(A_674,B_675) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13293,c_36])).

tff(c_26753,plain,(
    ! [B_945,A_946] :
      ( k2_xboole_0(B_945,k1_tarski(A_946)) = B_945
      | ~ r2_hidden(A_946,B_945) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1879,c_13435])).

tff(c_340,plain,(
    ! [B_104,A_103] : k2_xboole_0(B_104,A_103) = k2_xboole_0(A_103,B_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_62])).

tff(c_64,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_360,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_64])).

tff(c_27322,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_26753,c_360])).

tff(c_27419,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_27322])).

tff(c_27445,plain,(
    ! [A_949] : ~ r1_xboole_0(k1_xboole_0,A_949) ),
    inference(splitRight,[status(thm)],[c_617])).

tff(c_27458,plain,(
    ! [B_110] : ~ v1_xboole_0(B_110) ),
    inference(resolution,[status(thm)],[c_502,c_27445])).

tff(c_27463,plain,(
    ! [A_951] : r2_hidden('#skF_1'(A_951),A_951) ),
    inference(negUnitSimplification,[status(thm)],[c_27458,c_6])).

tff(c_22,plain,(
    ! [A_17,B_18,C_21] :
      ( ~ r1_xboole_0(A_17,B_18)
      | ~ r2_hidden(C_21,k3_xboole_0(A_17,B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_27469,plain,(
    ! [A_17,B_18] : ~ r1_xboole_0(A_17,B_18) ),
    inference(resolution,[status(thm)],[c_27463,c_22])).

tff(c_27473,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,B_36) != A_35 ),
    inference(negUnitSimplification,[status(thm)],[c_27469,c_44])).

tff(c_27490,plain,(
    ! [A_958,B_959] : k2_xboole_0(A_958,k4_xboole_0(B_959,A_958)) = k2_xboole_0(A_958,B_959) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_27506,plain,(
    ! [B_959] : k4_xboole_0(B_959,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_959) ),
    inference(superposition,[status(thm),theory(equality)],[c_27490,c_413])).

tff(c_27538,plain,(
    ! [B_959] : k4_xboole_0(B_959,k1_xboole_0) = B_959 ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_27506])).

tff(c_27540,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27473,c_27538])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:11:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.86/4.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.93/4.58  
% 10.93/4.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.93/4.58  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 10.93/4.58  
% 10.93/4.58  %Foreground sorts:
% 10.93/4.58  
% 10.93/4.58  
% 10.93/4.58  %Background operators:
% 10.93/4.58  
% 10.93/4.58  
% 10.93/4.58  %Foreground operators:
% 10.93/4.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.93/4.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.93/4.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.93/4.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.93/4.58  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.93/4.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.93/4.58  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.93/4.58  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.93/4.58  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.93/4.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.93/4.58  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.93/4.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.93/4.58  tff('#skF_5', type, '#skF_5': $i).
% 10.93/4.58  tff('#skF_6', type, '#skF_6': $i).
% 10.93/4.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.93/4.58  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.93/4.58  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.93/4.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.93/4.58  tff(k3_tarski, type, k3_tarski: $i > $i).
% 10.93/4.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.93/4.58  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.93/4.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.93/4.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.93/4.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.93/4.58  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 10.93/4.58  
% 10.93/4.60  tff(f_61, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 10.93/4.60  tff(f_36, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 10.93/4.60  tff(f_122, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 10.93/4.60  tff(f_85, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 10.93/4.60  tff(f_101, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 10.93/4.60  tff(f_117, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 10.93/4.60  tff(f_95, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 10.93/4.60  tff(f_89, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 10.93/4.60  tff(f_75, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 10.93/4.60  tff(f_99, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 10.93/4.60  tff(f_93, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 10.93/4.60  tff(f_81, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.93/4.60  tff(f_83, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.93/4.60  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 10.93/4.60  tff(f_91, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 10.93/4.60  tff(f_115, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 10.93/4.60  tff(c_495, plain, (![A_109, B_110]: (r2_hidden('#skF_3'(A_109, B_110), B_110) | r1_xboole_0(A_109, B_110))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.93/4.60  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.93/4.60  tff(c_502, plain, (![B_110, A_109]: (~v1_xboole_0(B_110) | r1_xboole_0(A_109, B_110))), inference(resolution, [status(thm)], [c_495, c_4])).
% 10.93/4.60  tff(c_66, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_122])).
% 10.93/4.60  tff(c_32, plain, (![A_26]: (k2_xboole_0(A_26, k1_xboole_0)=A_26)), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.93/4.60  tff(c_18, plain, (![A_12, B_13]: (r2_hidden('#skF_3'(A_12, B_13), A_12) | r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.93/4.60  tff(c_46, plain, (![B_38, A_37]: (k2_tarski(B_38, A_37)=k2_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.93/4.60  tff(c_228, plain, (![A_91, B_92]: (k3_tarski(k2_tarski(A_91, B_92))=k2_xboole_0(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.93/4.60  tff(c_334, plain, (![A_103, B_104]: (k3_tarski(k2_tarski(A_103, B_104))=k2_xboole_0(B_104, A_103))), inference(superposition, [status(thm), theory('equality')], [c_46, c_228])).
% 10.93/4.60  tff(c_62, plain, (![A_56, B_57]: (k3_tarski(k2_tarski(A_56, B_57))=k2_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.93/4.60  tff(c_361, plain, (![B_105, A_106]: (k2_xboole_0(B_105, A_106)=k2_xboole_0(A_106, B_105))), inference(superposition, [status(thm), theory('equality')], [c_334, c_62])).
% 10.93/4.60  tff(c_444, plain, (![A_107]: (k2_xboole_0(k1_xboole_0, A_107)=A_107)), inference(superposition, [status(thm), theory('equality')], [c_361, c_32])).
% 10.93/4.60  tff(c_40, plain, (![A_33, B_34]: (r1_tarski(A_33, k2_xboole_0(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.93/4.60  tff(c_162, plain, (![A_74, B_75]: (k3_xboole_0(A_74, B_75)=A_74 | ~r1_tarski(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.93/4.60  tff(c_169, plain, (![A_33, B_34]: (k3_xboole_0(A_33, k2_xboole_0(A_33, B_34))=A_33)), inference(resolution, [status(thm)], [c_40, c_162])).
% 10.93/4.60  tff(c_456, plain, (![A_107]: (k3_xboole_0(k1_xboole_0, A_107)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_444, c_169])).
% 10.93/4.60  tff(c_610, plain, (![A_128, B_129, C_130]: (~r1_xboole_0(A_128, B_129) | ~r2_hidden(C_130, k3_xboole_0(A_128, B_129)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.93/4.60  tff(c_617, plain, (![A_107, C_130]: (~r1_xboole_0(k1_xboole_0, A_107) | ~r2_hidden(C_130, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_456, c_610])).
% 10.93/4.60  tff(c_835, plain, (![C_145]: (~r2_hidden(C_145, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_617])).
% 10.93/4.60  tff(c_890, plain, (![B_149]: (r1_xboole_0(k1_xboole_0, B_149))), inference(resolution, [status(thm)], [c_18, c_835])).
% 10.93/4.60  tff(c_42, plain, (![A_35, B_36]: (k4_xboole_0(A_35, B_36)=A_35 | ~r1_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.93/4.60  tff(c_898, plain, (![B_149]: (k4_xboole_0(k1_xboole_0, B_149)=k1_xboole_0)), inference(resolution, [status(thm)], [c_890, c_42])).
% 10.93/4.60  tff(c_413, plain, (![A_106]: (k2_xboole_0(k1_xboole_0, A_106)=A_106)), inference(superposition, [status(thm), theory('equality')], [c_361, c_32])).
% 10.93/4.60  tff(c_749, plain, (![A_139, B_140]: (k4_xboole_0(k2_xboole_0(A_139, B_140), B_140)=k4_xboole_0(A_139, B_140))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.93/4.60  tff(c_758, plain, (![A_106]: (k4_xboole_0(k1_xboole_0, A_106)=k4_xboole_0(A_106, A_106))), inference(superposition, [status(thm), theory('equality')], [c_413, c_749])).
% 10.93/4.60  tff(c_983, plain, (![A_106]: (k4_xboole_0(A_106, A_106)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_898, c_758])).
% 10.93/4.60  tff(c_28, plain, (![B_23]: (r1_tarski(B_23, B_23))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.93/4.60  tff(c_170, plain, (![B_23]: (k3_xboole_0(B_23, B_23)=B_23)), inference(resolution, [status(thm)], [c_28, c_162])).
% 10.93/4.60  tff(c_851, plain, (![A_146, B_147]: (k5_xboole_0(A_146, k3_xboole_0(A_146, B_147))=k4_xboole_0(A_146, B_147))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.93/4.60  tff(c_872, plain, (![B_23]: (k5_xboole_0(B_23, B_23)=k4_xboole_0(B_23, B_23))), inference(superposition, [status(thm), theory('equality')], [c_170, c_851])).
% 10.93/4.60  tff(c_1188, plain, (![B_23]: (k5_xboole_0(B_23, B_23)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_983, c_872])).
% 10.93/4.60  tff(c_44, plain, (![A_35, B_36]: (r1_xboole_0(A_35, B_36) | k4_xboole_0(A_35, B_36)!=A_35)), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.93/4.60  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.93/4.60  tff(c_1538, plain, (![A_191, B_192]: (~r1_xboole_0(A_191, B_192) | v1_xboole_0(k3_xboole_0(A_191, B_192)))), inference(resolution, [status(thm)], [c_6, c_610])).
% 10.93/4.60  tff(c_1570, plain, (![B_193]: (~r1_xboole_0(B_193, B_193) | v1_xboole_0(B_193))), inference(superposition, [status(thm), theory('equality')], [c_170, c_1538])).
% 10.93/4.60  tff(c_1590, plain, (![B_36]: (v1_xboole_0(B_36) | k4_xboole_0(B_36, B_36)!=B_36)), inference(resolution, [status(thm)], [c_44, c_1570])).
% 10.93/4.60  tff(c_1610, plain, (![B_198]: (v1_xboole_0(B_198) | k1_xboole_0!=B_198)), inference(demodulation, [status(thm), theory('equality')], [c_983, c_1590])).
% 10.93/4.60  tff(c_1007, plain, (![A_154, B_155]: (r2_hidden('#skF_2'(A_154, B_155), A_154) | r1_tarski(A_154, B_155))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.93/4.60  tff(c_1164, plain, (![A_162, B_163]: (~v1_xboole_0(A_162) | r1_tarski(A_162, B_163))), inference(resolution, [status(thm)], [c_1007, c_4])).
% 10.93/4.60  tff(c_34, plain, (![A_27, B_28]: (k3_xboole_0(A_27, B_28)=A_27 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.93/4.60  tff(c_1180, plain, (![A_162, B_163]: (k3_xboole_0(A_162, B_163)=A_162 | ~v1_xboole_0(A_162))), inference(resolution, [status(thm)], [c_1164, c_34])).
% 10.93/4.60  tff(c_1782, plain, (![B_214, B_215]: (k3_xboole_0(B_214, B_215)=B_214 | k1_xboole_0!=B_214)), inference(resolution, [status(thm)], [c_1610, c_1180])).
% 10.93/4.60  tff(c_30, plain, (![A_24, B_25]: (k5_xboole_0(A_24, k3_xboole_0(A_24, B_25))=k4_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.93/4.60  tff(c_1800, plain, (![B_214, B_215]: (k5_xboole_0(B_214, B_214)=k4_xboole_0(B_214, B_215) | k1_xboole_0!=B_214)), inference(superposition, [status(thm), theory('equality')], [c_1782, c_30])).
% 10.93/4.60  tff(c_1838, plain, (![B_216, B_217]: (k4_xboole_0(B_216, B_217)=k1_xboole_0 | k1_xboole_0!=B_216)), inference(demodulation, [status(thm), theory('equality')], [c_1188, c_1800])).
% 10.93/4.60  tff(c_36, plain, (![A_29, B_30]: (k2_xboole_0(A_29, k4_xboole_0(B_30, A_29))=k2_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.93/4.60  tff(c_1854, plain, (![B_217, B_216]: (k2_xboole_0(B_217, k1_xboole_0)=k2_xboole_0(B_217, B_216) | k1_xboole_0!=B_216)), inference(superposition, [status(thm), theory('equality')], [c_1838, c_36])).
% 10.93/4.60  tff(c_1879, plain, (![B_217]: (k2_xboole_0(B_217, k1_xboole_0)=B_217)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1854])).
% 10.93/4.60  tff(c_219, plain, (![A_89, B_90]: (r1_tarski(k1_tarski(A_89), B_90) | ~r2_hidden(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.93/4.60  tff(c_3963, plain, (![A_331, B_332]: (k3_xboole_0(k1_tarski(A_331), B_332)=k1_tarski(A_331) | ~r2_hidden(A_331, B_332))), inference(resolution, [status(thm)], [c_219, c_34])).
% 10.93/4.60  tff(c_3999, plain, (![A_331, B_332]: (k5_xboole_0(k1_tarski(A_331), k1_tarski(A_331))=k4_xboole_0(k1_tarski(A_331), B_332) | ~r2_hidden(A_331, B_332))), inference(superposition, [status(thm), theory('equality')], [c_3963, c_30])).
% 10.93/4.60  tff(c_13293, plain, (![A_674, B_675]: (k4_xboole_0(k1_tarski(A_674), B_675)=k1_xboole_0 | ~r2_hidden(A_674, B_675))), inference(demodulation, [status(thm), theory('equality')], [c_1188, c_3999])).
% 10.93/4.60  tff(c_13435, plain, (![B_675, A_674]: (k2_xboole_0(B_675, k1_tarski(A_674))=k2_xboole_0(B_675, k1_xboole_0) | ~r2_hidden(A_674, B_675))), inference(superposition, [status(thm), theory('equality')], [c_13293, c_36])).
% 10.93/4.60  tff(c_26753, plain, (![B_945, A_946]: (k2_xboole_0(B_945, k1_tarski(A_946))=B_945 | ~r2_hidden(A_946, B_945))), inference(demodulation, [status(thm), theory('equality')], [c_1879, c_13435])).
% 10.93/4.60  tff(c_340, plain, (![B_104, A_103]: (k2_xboole_0(B_104, A_103)=k2_xboole_0(A_103, B_104))), inference(superposition, [status(thm), theory('equality')], [c_334, c_62])).
% 10.93/4.60  tff(c_64, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_122])).
% 10.93/4.60  tff(c_360, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_340, c_64])).
% 10.93/4.60  tff(c_27322, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_26753, c_360])).
% 10.93/4.60  tff(c_27419, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_27322])).
% 10.93/4.60  tff(c_27445, plain, (![A_949]: (~r1_xboole_0(k1_xboole_0, A_949))), inference(splitRight, [status(thm)], [c_617])).
% 10.93/4.60  tff(c_27458, plain, (![B_110]: (~v1_xboole_0(B_110))), inference(resolution, [status(thm)], [c_502, c_27445])).
% 10.93/4.60  tff(c_27463, plain, (![A_951]: (r2_hidden('#skF_1'(A_951), A_951))), inference(negUnitSimplification, [status(thm)], [c_27458, c_6])).
% 10.93/4.60  tff(c_22, plain, (![A_17, B_18, C_21]: (~r1_xboole_0(A_17, B_18) | ~r2_hidden(C_21, k3_xboole_0(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.93/4.60  tff(c_27469, plain, (![A_17, B_18]: (~r1_xboole_0(A_17, B_18))), inference(resolution, [status(thm)], [c_27463, c_22])).
% 10.93/4.60  tff(c_27473, plain, (![A_35, B_36]: (k4_xboole_0(A_35, B_36)!=A_35)), inference(negUnitSimplification, [status(thm)], [c_27469, c_44])).
% 10.93/4.60  tff(c_27490, plain, (![A_958, B_959]: (k2_xboole_0(A_958, k4_xboole_0(B_959, A_958))=k2_xboole_0(A_958, B_959))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.93/4.60  tff(c_27506, plain, (![B_959]: (k4_xboole_0(B_959, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_959))), inference(superposition, [status(thm), theory('equality')], [c_27490, c_413])).
% 10.93/4.60  tff(c_27538, plain, (![B_959]: (k4_xboole_0(B_959, k1_xboole_0)=B_959)), inference(demodulation, [status(thm), theory('equality')], [c_413, c_27506])).
% 10.93/4.60  tff(c_27540, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27473, c_27538])).
% 10.93/4.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.93/4.60  
% 10.93/4.60  Inference rules
% 10.93/4.60  ----------------------
% 10.93/4.60  #Ref     : 3
% 10.93/4.60  #Sup     : 7153
% 10.93/4.60  #Fact    : 0
% 10.93/4.60  #Define  : 0
% 10.93/4.60  #Split   : 3
% 10.93/4.60  #Chain   : 0
% 10.93/4.60  #Close   : 0
% 10.93/4.60  
% 10.93/4.60  Ordering : KBO
% 10.93/4.60  
% 10.93/4.60  Simplification rules
% 10.93/4.60  ----------------------
% 10.93/4.60  #Subsume      : 3967
% 10.93/4.60  #Demod        : 3053
% 10.93/4.60  #Tautology    : 1535
% 10.93/4.60  #SimpNegUnit  : 76
% 10.93/4.60  #BackRed      : 17
% 10.93/4.60  
% 10.93/4.60  #Partial instantiations: 0
% 10.93/4.60  #Strategies tried      : 1
% 10.93/4.60  
% 10.93/4.60  Timing (in seconds)
% 10.93/4.60  ----------------------
% 10.93/4.60  Preprocessing        : 0.35
% 10.93/4.60  Parsing              : 0.18
% 10.93/4.60  CNF conversion       : 0.03
% 10.93/4.60  Main loop            : 3.48
% 10.93/4.60  Inferencing          : 0.74
% 10.93/4.60  Reduction            : 1.52
% 10.93/4.60  Demodulation         : 1.14
% 10.93/4.60  BG Simplification    : 0.06
% 10.93/4.60  Subsumption          : 0.96
% 10.93/4.60  Abstraction          : 0.11
% 10.93/4.60  MUC search           : 0.00
% 10.93/4.60  Cooper               : 0.00
% 10.93/4.60  Total                : 3.87
% 10.93/4.60  Index Insertion      : 0.00
% 10.93/4.60  Index Deletion       : 0.00
% 10.93/4.60  Index Matching       : 0.00
% 10.93/4.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
