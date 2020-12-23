%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:24 EST 2020

% Result     : Theorem 8.17s
% Output     : CNFRefutation 8.17s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 108 expanded)
%              Number of leaves         :   42 (  53 expanded)
%              Depth                    :   15
%              Number of atoms          :   90 ( 117 expanded)
%              Number of equality atoms :   66 (  86 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_92,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_53,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_82,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_78,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_76,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_80,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_74,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_72,plain,(
    '#skF_6' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_339,plain,(
    ! [A_96,B_97] : k3_xboole_0(k1_tarski(A_96),k2_tarski(A_96,B_97)) = k1_tarski(A_96) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_134,plain,(
    ! [B_79,A_80] : k3_xboole_0(B_79,A_80) = k3_xboole_0(A_80,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_11,B_12] : r1_tarski(k3_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_152,plain,(
    ! [A_80,B_79] : r1_tarski(k3_xboole_0(A_80,B_79),B_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_16])).

tff(c_345,plain,(
    ! [A_96,B_97] : r1_tarski(k1_tarski(A_96),k2_tarski(A_96,B_97)) ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_152])).

tff(c_76,plain,(
    r1_tarski(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1288,plain,(
    ! [A_139,C_140,B_141] :
      ( r1_tarski(A_139,C_140)
      | ~ r1_tarski(B_141,C_140)
      | ~ r1_tarski(A_139,B_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1464,plain,(
    ! [A_150] :
      ( r1_tarski(A_150,k2_tarski('#skF_5','#skF_6'))
      | ~ r1_tarski(A_150,k2_tarski('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_76,c_1288])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2689,plain,(
    ! [A_187] :
      ( k3_xboole_0(A_187,k2_tarski('#skF_5','#skF_6')) = A_187
      | ~ r1_tarski(A_187,k2_tarski('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1464,c_20])).

tff(c_2730,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_5','#skF_6')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_345,c_2689])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_26,plain,(
    ! [A_21] : k5_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22,plain,(
    ! [A_18] : k3_xboole_0(A_18,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_387,plain,(
    ! [A_102,B_103] : k5_xboole_0(A_102,k3_xboole_0(A_102,B_103)) = k4_xboole_0(A_102,B_103) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_411,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = k4_xboole_0(A_18,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_387])).

tff(c_418,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_411])).

tff(c_641,plain,(
    ! [A_115,B_116] : k4_xboole_0(A_115,k4_xboole_0(A_115,B_116)) = k3_xboole_0(A_115,B_116) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_670,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k3_xboole_0(A_18,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_641])).

tff(c_677,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_670])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_414,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_387])).

tff(c_678,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_677,c_414])).

tff(c_293,plain,(
    ! [A_89,B_90] :
      ( k3_xboole_0(A_89,B_90) = A_89
      | ~ r1_tarski(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_781,plain,(
    ! [A_120,B_121] : k3_xboole_0(k3_xboole_0(A_120,B_121),A_120) = k3_xboole_0(A_120,B_121) ),
    inference(resolution,[status(thm)],[c_16,c_293])).

tff(c_14,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_790,plain,(
    ! [A_120,B_121] : k5_xboole_0(k3_xboole_0(A_120,B_121),k3_xboole_0(A_120,B_121)) = k4_xboole_0(k3_xboole_0(A_120,B_121),A_120) ),
    inference(superposition,[status(thm),theory(equality)],[c_781,c_14])).

tff(c_860,plain,(
    ! [A_122,B_123] : k4_xboole_0(k3_xboole_0(A_122,B_123),A_122) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_678,c_790])).

tff(c_28,plain,(
    ! [A_22,B_23] : k5_xboole_0(A_22,k4_xboole_0(B_23,A_22)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_868,plain,(
    ! [A_122,B_123] : k2_xboole_0(A_122,k3_xboole_0(A_122,B_123)) = k5_xboole_0(A_122,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_860,c_28])).

tff(c_915,plain,(
    ! [A_124,B_125] : k2_xboole_0(A_124,k3_xboole_0(A_124,B_125)) = A_124 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_868])).

tff(c_944,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k3_xboole_0(B_4,A_3)) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_915])).

tff(c_3621,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_6'),k1_tarski('#skF_3')) = k2_tarski('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2730,c_944])).

tff(c_60,plain,(
    ! [A_38,B_39,C_40] : k2_enumset1(A_38,A_38,B_39,C_40) = k1_enumset1(A_38,B_39,C_40) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_56,plain,(
    ! [A_35] : k2_tarski(A_35,A_35) = k1_tarski(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2394,plain,(
    ! [A_179,B_180,C_181,D_182] : k2_xboole_0(k2_tarski(A_179,B_180),k2_tarski(C_181,D_182)) = k2_enumset1(A_179,B_180,C_181,D_182) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_10165,plain,(
    ! [C_378,D_379,A_380,B_381] : k2_xboole_0(k2_tarski(C_378,D_379),k2_tarski(A_380,B_381)) = k2_enumset1(A_380,B_381,C_378,D_379) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2394])).

tff(c_10209,plain,(
    ! [C_378,D_379,A_35] : k2_xboole_0(k2_tarski(C_378,D_379),k1_tarski(A_35)) = k2_enumset1(A_35,A_35,C_378,D_379) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_10165])).

tff(c_10219,plain,(
    ! [C_378,D_379,A_35] : k2_xboole_0(k2_tarski(C_378,D_379),k1_tarski(A_35)) = k1_enumset1(A_35,C_378,D_379) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_10209])).

tff(c_14762,plain,(
    k1_enumset1('#skF_3','#skF_5','#skF_6') = k2_tarski('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3621,c_10219])).

tff(c_36,plain,(
    ! [E_30,B_25,C_26] : r2_hidden(E_30,k1_enumset1(E_30,B_25,C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_14798,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14762,c_36])).

tff(c_58,plain,(
    ! [A_36,B_37] : k1_enumset1(A_36,A_36,B_37) = k2_tarski(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1874,plain,(
    ! [E_168,C_169,B_170,A_171] :
      ( E_168 = C_169
      | E_168 = B_170
      | E_168 = A_171
      | ~ r2_hidden(E_168,k1_enumset1(A_171,B_170,C_169)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1877,plain,(
    ! [E_168,B_37,A_36] :
      ( E_168 = B_37
      | E_168 = A_36
      | E_168 = A_36
      | ~ r2_hidden(E_168,k2_tarski(A_36,B_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_1874])).

tff(c_14815,plain,
    ( '#skF_6' = '#skF_3'
    | '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_14798,c_1877])).

tff(c_14819,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_74,c_72,c_14815])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:40:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.17/3.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.17/3.14  
% 8.17/3.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.17/3.15  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 8.17/3.15  
% 8.17/3.15  %Foreground sorts:
% 8.17/3.15  
% 8.17/3.15  
% 8.17/3.15  %Background operators:
% 8.17/3.15  
% 8.17/3.15  
% 8.17/3.15  %Foreground operators:
% 8.17/3.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.17/3.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.17/3.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.17/3.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.17/3.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.17/3.15  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.17/3.15  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.17/3.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.17/3.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.17/3.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.17/3.15  tff('#skF_5', type, '#skF_5': $i).
% 8.17/3.15  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 8.17/3.15  tff('#skF_6', type, '#skF_6': $i).
% 8.17/3.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.17/3.15  tff('#skF_3', type, '#skF_3': $i).
% 8.17/3.15  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.17/3.15  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.17/3.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.17/3.15  tff('#skF_4', type, '#skF_4': $i).
% 8.17/3.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.17/3.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.17/3.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.17/3.15  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.17/3.15  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 8.17/3.15  
% 8.17/3.16  tff(f_102, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 8.17/3.16  tff(f_92, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 8.17/3.16  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.17/3.16  tff(f_41, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 8.17/3.16  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 8.17/3.16  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.17/3.16  tff(f_57, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 8.17/3.16  tff(f_53, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 8.17/3.16  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.17/3.16  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.17/3.16  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 8.17/3.16  tff(f_59, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 8.17/3.16  tff(f_82, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 8.17/3.16  tff(f_78, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 8.17/3.16  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.17/3.16  tff(f_76, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 8.17/3.16  tff(f_74, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 8.17/3.16  tff(f_80, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 8.17/3.16  tff(c_74, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.17/3.16  tff(c_72, plain, ('#skF_6'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.17/3.16  tff(c_339, plain, (![A_96, B_97]: (k3_xboole_0(k1_tarski(A_96), k2_tarski(A_96, B_97))=k1_tarski(A_96))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.17/3.16  tff(c_134, plain, (![B_79, A_80]: (k3_xboole_0(B_79, A_80)=k3_xboole_0(A_80, B_79))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.17/3.16  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(k3_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.17/3.16  tff(c_152, plain, (![A_80, B_79]: (r1_tarski(k3_xboole_0(A_80, B_79), B_79))), inference(superposition, [status(thm), theory('equality')], [c_134, c_16])).
% 8.17/3.16  tff(c_345, plain, (![A_96, B_97]: (r1_tarski(k1_tarski(A_96), k2_tarski(A_96, B_97)))), inference(superposition, [status(thm), theory('equality')], [c_339, c_152])).
% 8.17/3.16  tff(c_76, plain, (r1_tarski(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.17/3.16  tff(c_1288, plain, (![A_139, C_140, B_141]: (r1_tarski(A_139, C_140) | ~r1_tarski(B_141, C_140) | ~r1_tarski(A_139, B_141))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.17/3.16  tff(c_1464, plain, (![A_150]: (r1_tarski(A_150, k2_tarski('#skF_5', '#skF_6')) | ~r1_tarski(A_150, k2_tarski('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_76, c_1288])).
% 8.17/3.16  tff(c_20, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.17/3.16  tff(c_2689, plain, (![A_187]: (k3_xboole_0(A_187, k2_tarski('#skF_5', '#skF_6'))=A_187 | ~r1_tarski(A_187, k2_tarski('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_1464, c_20])).
% 8.17/3.16  tff(c_2730, plain, (k3_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_5', '#skF_6'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_345, c_2689])).
% 8.17/3.16  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.17/3.16  tff(c_26, plain, (![A_21]: (k5_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.17/3.16  tff(c_22, plain, (![A_18]: (k3_xboole_0(A_18, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.17/3.16  tff(c_387, plain, (![A_102, B_103]: (k5_xboole_0(A_102, k3_xboole_0(A_102, B_103))=k4_xboole_0(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.17/3.16  tff(c_411, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=k4_xboole_0(A_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_387])).
% 8.17/3.16  tff(c_418, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_411])).
% 8.17/3.16  tff(c_641, plain, (![A_115, B_116]: (k4_xboole_0(A_115, k4_xboole_0(A_115, B_116))=k3_xboole_0(A_115, B_116))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.17/3.16  tff(c_670, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k3_xboole_0(A_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_418, c_641])).
% 8.17/3.16  tff(c_677, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_670])).
% 8.17/3.16  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.17/3.16  tff(c_414, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_387])).
% 8.17/3.16  tff(c_678, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_677, c_414])).
% 8.17/3.16  tff(c_293, plain, (![A_89, B_90]: (k3_xboole_0(A_89, B_90)=A_89 | ~r1_tarski(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.17/3.16  tff(c_781, plain, (![A_120, B_121]: (k3_xboole_0(k3_xboole_0(A_120, B_121), A_120)=k3_xboole_0(A_120, B_121))), inference(resolution, [status(thm)], [c_16, c_293])).
% 8.17/3.16  tff(c_14, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.17/3.16  tff(c_790, plain, (![A_120, B_121]: (k5_xboole_0(k3_xboole_0(A_120, B_121), k3_xboole_0(A_120, B_121))=k4_xboole_0(k3_xboole_0(A_120, B_121), A_120))), inference(superposition, [status(thm), theory('equality')], [c_781, c_14])).
% 8.17/3.16  tff(c_860, plain, (![A_122, B_123]: (k4_xboole_0(k3_xboole_0(A_122, B_123), A_122)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_678, c_790])).
% 8.17/3.16  tff(c_28, plain, (![A_22, B_23]: (k5_xboole_0(A_22, k4_xboole_0(B_23, A_22))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.17/3.16  tff(c_868, plain, (![A_122, B_123]: (k2_xboole_0(A_122, k3_xboole_0(A_122, B_123))=k5_xboole_0(A_122, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_860, c_28])).
% 8.17/3.16  tff(c_915, plain, (![A_124, B_125]: (k2_xboole_0(A_124, k3_xboole_0(A_124, B_125))=A_124)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_868])).
% 8.17/3.16  tff(c_944, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k3_xboole_0(B_4, A_3))=A_3)), inference(superposition, [status(thm), theory('equality')], [c_4, c_915])).
% 8.17/3.16  tff(c_3621, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), k1_tarski('#skF_3'))=k2_tarski('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2730, c_944])).
% 8.17/3.16  tff(c_60, plain, (![A_38, B_39, C_40]: (k2_enumset1(A_38, A_38, B_39, C_40)=k1_enumset1(A_38, B_39, C_40))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.17/3.16  tff(c_56, plain, (![A_35]: (k2_tarski(A_35, A_35)=k1_tarski(A_35))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.17/3.16  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.17/3.16  tff(c_2394, plain, (![A_179, B_180, C_181, D_182]: (k2_xboole_0(k2_tarski(A_179, B_180), k2_tarski(C_181, D_182))=k2_enumset1(A_179, B_180, C_181, D_182))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.17/3.16  tff(c_10165, plain, (![C_378, D_379, A_380, B_381]: (k2_xboole_0(k2_tarski(C_378, D_379), k2_tarski(A_380, B_381))=k2_enumset1(A_380, B_381, C_378, D_379))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2394])).
% 8.17/3.16  tff(c_10209, plain, (![C_378, D_379, A_35]: (k2_xboole_0(k2_tarski(C_378, D_379), k1_tarski(A_35))=k2_enumset1(A_35, A_35, C_378, D_379))), inference(superposition, [status(thm), theory('equality')], [c_56, c_10165])).
% 8.17/3.16  tff(c_10219, plain, (![C_378, D_379, A_35]: (k2_xboole_0(k2_tarski(C_378, D_379), k1_tarski(A_35))=k1_enumset1(A_35, C_378, D_379))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_10209])).
% 8.17/3.16  tff(c_14762, plain, (k1_enumset1('#skF_3', '#skF_5', '#skF_6')=k2_tarski('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3621, c_10219])).
% 8.17/3.16  tff(c_36, plain, (![E_30, B_25, C_26]: (r2_hidden(E_30, k1_enumset1(E_30, B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.17/3.16  tff(c_14798, plain, (r2_hidden('#skF_3', k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_14762, c_36])).
% 8.17/3.16  tff(c_58, plain, (![A_36, B_37]: (k1_enumset1(A_36, A_36, B_37)=k2_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.17/3.16  tff(c_1874, plain, (![E_168, C_169, B_170, A_171]: (E_168=C_169 | E_168=B_170 | E_168=A_171 | ~r2_hidden(E_168, k1_enumset1(A_171, B_170, C_169)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.17/3.16  tff(c_1877, plain, (![E_168, B_37, A_36]: (E_168=B_37 | E_168=A_36 | E_168=A_36 | ~r2_hidden(E_168, k2_tarski(A_36, B_37)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_1874])).
% 8.17/3.16  tff(c_14815, plain, ('#skF_6'='#skF_3' | '#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_14798, c_1877])).
% 8.17/3.16  tff(c_14819, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_74, c_72, c_14815])).
% 8.17/3.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.17/3.16  
% 8.17/3.16  Inference rules
% 8.17/3.16  ----------------------
% 8.17/3.16  #Ref     : 0
% 8.17/3.16  #Sup     : 3512
% 8.17/3.16  #Fact    : 6
% 8.17/3.16  #Define  : 0
% 8.17/3.16  #Split   : 1
% 8.17/3.16  #Chain   : 0
% 8.17/3.16  #Close   : 0
% 8.17/3.16  
% 8.17/3.16  Ordering : KBO
% 8.17/3.16  
% 8.17/3.16  Simplification rules
% 8.17/3.16  ----------------------
% 8.17/3.16  #Subsume      : 162
% 8.17/3.16  #Demod        : 3691
% 8.17/3.16  #Tautology    : 2527
% 8.17/3.16  #SimpNegUnit  : 1
% 8.17/3.16  #BackRed      : 2
% 8.17/3.16  
% 8.17/3.16  #Partial instantiations: 0
% 8.17/3.16  #Strategies tried      : 1
% 8.17/3.16  
% 8.17/3.16  Timing (in seconds)
% 8.17/3.16  ----------------------
% 8.17/3.16  Preprocessing        : 0.48
% 8.17/3.16  Parsing              : 0.25
% 8.17/3.16  CNF conversion       : 0.03
% 8.17/3.16  Main loop            : 1.90
% 8.17/3.16  Inferencing          : 0.47
% 8.17/3.16  Reduction            : 0.96
% 8.17/3.16  Demodulation         : 0.82
% 8.17/3.16  BG Simplification    : 0.06
% 8.17/3.16  Subsumption          : 0.32
% 8.17/3.16  Abstraction          : 0.09
% 8.17/3.16  MUC search           : 0.00
% 8.17/3.16  Cooper               : 0.00
% 8.17/3.17  Total                : 2.41
% 8.17/3.17  Index Insertion      : 0.00
% 8.17/3.17  Index Deletion       : 0.00
% 8.17/3.17  Index Matching       : 0.00
% 8.17/3.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
