%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:07 EST 2020

% Result     : Theorem 54.07s
% Output     : CNFRefutation 54.07s
% Verified   : 
% Statistics : Number of formulae       :  149 (1021 expanded)
%              Number of leaves         :   35 ( 356 expanded)
%              Depth                    :   28
%              Number of atoms          :  162 (1054 expanded)
%              Number of equality atoms :  141 (1017 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_106,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k3_xboole_0(k2_tarski(A,C),B) = k2_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & r2_hidden(C,B) )
     => k2_xboole_0(k2_tarski(A,C),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_70,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_60,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_34,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_86,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).

tff(c_66,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_64,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1982,plain,(
    ! [A_135,C_136,B_137] :
      ( k2_xboole_0(k2_tarski(A_135,C_136),B_137) = B_137
      | ~ r2_hidden(C_136,B_137)
      | ~ r2_hidden(A_135,B_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_xboole_0(B_4,A_3) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2035,plain,(
    ! [B_137,A_135,C_136] :
      ( k2_xboole_0(B_137,k2_tarski(A_135,C_136)) = B_137
      | ~ r2_hidden(C_136,B_137)
      | ~ r2_hidden(A_135,B_137) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1982,c_4])).

tff(c_136,plain,(
    ! [B_59,A_60] : k5_xboole_0(B_59,A_60) = k5_xboole_0(A_60,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_40,plain,(
    ! [A_36] : k5_xboole_0(A_36,k1_xboole_0) = A_36 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_152,plain,(
    ! [A_60] : k5_xboole_0(k1_xboole_0,A_60) = A_60 ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_40])).

tff(c_30,plain,(
    ! [A_26] : k4_xboole_0(A_26,k1_xboole_0) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6,plain,(
    ! [B_6,A_5] : k3_xboole_0(B_6,A_5) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_306,plain,(
    ! [A_68,B_69] : k2_xboole_0(A_68,k3_xboole_0(A_68,B_69)) = A_68 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_315,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k3_xboole_0(B_6,A_5)) = A_5 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_306])).

tff(c_579,plain,(
    ! [A_95,B_96] : k5_xboole_0(A_95,k3_xboole_0(A_95,B_96)) = k4_xboole_0(A_95,B_96) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_586,plain,(
    ! [B_96] : k4_xboole_0(k1_xboole_0,B_96) = k3_xboole_0(k1_xboole_0,B_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_579,c_152])).

tff(c_663,plain,(
    ! [A_98,B_99] : k2_xboole_0(A_98,k4_xboole_0(B_99,A_98)) = k2_xboole_0(A_98,B_99) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_672,plain,(
    ! [B_96] : k2_xboole_0(B_96,k3_xboole_0(k1_xboole_0,B_96)) = k2_xboole_0(B_96,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_586,c_663])).

tff(c_759,plain,(
    ! [B_103] : k2_xboole_0(B_103,k1_xboole_0) = B_103 ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_672])).

tff(c_812,plain,(
    ! [B_104] : k2_xboole_0(k1_xboole_0,B_104) = B_104 ),
    inference(superposition,[status(thm),theory(equality)],[c_759,c_4])).

tff(c_22,plain,(
    ! [A_17,B_18] : k2_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_835,plain,(
    ! [B_18] : k3_xboole_0(k1_xboole_0,B_18) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_812,c_22])).

tff(c_962,plain,(
    ! [B_96] : k4_xboole_0(k1_xboole_0,B_96) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_835,c_586])).

tff(c_860,plain,(
    ! [B_6] : k3_xboole_0(B_6,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_812])).

tff(c_433,plain,(
    ! [A_89,B_90] : k4_xboole_0(A_89,k4_xboole_0(A_89,B_90)) = k3_xboole_0(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_451,plain,(
    ! [A_26] : k4_xboole_0(A_26,A_26) = k3_xboole_0(A_26,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_433])).

tff(c_913,plain,(
    ! [A_26] : k4_xboole_0(A_26,A_26) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_860,c_451])).

tff(c_1175,plain,(
    ! [A_114,B_115,C_116] : k4_xboole_0(k4_xboole_0(A_114,B_115),C_116) = k4_xboole_0(A_114,k2_xboole_0(B_115,C_116)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1215,plain,(
    ! [A_26,C_116] : k4_xboole_0(A_26,k2_xboole_0(A_26,C_116)) = k4_xboole_0(k1_xboole_0,C_116) ),
    inference(superposition,[status(thm),theory(equality)],[c_913,c_1175])).

tff(c_1559,plain,(
    ! [A_124,C_125] : k4_xboole_0(A_124,k2_xboole_0(A_124,C_125)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_962,c_1215])).

tff(c_36,plain,(
    ! [A_32,B_33] : k4_xboole_0(A_32,k4_xboole_0(A_32,B_33)) = k3_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1588,plain,(
    ! [A_124,C_125] : k3_xboole_0(A_124,k2_xboole_0(A_124,C_125)) = k4_xboole_0(A_124,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1559,c_36])).

tff(c_1640,plain,(
    ! [A_124,C_125] : k3_xboole_0(A_124,k2_xboole_0(A_124,C_125)) = A_124 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1588])).

tff(c_28,plain,(
    ! [A_24,B_25] : k2_xboole_0(A_24,k4_xboole_0(B_25,A_24)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1185,plain,(
    ! [A_114,B_115] : k4_xboole_0(A_114,k2_xboole_0(B_115,k4_xboole_0(A_114,B_115))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1175,c_913])).

tff(c_1477,plain,(
    ! [A_122,B_123] : k4_xboole_0(A_122,k2_xboole_0(B_123,A_122)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1185])).

tff(c_1503,plain,(
    ! [A_122,B_123] : k3_xboole_0(A_122,k2_xboole_0(B_123,A_122)) = k4_xboole_0(A_122,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1477,c_36])).

tff(c_1551,plain,(
    ! [A_122,B_123] : k3_xboole_0(A_122,k2_xboole_0(B_123,A_122)) = A_122 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1503])).

tff(c_678,plain,(
    ! [A_26] : k2_xboole_0(A_26,k3_xboole_0(A_26,k1_xboole_0)) = k2_xboole_0(A_26,A_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_451,c_663])).

tff(c_689,plain,(
    ! [A_26] : k2_xboole_0(A_26,A_26) = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_678])).

tff(c_46,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(A_40,B_41)
      | k4_xboole_0(A_40,B_41) != A_40 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_42,plain,(
    ! [A_37,B_38,C_39] :
      ( k3_xboole_0(A_37,k2_xboole_0(B_38,C_39)) = k3_xboole_0(A_37,C_39)
      | ~ r1_xboole_0(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1885,plain,(
    ! [A_133,C_134] : k3_xboole_0(A_133,k2_xboole_0(A_133,C_134)) = A_133 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1588])).

tff(c_2622,plain,(
    ! [B_152,C_153] :
      ( k3_xboole_0(B_152,C_153) = B_152
      | ~ r1_xboole_0(B_152,B_152) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_1885])).

tff(c_2625,plain,(
    ! [B_41,C_153] :
      ( k3_xboole_0(B_41,C_153) = B_41
      | k4_xboole_0(B_41,B_41) != B_41 ) ),
    inference(resolution,[status(thm)],[c_46,c_2622])).

tff(c_2635,plain,(
    ! [B_154,C_155] :
      ( k3_xboole_0(B_154,C_155) = B_154
      | k1_xboole_0 != B_154 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_913,c_2625])).

tff(c_2973,plain,(
    ! [C_155] : k2_xboole_0(C_155,k1_xboole_0) = C_155 ),
    inference(superposition,[status(thm),theory(equality)],[c_2635,c_315])).

tff(c_777,plain,(
    ! [B_103] : k2_xboole_0(k1_xboole_0,B_103) = B_103 ),
    inference(superposition,[status(thm),theory(equality)],[c_759,c_4])).

tff(c_1585,plain,(
    ! [A_124,C_125] : k2_xboole_0(k2_xboole_0(A_124,C_125),k1_xboole_0) = k2_xboole_0(k2_xboole_0(A_124,C_125),A_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_1559,c_28])).

tff(c_5914,plain,(
    ! [A_220,C_221] : k2_xboole_0(k2_xboole_0(A_220,C_221),A_220) = k2_xboole_0(A_220,C_221) ),
    inference(demodulation,[status(thm),theory(equality)],[c_777,c_4,c_1585])).

tff(c_11817,plain,(
    ! [B_283,A_284] : k2_xboole_0(k2_xboole_0(B_283,A_284),A_284) = k2_xboole_0(A_284,B_283) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_5914])).

tff(c_1258,plain,(
    ! [A_26,C_116] : k4_xboole_0(A_26,k2_xboole_0(A_26,C_116)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_962,c_1215])).

tff(c_11944,plain,(
    ! [B_283,A_284] : k4_xboole_0(k2_xboole_0(B_283,A_284),k2_xboole_0(A_284,B_283)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_11817,c_1258])).

tff(c_47415,plain,(
    ! [C_547,A_548,B_549] : k2_xboole_0(C_547,k4_xboole_0(A_548,k2_xboole_0(B_549,C_547))) = k2_xboole_0(C_547,k4_xboole_0(A_548,B_549)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1175,c_28])).

tff(c_47815,plain,(
    ! [B_283,A_284] : k2_xboole_0(B_283,k4_xboole_0(k2_xboole_0(B_283,A_284),A_284)) = k2_xboole_0(B_283,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_11944,c_47415])).

tff(c_48131,plain,(
    ! [B_550,A_551] : k2_xboole_0(B_550,k4_xboole_0(k2_xboole_0(B_550,A_551),A_551)) = B_550 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2973,c_47815])).

tff(c_1500,plain,(
    ! [B_123,A_122] : k2_xboole_0(k2_xboole_0(B_123,A_122),k1_xboole_0) = k2_xboole_0(k2_xboole_0(B_123,A_122),A_122) ),
    inference(superposition,[status(thm),theory(equality)],[c_1477,c_28])).

tff(c_6951,plain,(
    ! [B_235,A_236] : k2_xboole_0(k2_xboole_0(B_235,A_236),A_236) = k2_xboole_0(B_235,A_236) ),
    inference(demodulation,[status(thm),theory(equality)],[c_777,c_4,c_1500])).

tff(c_7341,plain,(
    ! [A_239,B_240] : k2_xboole_0(A_239,k2_xboole_0(B_240,A_239)) = k2_xboole_0(B_240,A_239) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_6951])).

tff(c_7482,plain,(
    ! [B_4,A_3] : k2_xboole_0(B_4,k2_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_7341])).

tff(c_48228,plain,(
    ! [B_550,A_551] : k2_xboole_0(k4_xboole_0(k2_xboole_0(B_550,A_551),A_551),B_550) = k2_xboole_0(B_550,B_550) ),
    inference(superposition,[status(thm),theory(equality)],[c_48131,c_7482])).

tff(c_50199,plain,(
    ! [B_558,A_559] : k2_xboole_0(k4_xboole_0(k2_xboole_0(B_558,A_559),A_559),B_558) = B_558 ),
    inference(demodulation,[status(thm),theory(equality)],[c_689,c_48228])).

tff(c_1238,plain,(
    ! [A_32,B_33,C_116] : k4_xboole_0(A_32,k2_xboole_0(k4_xboole_0(A_32,B_33),C_116)) = k4_xboole_0(k3_xboole_0(A_32,B_33),C_116) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1175])).

tff(c_50227,plain,(
    ! [B_558,A_559] : k4_xboole_0(k3_xboole_0(k2_xboole_0(B_558,A_559),A_559),B_558) = k4_xboole_0(k2_xboole_0(B_558,A_559),B_558) ),
    inference(superposition,[status(thm),theory(equality)],[c_50199,c_1238])).

tff(c_155626,plain,(
    ! [B_982,A_983] : k4_xboole_0(k2_xboole_0(B_982,A_983),B_982) = k4_xboole_0(A_983,B_982) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1551,c_6,c_50227])).

tff(c_18,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_500,plain,(
    ! [A_92,B_93] : k4_xboole_0(A_92,k3_xboole_0(A_92,B_93)) = k4_xboole_0(A_92,B_93) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_506,plain,(
    ! [A_92,B_93] : k4_xboole_0(A_92,k4_xboole_0(A_92,B_93)) = k3_xboole_0(A_92,k3_xboole_0(A_92,B_93)) ),
    inference(superposition,[status(thm),theory(equality)],[c_500,c_36])).

tff(c_523,plain,(
    ! [A_92,B_93] : k3_xboole_0(A_92,k3_xboole_0(A_92,B_93)) = k3_xboole_0(A_92,B_93) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_506])).

tff(c_8,plain,(
    ! [B_8,A_7] : k5_xboole_0(B_8,A_7) = k5_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1319,plain,(
    ! [A_118,B_119] : k5_xboole_0(k5_xboole_0(A_118,B_119),k2_xboole_0(A_118,B_119)) = k3_xboole_0(A_118,B_119) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1352,plain,(
    ! [A_13,B_14] : k5_xboole_0(k4_xboole_0(A_13,B_14),k2_xboole_0(A_13,k3_xboole_0(A_13,B_14))) = k3_xboole_0(A_13,k3_xboole_0(A_13,B_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1319])).

tff(c_1396,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,k3_xboole_0(A_13,B_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_22,c_1352])).

tff(c_5620,plain,(
    ! [A_216,B_217] : k5_xboole_0(A_216,k4_xboole_0(A_216,B_217)) = k3_xboole_0(A_216,B_217) ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_1396])).

tff(c_5693,plain,(
    ! [A_32,B_33] : k5_xboole_0(A_32,k3_xboole_0(A_32,B_33)) = k3_xboole_0(A_32,k4_xboole_0(A_32,B_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_5620])).

tff(c_5719,plain,(
    ! [A_32,B_33] : k3_xboole_0(A_32,k4_xboole_0(A_32,B_33)) = k4_xboole_0(A_32,B_33) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_5693])).

tff(c_48,plain,(
    ! [A_42,B_43] :
      ( k4_xboole_0(k2_xboole_0(A_42,B_43),B_43) = A_42
      | ~ r1_xboole_0(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1252,plain,(
    ! [A_114,B_115] : k4_xboole_0(A_114,k2_xboole_0(B_115,A_114)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1185])).

tff(c_1188,plain,(
    ! [C_116,A_114,B_115] : k2_xboole_0(C_116,k4_xboole_0(A_114,k2_xboole_0(B_115,C_116))) = k2_xboole_0(C_116,k4_xboole_0(A_114,B_115)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1175,c_28])).

tff(c_32,plain,(
    ! [A_27,B_28,C_29] : k4_xboole_0(k4_xboole_0(A_27,B_28),C_29) = k4_xboole_0(A_27,k2_xboole_0(B_28,C_29)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1199,plain,(
    ! [A_114,B_115,B_33] : k4_xboole_0(A_114,k2_xboole_0(B_115,k4_xboole_0(k4_xboole_0(A_114,B_115),B_33))) = k3_xboole_0(k4_xboole_0(A_114,B_115),B_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_1175,c_36])).

tff(c_68152,plain,(
    ! [A_644,B_645,B_646] : k4_xboole_0(A_644,k2_xboole_0(B_645,k4_xboole_0(A_644,k2_xboole_0(B_645,B_646)))) = k3_xboole_0(k4_xboole_0(A_644,B_645),B_646) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1199])).

tff(c_68522,plain,(
    ! [A_114,B_115] : k4_xboole_0(A_114,k2_xboole_0(B_115,k4_xboole_0(A_114,B_115))) = k3_xboole_0(k4_xboole_0(A_114,B_115),B_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_1188,c_68152])).

tff(c_69105,plain,(
    ! [B_647,A_648] : k3_xboole_0(B_647,k4_xboole_0(A_648,B_647)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1252,c_28,c_6,c_68522])).

tff(c_69987,plain,(
    ! [B_651,A_652] :
      ( k3_xboole_0(B_651,A_652) = k1_xboole_0
      | ~ r1_xboole_0(A_652,B_651) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_69105])).

tff(c_93752,plain,(
    ! [B_734,A_735] :
      ( k3_xboole_0(B_734,A_735) = k1_xboole_0
      | k4_xboole_0(A_735,B_734) != A_735 ) ),
    inference(resolution,[status(thm)],[c_46,c_69987])).

tff(c_93980,plain,(
    ! [A_32,B_33] :
      ( k3_xboole_0(k4_xboole_0(A_32,B_33),A_32) = k1_xboole_0
      | k3_xboole_0(A_32,B_33) != A_32 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_93752])).

tff(c_94023,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,B_33) = k1_xboole_0
      | k3_xboole_0(A_32,B_33) != A_32 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5719,c_6,c_93980])).

tff(c_155686,plain,(
    ! [A_983,B_982] :
      ( k4_xboole_0(A_983,B_982) = k1_xboole_0
      | k3_xboole_0(k2_xboole_0(B_982,A_983),B_982) != k2_xboole_0(B_982,A_983) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155626,c_94023])).

tff(c_193438,plain,(
    ! [A_1138,B_1139] :
      ( k4_xboole_0(A_1138,B_1139) = k1_xboole_0
      | k2_xboole_0(B_1139,A_1138) != B_1139 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1640,c_6,c_155686])).

tff(c_687,plain,(
    ! [B_96] : k2_xboole_0(B_96,k1_xboole_0) = B_96 ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_672])).

tff(c_38,plain,(
    ! [A_34,B_35] : k2_xboole_0(k3_xboole_0(A_34,B_35),k4_xboole_0(A_34,B_35)) = A_34 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2083,plain,(
    ! [A_138,B_139] : k4_xboole_0(k4_xboole_0(A_138,B_139),A_138) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1477])).

tff(c_2097,plain,(
    ! [A_138,B_139] : k2_xboole_0(A_138,k4_xboole_0(A_138,B_139)) = k2_xboole_0(A_138,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2083,c_28])).

tff(c_2161,plain,(
    ! [A_138,B_139] : k2_xboole_0(A_138,k4_xboole_0(A_138,B_139)) = A_138 ),
    inference(demodulation,[status(thm),theory(equality)],[c_687,c_2097])).

tff(c_2630,plain,(
    ! [B_41,C_153] :
      ( k3_xboole_0(B_41,C_153) = B_41
      | k1_xboole_0 != B_41 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_913,c_2625])).

tff(c_380,plain,(
    ! [A_86,B_87] : k2_xboole_0(k3_xboole_0(A_86,B_87),k4_xboole_0(A_86,B_87)) = A_86 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2842,plain,(
    ! [A_158,B_159] : k2_xboole_0(k3_xboole_0(A_158,B_159),k4_xboole_0(B_159,A_158)) = B_159 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_380])).

tff(c_2882,plain,(
    ! [B_41,C_153] :
      ( k2_xboole_0(B_41,k4_xboole_0(C_153,B_41)) = C_153
      | k1_xboole_0 != B_41 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2630,c_2842])).

tff(c_3249,plain,(
    ! [C_153] : k2_xboole_0(k1_xboole_0,C_153) = C_153 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2882])).

tff(c_3251,plain,(
    ! [B_164,C_165] :
      ( k2_xboole_0(B_164,C_165) = C_165
      | k1_xboole_0 != B_164 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2882])).

tff(c_34928,plain,(
    ! [B_25] : k4_xboole_0(B_25,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_3251,c_28])).

tff(c_69004,plain,(
    ! [B_115,A_114] : k3_xboole_0(B_115,k4_xboole_0(A_114,B_115)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1252,c_28,c_6,c_68522])).

tff(c_1404,plain,(
    ! [A_120,B_121] : k4_xboole_0(k2_xboole_0(A_120,B_121),k3_xboole_0(A_120,B_121)) = k5_xboole_0(A_120,B_121) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1443,plain,(
    ! [A_24,B_25] : k4_xboole_0(k2_xboole_0(A_24,B_25),k3_xboole_0(A_24,k4_xboole_0(B_25,A_24))) = k5_xboole_0(A_24,k4_xboole_0(B_25,A_24)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1404])).

tff(c_94028,plain,(
    ! [A_736,B_737] : k5_xboole_0(A_736,k4_xboole_0(B_737,A_736)) = k2_xboole_0(A_736,B_737) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3249,c_34928,c_69004,c_1443])).

tff(c_94371,plain,(
    ! [A_32,B_33] : k5_xboole_0(k4_xboole_0(A_32,B_33),k3_xboole_0(A_32,B_33)) = k2_xboole_0(k4_xboole_0(A_32,B_33),A_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_94028])).

tff(c_167339,plain,(
    ! [A_1019,B_1020] : k5_xboole_0(k4_xboole_0(A_1019,B_1020),k3_xboole_0(A_1019,B_1020)) = A_1019 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2161,c_4,c_94371])).

tff(c_168100,plain,(
    ! [A_5,B_6] : k5_xboole_0(k4_xboole_0(A_5,B_6),k3_xboole_0(B_6,A_5)) = A_5 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_167339])).

tff(c_193495,plain,(
    ! [B_1139,A_1138] :
      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(B_1139,A_1138)) = A_1138
      | k2_xboole_0(B_1139,A_1138) != B_1139 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_193438,c_168100])).

tff(c_202671,plain,(
    ! [B_1166,A_1167] :
      ( k3_xboole_0(B_1166,A_1167) = A_1167
      | k2_xboole_0(B_1166,A_1167) != B_1166 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_193495])).

tff(c_62,plain,(
    k3_xboole_0(k2_tarski('#skF_1','#skF_3'),'#skF_2') != k2_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_67,plain,(
    k3_xboole_0('#skF_2',k2_tarski('#skF_1','#skF_3')) != k2_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_62])).

tff(c_203989,plain,(
    k2_xboole_0('#skF_2',k2_tarski('#skF_1','#skF_3')) != '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_202671,c_67])).

tff(c_204049,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2035,c_203989])).

tff(c_204059,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_204049])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n016.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 17:17:04 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 54.07/43.91  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 54.07/43.92  
% 54.07/43.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 54.07/43.92  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 54.07/43.92  
% 54.07/43.92  %Foreground sorts:
% 54.07/43.92  
% 54.07/43.92  
% 54.07/43.92  %Background operators:
% 54.07/43.92  
% 54.07/43.92  
% 54.07/43.92  %Foreground operators:
% 54.07/43.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 54.07/43.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 54.07/43.92  tff(k1_tarski, type, k1_tarski: $i > $i).
% 54.07/43.92  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 54.07/43.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 54.07/43.92  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 54.07/43.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 54.07/43.92  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 54.07/43.92  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 54.07/43.92  tff('#skF_2', type, '#skF_2': $i).
% 54.07/43.92  tff('#skF_3', type, '#skF_3': $i).
% 54.07/43.92  tff('#skF_1', type, '#skF_1': $i).
% 54.07/43.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 54.07/43.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 54.07/43.92  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 54.07/43.92  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 54.07/43.92  
% 54.07/43.95  tff(f_106, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k3_xboole_0(k2_tarski(A, C), B) = k2_tarski(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_zfmisc_1)).
% 54.07/43.95  tff(f_99, axiom, (![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k2_xboole_0(k2_tarski(A, C), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 54.07/43.95  tff(f_32, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 54.07/43.95  tff(f_36, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 54.07/43.95  tff(f_70, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 54.07/43.95  tff(f_60, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 54.07/43.95  tff(f_34, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 54.07/43.95  tff(f_50, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 54.07/43.95  tff(f_46, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 54.07/43.95  tff(f_58, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 54.07/43.95  tff(f_66, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 54.07/43.95  tff(f_62, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 54.07/43.95  tff(f_78, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 54.07/43.95  tff(f_74, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_xboole_1)).
% 54.07/43.95  tff(f_64, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 54.07/43.95  tff(f_86, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 54.07/43.95  tff(f_82, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 54.07/43.95  tff(f_68, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 54.07/43.95  tff(f_48, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t101_xboole_1)).
% 54.07/43.95  tff(c_66, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 54.07/43.95  tff(c_64, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 54.07/43.95  tff(c_1982, plain, (![A_135, C_136, B_137]: (k2_xboole_0(k2_tarski(A_135, C_136), B_137)=B_137 | ~r2_hidden(C_136, B_137) | ~r2_hidden(A_135, B_137))), inference(cnfTransformation, [status(thm)], [f_99])).
% 54.07/43.95  tff(c_4, plain, (![B_4, A_3]: (k2_xboole_0(B_4, A_3)=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_32])).
% 54.07/43.95  tff(c_2035, plain, (![B_137, A_135, C_136]: (k2_xboole_0(B_137, k2_tarski(A_135, C_136))=B_137 | ~r2_hidden(C_136, B_137) | ~r2_hidden(A_135, B_137))), inference(superposition, [status(thm), theory('equality')], [c_1982, c_4])).
% 54.07/43.95  tff(c_136, plain, (![B_59, A_60]: (k5_xboole_0(B_59, A_60)=k5_xboole_0(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_36])).
% 54.07/43.95  tff(c_40, plain, (![A_36]: (k5_xboole_0(A_36, k1_xboole_0)=A_36)), inference(cnfTransformation, [status(thm)], [f_70])).
% 54.07/43.95  tff(c_152, plain, (![A_60]: (k5_xboole_0(k1_xboole_0, A_60)=A_60)), inference(superposition, [status(thm), theory('equality')], [c_136, c_40])).
% 54.07/43.95  tff(c_30, plain, (![A_26]: (k4_xboole_0(A_26, k1_xboole_0)=A_26)), inference(cnfTransformation, [status(thm)], [f_60])).
% 54.07/43.95  tff(c_6, plain, (![B_6, A_5]: (k3_xboole_0(B_6, A_5)=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 54.07/43.95  tff(c_306, plain, (![A_68, B_69]: (k2_xboole_0(A_68, k3_xboole_0(A_68, B_69))=A_68)), inference(cnfTransformation, [status(thm)], [f_50])).
% 54.07/43.95  tff(c_315, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k3_xboole_0(B_6, A_5))=A_5)), inference(superposition, [status(thm), theory('equality')], [c_6, c_306])).
% 54.07/43.95  tff(c_579, plain, (![A_95, B_96]: (k5_xboole_0(A_95, k3_xboole_0(A_95, B_96))=k4_xboole_0(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_46])).
% 54.07/43.95  tff(c_586, plain, (![B_96]: (k4_xboole_0(k1_xboole_0, B_96)=k3_xboole_0(k1_xboole_0, B_96))), inference(superposition, [status(thm), theory('equality')], [c_579, c_152])).
% 54.07/43.95  tff(c_663, plain, (![A_98, B_99]: (k2_xboole_0(A_98, k4_xboole_0(B_99, A_98))=k2_xboole_0(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_58])).
% 54.07/43.95  tff(c_672, plain, (![B_96]: (k2_xboole_0(B_96, k3_xboole_0(k1_xboole_0, B_96))=k2_xboole_0(B_96, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_586, c_663])).
% 54.07/43.95  tff(c_759, plain, (![B_103]: (k2_xboole_0(B_103, k1_xboole_0)=B_103)), inference(demodulation, [status(thm), theory('equality')], [c_315, c_672])).
% 54.07/43.95  tff(c_812, plain, (![B_104]: (k2_xboole_0(k1_xboole_0, B_104)=B_104)), inference(superposition, [status(thm), theory('equality')], [c_759, c_4])).
% 54.07/43.95  tff(c_22, plain, (![A_17, B_18]: (k2_xboole_0(A_17, k3_xboole_0(A_17, B_18))=A_17)), inference(cnfTransformation, [status(thm)], [f_50])).
% 54.07/43.95  tff(c_835, plain, (![B_18]: (k3_xboole_0(k1_xboole_0, B_18)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_812, c_22])).
% 54.07/43.95  tff(c_962, plain, (![B_96]: (k4_xboole_0(k1_xboole_0, B_96)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_835, c_586])).
% 54.07/43.95  tff(c_860, plain, (![B_6]: (k3_xboole_0(B_6, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_315, c_812])).
% 54.07/43.95  tff(c_433, plain, (![A_89, B_90]: (k4_xboole_0(A_89, k4_xboole_0(A_89, B_90))=k3_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_66])).
% 54.07/43.95  tff(c_451, plain, (![A_26]: (k4_xboole_0(A_26, A_26)=k3_xboole_0(A_26, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_433])).
% 54.07/43.95  tff(c_913, plain, (![A_26]: (k4_xboole_0(A_26, A_26)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_860, c_451])).
% 54.07/43.95  tff(c_1175, plain, (![A_114, B_115, C_116]: (k4_xboole_0(k4_xboole_0(A_114, B_115), C_116)=k4_xboole_0(A_114, k2_xboole_0(B_115, C_116)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 54.07/43.95  tff(c_1215, plain, (![A_26, C_116]: (k4_xboole_0(A_26, k2_xboole_0(A_26, C_116))=k4_xboole_0(k1_xboole_0, C_116))), inference(superposition, [status(thm), theory('equality')], [c_913, c_1175])).
% 54.07/43.95  tff(c_1559, plain, (![A_124, C_125]: (k4_xboole_0(A_124, k2_xboole_0(A_124, C_125))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_962, c_1215])).
% 54.07/43.95  tff(c_36, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k4_xboole_0(A_32, B_33))=k3_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_66])).
% 54.07/43.95  tff(c_1588, plain, (![A_124, C_125]: (k3_xboole_0(A_124, k2_xboole_0(A_124, C_125))=k4_xboole_0(A_124, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1559, c_36])).
% 54.07/43.95  tff(c_1640, plain, (![A_124, C_125]: (k3_xboole_0(A_124, k2_xboole_0(A_124, C_125))=A_124)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1588])).
% 54.07/43.95  tff(c_28, plain, (![A_24, B_25]: (k2_xboole_0(A_24, k4_xboole_0(B_25, A_24))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_58])).
% 54.07/43.95  tff(c_1185, plain, (![A_114, B_115]: (k4_xboole_0(A_114, k2_xboole_0(B_115, k4_xboole_0(A_114, B_115)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1175, c_913])).
% 54.07/43.95  tff(c_1477, plain, (![A_122, B_123]: (k4_xboole_0(A_122, k2_xboole_0(B_123, A_122))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1185])).
% 54.07/43.95  tff(c_1503, plain, (![A_122, B_123]: (k3_xboole_0(A_122, k2_xboole_0(B_123, A_122))=k4_xboole_0(A_122, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1477, c_36])).
% 54.07/43.95  tff(c_1551, plain, (![A_122, B_123]: (k3_xboole_0(A_122, k2_xboole_0(B_123, A_122))=A_122)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1503])).
% 54.07/43.95  tff(c_678, plain, (![A_26]: (k2_xboole_0(A_26, k3_xboole_0(A_26, k1_xboole_0))=k2_xboole_0(A_26, A_26))), inference(superposition, [status(thm), theory('equality')], [c_451, c_663])).
% 54.07/43.95  tff(c_689, plain, (![A_26]: (k2_xboole_0(A_26, A_26)=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_678])).
% 54.07/43.95  tff(c_46, plain, (![A_40, B_41]: (r1_xboole_0(A_40, B_41) | k4_xboole_0(A_40, B_41)!=A_40)), inference(cnfTransformation, [status(thm)], [f_78])).
% 54.07/43.95  tff(c_42, plain, (![A_37, B_38, C_39]: (k3_xboole_0(A_37, k2_xboole_0(B_38, C_39))=k3_xboole_0(A_37, C_39) | ~r1_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_74])).
% 54.07/43.95  tff(c_1885, plain, (![A_133, C_134]: (k3_xboole_0(A_133, k2_xboole_0(A_133, C_134))=A_133)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1588])).
% 54.07/43.95  tff(c_2622, plain, (![B_152, C_153]: (k3_xboole_0(B_152, C_153)=B_152 | ~r1_xboole_0(B_152, B_152))), inference(superposition, [status(thm), theory('equality')], [c_42, c_1885])).
% 54.07/43.95  tff(c_2625, plain, (![B_41, C_153]: (k3_xboole_0(B_41, C_153)=B_41 | k4_xboole_0(B_41, B_41)!=B_41)), inference(resolution, [status(thm)], [c_46, c_2622])).
% 54.07/43.95  tff(c_2635, plain, (![B_154, C_155]: (k3_xboole_0(B_154, C_155)=B_154 | k1_xboole_0!=B_154)), inference(demodulation, [status(thm), theory('equality')], [c_913, c_2625])).
% 54.07/43.95  tff(c_2973, plain, (![C_155]: (k2_xboole_0(C_155, k1_xboole_0)=C_155)), inference(superposition, [status(thm), theory('equality')], [c_2635, c_315])).
% 54.07/43.95  tff(c_777, plain, (![B_103]: (k2_xboole_0(k1_xboole_0, B_103)=B_103)), inference(superposition, [status(thm), theory('equality')], [c_759, c_4])).
% 54.07/43.95  tff(c_1585, plain, (![A_124, C_125]: (k2_xboole_0(k2_xboole_0(A_124, C_125), k1_xboole_0)=k2_xboole_0(k2_xboole_0(A_124, C_125), A_124))), inference(superposition, [status(thm), theory('equality')], [c_1559, c_28])).
% 54.07/43.95  tff(c_5914, plain, (![A_220, C_221]: (k2_xboole_0(k2_xboole_0(A_220, C_221), A_220)=k2_xboole_0(A_220, C_221))), inference(demodulation, [status(thm), theory('equality')], [c_777, c_4, c_1585])).
% 54.07/43.95  tff(c_11817, plain, (![B_283, A_284]: (k2_xboole_0(k2_xboole_0(B_283, A_284), A_284)=k2_xboole_0(A_284, B_283))), inference(superposition, [status(thm), theory('equality')], [c_4, c_5914])).
% 54.07/43.95  tff(c_1258, plain, (![A_26, C_116]: (k4_xboole_0(A_26, k2_xboole_0(A_26, C_116))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_962, c_1215])).
% 54.07/43.95  tff(c_11944, plain, (![B_283, A_284]: (k4_xboole_0(k2_xboole_0(B_283, A_284), k2_xboole_0(A_284, B_283))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_11817, c_1258])).
% 54.07/43.95  tff(c_47415, plain, (![C_547, A_548, B_549]: (k2_xboole_0(C_547, k4_xboole_0(A_548, k2_xboole_0(B_549, C_547)))=k2_xboole_0(C_547, k4_xboole_0(A_548, B_549)))), inference(superposition, [status(thm), theory('equality')], [c_1175, c_28])).
% 54.07/43.95  tff(c_47815, plain, (![B_283, A_284]: (k2_xboole_0(B_283, k4_xboole_0(k2_xboole_0(B_283, A_284), A_284))=k2_xboole_0(B_283, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_11944, c_47415])).
% 54.07/43.95  tff(c_48131, plain, (![B_550, A_551]: (k2_xboole_0(B_550, k4_xboole_0(k2_xboole_0(B_550, A_551), A_551))=B_550)), inference(demodulation, [status(thm), theory('equality')], [c_2973, c_47815])).
% 54.07/43.95  tff(c_1500, plain, (![B_123, A_122]: (k2_xboole_0(k2_xboole_0(B_123, A_122), k1_xboole_0)=k2_xboole_0(k2_xboole_0(B_123, A_122), A_122))), inference(superposition, [status(thm), theory('equality')], [c_1477, c_28])).
% 54.07/43.95  tff(c_6951, plain, (![B_235, A_236]: (k2_xboole_0(k2_xboole_0(B_235, A_236), A_236)=k2_xboole_0(B_235, A_236))), inference(demodulation, [status(thm), theory('equality')], [c_777, c_4, c_1500])).
% 54.07/43.95  tff(c_7341, plain, (![A_239, B_240]: (k2_xboole_0(A_239, k2_xboole_0(B_240, A_239))=k2_xboole_0(B_240, A_239))), inference(superposition, [status(thm), theory('equality')], [c_4, c_6951])).
% 54.07/43.95  tff(c_7482, plain, (![B_4, A_3]: (k2_xboole_0(B_4, k2_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_7341])).
% 54.07/43.95  tff(c_48228, plain, (![B_550, A_551]: (k2_xboole_0(k4_xboole_0(k2_xboole_0(B_550, A_551), A_551), B_550)=k2_xboole_0(B_550, B_550))), inference(superposition, [status(thm), theory('equality')], [c_48131, c_7482])).
% 54.07/43.95  tff(c_50199, plain, (![B_558, A_559]: (k2_xboole_0(k4_xboole_0(k2_xboole_0(B_558, A_559), A_559), B_558)=B_558)), inference(demodulation, [status(thm), theory('equality')], [c_689, c_48228])).
% 54.07/43.95  tff(c_1238, plain, (![A_32, B_33, C_116]: (k4_xboole_0(A_32, k2_xboole_0(k4_xboole_0(A_32, B_33), C_116))=k4_xboole_0(k3_xboole_0(A_32, B_33), C_116))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1175])).
% 54.07/43.95  tff(c_50227, plain, (![B_558, A_559]: (k4_xboole_0(k3_xboole_0(k2_xboole_0(B_558, A_559), A_559), B_558)=k4_xboole_0(k2_xboole_0(B_558, A_559), B_558))), inference(superposition, [status(thm), theory('equality')], [c_50199, c_1238])).
% 54.07/43.95  tff(c_155626, plain, (![B_982, A_983]: (k4_xboole_0(k2_xboole_0(B_982, A_983), B_982)=k4_xboole_0(A_983, B_982))), inference(demodulation, [status(thm), theory('equality')], [c_1551, c_6, c_50227])).
% 54.07/43.95  tff(c_18, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 54.07/43.95  tff(c_500, plain, (![A_92, B_93]: (k4_xboole_0(A_92, k3_xboole_0(A_92, B_93))=k4_xboole_0(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_64])).
% 54.07/43.95  tff(c_506, plain, (![A_92, B_93]: (k4_xboole_0(A_92, k4_xboole_0(A_92, B_93))=k3_xboole_0(A_92, k3_xboole_0(A_92, B_93)))), inference(superposition, [status(thm), theory('equality')], [c_500, c_36])).
% 54.07/43.95  tff(c_523, plain, (![A_92, B_93]: (k3_xboole_0(A_92, k3_xboole_0(A_92, B_93))=k3_xboole_0(A_92, B_93))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_506])).
% 54.07/43.95  tff(c_8, plain, (![B_8, A_7]: (k5_xboole_0(B_8, A_7)=k5_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_36])).
% 54.07/43.95  tff(c_1319, plain, (![A_118, B_119]: (k5_xboole_0(k5_xboole_0(A_118, B_119), k2_xboole_0(A_118, B_119))=k3_xboole_0(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_86])).
% 54.07/43.95  tff(c_1352, plain, (![A_13, B_14]: (k5_xboole_0(k4_xboole_0(A_13, B_14), k2_xboole_0(A_13, k3_xboole_0(A_13, B_14)))=k3_xboole_0(A_13, k3_xboole_0(A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1319])).
% 54.07/43.95  tff(c_1396, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, k3_xboole_0(A_13, B_14)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_22, c_1352])).
% 54.07/43.95  tff(c_5620, plain, (![A_216, B_217]: (k5_xboole_0(A_216, k4_xboole_0(A_216, B_217))=k3_xboole_0(A_216, B_217))), inference(demodulation, [status(thm), theory('equality')], [c_523, c_1396])).
% 54.07/43.95  tff(c_5693, plain, (![A_32, B_33]: (k5_xboole_0(A_32, k3_xboole_0(A_32, B_33))=k3_xboole_0(A_32, k4_xboole_0(A_32, B_33)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_5620])).
% 54.07/43.95  tff(c_5719, plain, (![A_32, B_33]: (k3_xboole_0(A_32, k4_xboole_0(A_32, B_33))=k4_xboole_0(A_32, B_33))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_5693])).
% 54.07/43.95  tff(c_48, plain, (![A_42, B_43]: (k4_xboole_0(k2_xboole_0(A_42, B_43), B_43)=A_42 | ~r1_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_82])).
% 54.07/43.95  tff(c_1252, plain, (![A_114, B_115]: (k4_xboole_0(A_114, k2_xboole_0(B_115, A_114))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1185])).
% 54.07/43.95  tff(c_1188, plain, (![C_116, A_114, B_115]: (k2_xboole_0(C_116, k4_xboole_0(A_114, k2_xboole_0(B_115, C_116)))=k2_xboole_0(C_116, k4_xboole_0(A_114, B_115)))), inference(superposition, [status(thm), theory('equality')], [c_1175, c_28])).
% 54.07/43.95  tff(c_32, plain, (![A_27, B_28, C_29]: (k4_xboole_0(k4_xboole_0(A_27, B_28), C_29)=k4_xboole_0(A_27, k2_xboole_0(B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 54.07/43.95  tff(c_1199, plain, (![A_114, B_115, B_33]: (k4_xboole_0(A_114, k2_xboole_0(B_115, k4_xboole_0(k4_xboole_0(A_114, B_115), B_33)))=k3_xboole_0(k4_xboole_0(A_114, B_115), B_33))), inference(superposition, [status(thm), theory('equality')], [c_1175, c_36])).
% 54.07/43.95  tff(c_68152, plain, (![A_644, B_645, B_646]: (k4_xboole_0(A_644, k2_xboole_0(B_645, k4_xboole_0(A_644, k2_xboole_0(B_645, B_646))))=k3_xboole_0(k4_xboole_0(A_644, B_645), B_646))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1199])).
% 54.07/43.95  tff(c_68522, plain, (![A_114, B_115]: (k4_xboole_0(A_114, k2_xboole_0(B_115, k4_xboole_0(A_114, B_115)))=k3_xboole_0(k4_xboole_0(A_114, B_115), B_115))), inference(superposition, [status(thm), theory('equality')], [c_1188, c_68152])).
% 54.07/43.95  tff(c_69105, plain, (![B_647, A_648]: (k3_xboole_0(B_647, k4_xboole_0(A_648, B_647))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1252, c_28, c_6, c_68522])).
% 54.07/43.95  tff(c_69987, plain, (![B_651, A_652]: (k3_xboole_0(B_651, A_652)=k1_xboole_0 | ~r1_xboole_0(A_652, B_651))), inference(superposition, [status(thm), theory('equality')], [c_48, c_69105])).
% 54.07/43.95  tff(c_93752, plain, (![B_734, A_735]: (k3_xboole_0(B_734, A_735)=k1_xboole_0 | k4_xboole_0(A_735, B_734)!=A_735)), inference(resolution, [status(thm)], [c_46, c_69987])).
% 54.07/43.95  tff(c_93980, plain, (![A_32, B_33]: (k3_xboole_0(k4_xboole_0(A_32, B_33), A_32)=k1_xboole_0 | k3_xboole_0(A_32, B_33)!=A_32)), inference(superposition, [status(thm), theory('equality')], [c_36, c_93752])).
% 54.07/43.95  tff(c_94023, plain, (![A_32, B_33]: (k4_xboole_0(A_32, B_33)=k1_xboole_0 | k3_xboole_0(A_32, B_33)!=A_32)), inference(demodulation, [status(thm), theory('equality')], [c_5719, c_6, c_93980])).
% 54.07/43.95  tff(c_155686, plain, (![A_983, B_982]: (k4_xboole_0(A_983, B_982)=k1_xboole_0 | k3_xboole_0(k2_xboole_0(B_982, A_983), B_982)!=k2_xboole_0(B_982, A_983))), inference(superposition, [status(thm), theory('equality')], [c_155626, c_94023])).
% 54.07/43.95  tff(c_193438, plain, (![A_1138, B_1139]: (k4_xboole_0(A_1138, B_1139)=k1_xboole_0 | k2_xboole_0(B_1139, A_1138)!=B_1139)), inference(demodulation, [status(thm), theory('equality')], [c_1640, c_6, c_155686])).
% 54.07/43.95  tff(c_687, plain, (![B_96]: (k2_xboole_0(B_96, k1_xboole_0)=B_96)), inference(demodulation, [status(thm), theory('equality')], [c_315, c_672])).
% 54.07/43.95  tff(c_38, plain, (![A_34, B_35]: (k2_xboole_0(k3_xboole_0(A_34, B_35), k4_xboole_0(A_34, B_35))=A_34)), inference(cnfTransformation, [status(thm)], [f_68])).
% 54.07/43.95  tff(c_2083, plain, (![A_138, B_139]: (k4_xboole_0(k4_xboole_0(A_138, B_139), A_138)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_38, c_1477])).
% 54.07/43.95  tff(c_2097, plain, (![A_138, B_139]: (k2_xboole_0(A_138, k4_xboole_0(A_138, B_139))=k2_xboole_0(A_138, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2083, c_28])).
% 54.07/43.95  tff(c_2161, plain, (![A_138, B_139]: (k2_xboole_0(A_138, k4_xboole_0(A_138, B_139))=A_138)), inference(demodulation, [status(thm), theory('equality')], [c_687, c_2097])).
% 54.07/43.95  tff(c_2630, plain, (![B_41, C_153]: (k3_xboole_0(B_41, C_153)=B_41 | k1_xboole_0!=B_41)), inference(demodulation, [status(thm), theory('equality')], [c_913, c_2625])).
% 54.07/43.95  tff(c_380, plain, (![A_86, B_87]: (k2_xboole_0(k3_xboole_0(A_86, B_87), k4_xboole_0(A_86, B_87))=A_86)), inference(cnfTransformation, [status(thm)], [f_68])).
% 54.07/43.95  tff(c_2842, plain, (![A_158, B_159]: (k2_xboole_0(k3_xboole_0(A_158, B_159), k4_xboole_0(B_159, A_158))=B_159)), inference(superposition, [status(thm), theory('equality')], [c_6, c_380])).
% 54.07/43.95  tff(c_2882, plain, (![B_41, C_153]: (k2_xboole_0(B_41, k4_xboole_0(C_153, B_41))=C_153 | k1_xboole_0!=B_41)), inference(superposition, [status(thm), theory('equality')], [c_2630, c_2842])).
% 54.07/43.95  tff(c_3249, plain, (![C_153]: (k2_xboole_0(k1_xboole_0, C_153)=C_153)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2882])).
% 54.07/43.95  tff(c_3251, plain, (![B_164, C_165]: (k2_xboole_0(B_164, C_165)=C_165 | k1_xboole_0!=B_164)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2882])).
% 54.07/43.95  tff(c_34928, plain, (![B_25]: (k4_xboole_0(B_25, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_25))), inference(superposition, [status(thm), theory('equality')], [c_3251, c_28])).
% 54.07/43.95  tff(c_69004, plain, (![B_115, A_114]: (k3_xboole_0(B_115, k4_xboole_0(A_114, B_115))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1252, c_28, c_6, c_68522])).
% 54.07/43.95  tff(c_1404, plain, (![A_120, B_121]: (k4_xboole_0(k2_xboole_0(A_120, B_121), k3_xboole_0(A_120, B_121))=k5_xboole_0(A_120, B_121))), inference(cnfTransformation, [status(thm)], [f_48])).
% 54.07/43.95  tff(c_1443, plain, (![A_24, B_25]: (k4_xboole_0(k2_xboole_0(A_24, B_25), k3_xboole_0(A_24, k4_xboole_0(B_25, A_24)))=k5_xboole_0(A_24, k4_xboole_0(B_25, A_24)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1404])).
% 54.07/43.95  tff(c_94028, plain, (![A_736, B_737]: (k5_xboole_0(A_736, k4_xboole_0(B_737, A_736))=k2_xboole_0(A_736, B_737))), inference(demodulation, [status(thm), theory('equality')], [c_3249, c_34928, c_69004, c_1443])).
% 54.07/43.95  tff(c_94371, plain, (![A_32, B_33]: (k5_xboole_0(k4_xboole_0(A_32, B_33), k3_xboole_0(A_32, B_33))=k2_xboole_0(k4_xboole_0(A_32, B_33), A_32))), inference(superposition, [status(thm), theory('equality')], [c_36, c_94028])).
% 54.07/43.95  tff(c_167339, plain, (![A_1019, B_1020]: (k5_xboole_0(k4_xboole_0(A_1019, B_1020), k3_xboole_0(A_1019, B_1020))=A_1019)), inference(demodulation, [status(thm), theory('equality')], [c_2161, c_4, c_94371])).
% 54.07/43.95  tff(c_168100, plain, (![A_5, B_6]: (k5_xboole_0(k4_xboole_0(A_5, B_6), k3_xboole_0(B_6, A_5))=A_5)), inference(superposition, [status(thm), theory('equality')], [c_6, c_167339])).
% 54.07/43.95  tff(c_193495, plain, (![B_1139, A_1138]: (k5_xboole_0(k1_xboole_0, k3_xboole_0(B_1139, A_1138))=A_1138 | k2_xboole_0(B_1139, A_1138)!=B_1139)), inference(superposition, [status(thm), theory('equality')], [c_193438, c_168100])).
% 54.07/43.95  tff(c_202671, plain, (![B_1166, A_1167]: (k3_xboole_0(B_1166, A_1167)=A_1167 | k2_xboole_0(B_1166, A_1167)!=B_1166)), inference(demodulation, [status(thm), theory('equality')], [c_152, c_193495])).
% 54.07/43.95  tff(c_62, plain, (k3_xboole_0(k2_tarski('#skF_1', '#skF_3'), '#skF_2')!=k2_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 54.07/43.95  tff(c_67, plain, (k3_xboole_0('#skF_2', k2_tarski('#skF_1', '#skF_3'))!=k2_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_62])).
% 54.07/43.95  tff(c_203989, plain, (k2_xboole_0('#skF_2', k2_tarski('#skF_1', '#skF_3'))!='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_202671, c_67])).
% 54.07/43.95  tff(c_204049, plain, (~r2_hidden('#skF_3', '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2035, c_203989])).
% 54.07/43.95  tff(c_204059, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_204049])).
% 54.07/43.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 54.07/43.95  
% 54.07/43.95  Inference rules
% 54.07/43.95  ----------------------
% 54.07/43.95  #Ref     : 4
% 54.07/43.95  #Sup     : 54164
% 54.07/43.95  #Fact    : 0
% 54.07/43.95  #Define  : 0
% 54.07/43.95  #Split   : 1
% 54.07/43.95  #Chain   : 0
% 54.07/43.95  #Close   : 0
% 54.07/43.95  
% 54.07/43.95  Ordering : KBO
% 54.07/43.95  
% 54.07/43.95  Simplification rules
% 54.07/43.95  ----------------------
% 54.07/43.95  #Subsume      : 11843
% 54.07/43.95  #Demod        : 45882
% 54.07/43.95  #Tautology    : 20871
% 54.07/43.95  #SimpNegUnit  : 56
% 54.07/43.95  #BackRed      : 33
% 54.07/43.95  
% 54.07/43.95  #Partial instantiations: 0
% 54.07/43.95  #Strategies tried      : 1
% 54.07/43.95  
% 54.07/43.95  Timing (in seconds)
% 54.07/43.95  ----------------------
% 54.07/43.95  Preprocessing        : 0.42
% 54.07/43.95  Parsing              : 0.20
% 54.07/43.95  CNF conversion       : 0.03
% 54.07/43.95  Main loop            : 42.73
% 54.07/43.95  Inferencing          : 3.57
% 54.07/43.95  Reduction            : 27.63
% 54.07/43.95  Demodulation         : 25.45
% 54.07/43.95  BG Simplification    : 0.56
% 54.07/43.95  Subsumption          : 8.75
% 54.07/43.95  Abstraction          : 1.01
% 54.07/43.95  MUC search           : 0.00
% 54.07/43.95  Cooper               : 0.00
% 54.07/43.95  Total                : 43.21
% 54.07/43.95  Index Insertion      : 0.00
% 54.07/43.95  Index Deletion       : 0.00
% 54.07/43.95  Index Matching       : 0.00
% 54.07/43.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
