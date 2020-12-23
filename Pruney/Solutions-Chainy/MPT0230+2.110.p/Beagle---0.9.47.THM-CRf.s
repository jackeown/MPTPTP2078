%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:10 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 113 expanded)
%              Number of leaves         :   43 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :   86 ( 126 expanded)
%              Number of equality atoms :   65 (  90 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_106,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_88,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_86,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_90,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_92,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_82,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_59,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_61,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_80,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

tff(c_64,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_66,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_54,plain,(
    ! [A_39,B_40,C_41] : k2_enumset1(A_39,A_39,B_40,C_41) = k1_enumset1(A_39,B_40,C_41) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_52,plain,(
    ! [A_37,B_38] : k1_enumset1(A_37,A_37,B_38) = k2_tarski(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_56,plain,(
    ! [A_42,B_43,C_44,D_45] : k3_enumset1(A_42,A_42,B_43,C_44,D_45) = k2_enumset1(A_42,B_43,C_44,D_45) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_58,plain,(
    ! [A_46,E_50,B_47,C_48,D_49] : k4_enumset1(A_46,A_46,B_47,C_48,D_49,E_50) = k3_enumset1(A_46,B_47,C_48,D_49,E_50) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_952,plain,(
    ! [C_163,D_168,A_166,B_164,E_167,F_165] : k2_xboole_0(k3_enumset1(A_166,B_164,C_163,D_168,E_167),k1_tarski(F_165)) = k4_enumset1(A_166,B_164,C_163,D_168,E_167,F_165) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_961,plain,(
    ! [B_43,A_42,D_45,F_165,C_44] : k4_enumset1(A_42,A_42,B_43,C_44,D_45,F_165) = k2_xboole_0(k2_enumset1(A_42,B_43,C_44,D_45),k1_tarski(F_165)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_952])).

tff(c_1017,plain,(
    ! [B_172,F_174,D_171,C_175,A_173] : k2_xboole_0(k2_enumset1(A_173,B_172,C_175,D_171),k1_tarski(F_174)) = k3_enumset1(A_173,B_172,C_175,D_171,F_174) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_961])).

tff(c_1026,plain,(
    ! [A_39,B_40,C_41,F_174] : k3_enumset1(A_39,A_39,B_40,C_41,F_174) = k2_xboole_0(k1_enumset1(A_39,B_40,C_41),k1_tarski(F_174)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1017])).

tff(c_1030,plain,(
    ! [A_176,B_177,C_178,F_179] : k2_xboole_0(k1_enumset1(A_176,B_177,C_178),k1_tarski(F_179)) = k2_enumset1(A_176,B_177,C_178,F_179) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1026])).

tff(c_1048,plain,(
    ! [A_37,B_38,F_179] : k2_xboole_0(k2_tarski(A_37,B_38),k1_tarski(F_179)) = k2_enumset1(A_37,A_37,B_38,F_179) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1030])).

tff(c_1052,plain,(
    ! [A_180,B_181,F_182] : k2_xboole_0(k2_tarski(A_180,B_181),k1_tarski(F_182)) = k1_enumset1(A_180,B_181,F_182) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1048])).

tff(c_16,plain,(
    ! [A_16] : k5_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    ! [A_17] : r1_xboole_0(A_17,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_177,plain,(
    ! [A_90,B_91,C_92] :
      ( ~ r1_xboole_0(A_90,B_91)
      | ~ r2_hidden(C_92,k3_xboole_0(A_90,B_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_218,plain,(
    ! [A_98,B_99] :
      ( ~ r1_xboole_0(A_98,B_99)
      | k3_xboole_0(A_98,B_99) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_177])).

tff(c_222,plain,(
    ! [A_17] : k3_xboole_0(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_218])).

tff(c_223,plain,(
    ! [A_100] : k3_xboole_0(A_100,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_218])).

tff(c_10,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_231,plain,(
    ! [A_100] : k5_xboole_0(A_100,k1_xboole_0) = k4_xboole_0(A_100,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_10])).

tff(c_245,plain,(
    ! [A_100] : k4_xboole_0(A_100,k1_xboole_0) = A_100 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_231])).

tff(c_310,plain,(
    ! [A_103,B_104] : k4_xboole_0(A_103,k4_xboole_0(A_103,B_104)) = k3_xboole_0(A_103,B_104) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_328,plain,(
    ! [A_100] : k4_xboole_0(A_100,A_100) = k3_xboole_0(A_100,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_310])).

tff(c_331,plain,(
    ! [A_100] : k4_xboole_0(A_100,A_100) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_328])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_135,plain,(
    ! [A_87,B_88] : k5_xboole_0(A_87,k3_xboole_0(A_87,B_88)) = k4_xboole_0(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_144,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_135])).

tff(c_68,plain,(
    r1_tarski(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_125,plain,(
    ! [A_83,B_84] :
      ( k3_xboole_0(A_83,B_84) = A_83
      | ~ r1_tarski(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_129,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_125])).

tff(c_167,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_10])).

tff(c_170,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_167])).

tff(c_515,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_170])).

tff(c_20,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_522,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) = k5_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_515,c_20])).

tff(c_526,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) = k2_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_522])).

tff(c_1058,plain,(
    k1_enumset1('#skF_6','#skF_7','#skF_5') = k2_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1052,c_526])).

tff(c_24,plain,(
    ! [E_26,A_20,B_21] : r2_hidden(E_26,k1_enumset1(A_20,B_21,E_26)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1089,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1058,c_24])).

tff(c_358,plain,(
    ! [C_106,B_107,A_108] : k1_enumset1(C_106,B_107,A_108) = k1_enumset1(A_108,B_107,C_106) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_374,plain,(
    ! [C_106,B_107] : k1_enumset1(C_106,B_107,B_107) = k2_tarski(B_107,C_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_358,c_52])).

tff(c_665,plain,(
    ! [E_128,C_129,B_130,A_131] :
      ( E_128 = C_129
      | E_128 = B_130
      | E_128 = A_131
      | ~ r2_hidden(E_128,k1_enumset1(A_131,B_130,C_129)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_672,plain,(
    ! [E_128,B_107,C_106] :
      ( E_128 = B_107
      | E_128 = B_107
      | E_128 = C_106
      | ~ r2_hidden(E_128,k2_tarski(B_107,C_106)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_374,c_665])).

tff(c_1107,plain,
    ( '#skF_5' = '#skF_6'
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1089,c_672])).

tff(c_1114,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_66,c_66,c_1107])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:14:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.99/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.57  
% 2.99/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.58  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 2.99/1.58  
% 2.99/1.58  %Foreground sorts:
% 2.99/1.58  
% 2.99/1.58  
% 2.99/1.58  %Background operators:
% 2.99/1.58  
% 2.99/1.58  
% 2.99/1.58  %Foreground operators:
% 2.99/1.58  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.99/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.99/1.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.99/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.99/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.99/1.58  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.99/1.58  tff('#skF_7', type, '#skF_7': $i).
% 2.99/1.58  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.99/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.99/1.58  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.99/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.99/1.58  tff('#skF_5', type, '#skF_5': $i).
% 2.99/1.58  tff('#skF_6', type, '#skF_6': $i).
% 2.99/1.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.99/1.58  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.99/1.58  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.99/1.58  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.99/1.58  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.99/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.99/1.58  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.99/1.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.99/1.58  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.99/1.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.99/1.58  
% 2.99/1.59  tff(f_106, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 2.99/1.59  tff(f_88, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.99/1.59  tff(f_86, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.99/1.59  tff(f_90, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.99/1.59  tff(f_92, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.99/1.59  tff(f_82, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 2.99/1.59  tff(f_59, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.99/1.59  tff(f_61, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.99/1.59  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.99/1.59  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.99/1.59  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.99/1.59  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.99/1.59  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.99/1.59  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.99/1.59  tff(f_63, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.99/1.59  tff(f_78, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.99/1.59  tff(f_80, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_enumset1)).
% 2.99/1.59  tff(c_64, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.99/1.59  tff(c_66, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.99/1.59  tff(c_54, plain, (![A_39, B_40, C_41]: (k2_enumset1(A_39, A_39, B_40, C_41)=k1_enumset1(A_39, B_40, C_41))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.99/1.59  tff(c_52, plain, (![A_37, B_38]: (k1_enumset1(A_37, A_37, B_38)=k2_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.99/1.59  tff(c_56, plain, (![A_42, B_43, C_44, D_45]: (k3_enumset1(A_42, A_42, B_43, C_44, D_45)=k2_enumset1(A_42, B_43, C_44, D_45))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.99/1.59  tff(c_58, plain, (![A_46, E_50, B_47, C_48, D_49]: (k4_enumset1(A_46, A_46, B_47, C_48, D_49, E_50)=k3_enumset1(A_46, B_47, C_48, D_49, E_50))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.99/1.59  tff(c_952, plain, (![C_163, D_168, A_166, B_164, E_167, F_165]: (k2_xboole_0(k3_enumset1(A_166, B_164, C_163, D_168, E_167), k1_tarski(F_165))=k4_enumset1(A_166, B_164, C_163, D_168, E_167, F_165))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.99/1.59  tff(c_961, plain, (![B_43, A_42, D_45, F_165, C_44]: (k4_enumset1(A_42, A_42, B_43, C_44, D_45, F_165)=k2_xboole_0(k2_enumset1(A_42, B_43, C_44, D_45), k1_tarski(F_165)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_952])).
% 2.99/1.59  tff(c_1017, plain, (![B_172, F_174, D_171, C_175, A_173]: (k2_xboole_0(k2_enumset1(A_173, B_172, C_175, D_171), k1_tarski(F_174))=k3_enumset1(A_173, B_172, C_175, D_171, F_174))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_961])).
% 2.99/1.59  tff(c_1026, plain, (![A_39, B_40, C_41, F_174]: (k3_enumset1(A_39, A_39, B_40, C_41, F_174)=k2_xboole_0(k1_enumset1(A_39, B_40, C_41), k1_tarski(F_174)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_1017])).
% 2.99/1.59  tff(c_1030, plain, (![A_176, B_177, C_178, F_179]: (k2_xboole_0(k1_enumset1(A_176, B_177, C_178), k1_tarski(F_179))=k2_enumset1(A_176, B_177, C_178, F_179))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1026])).
% 2.99/1.59  tff(c_1048, plain, (![A_37, B_38, F_179]: (k2_xboole_0(k2_tarski(A_37, B_38), k1_tarski(F_179))=k2_enumset1(A_37, A_37, B_38, F_179))), inference(superposition, [status(thm), theory('equality')], [c_52, c_1030])).
% 2.99/1.59  tff(c_1052, plain, (![A_180, B_181, F_182]: (k2_xboole_0(k2_tarski(A_180, B_181), k1_tarski(F_182))=k1_enumset1(A_180, B_181, F_182))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1048])).
% 2.99/1.59  tff(c_16, plain, (![A_16]: (k5_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.99/1.59  tff(c_18, plain, (![A_17]: (r1_xboole_0(A_17, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.99/1.59  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.99/1.59  tff(c_177, plain, (![A_90, B_91, C_92]: (~r1_xboole_0(A_90, B_91) | ~r2_hidden(C_92, k3_xboole_0(A_90, B_91)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.99/1.59  tff(c_218, plain, (![A_98, B_99]: (~r1_xboole_0(A_98, B_99) | k3_xboole_0(A_98, B_99)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_177])).
% 2.99/1.59  tff(c_222, plain, (![A_17]: (k3_xboole_0(A_17, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_218])).
% 2.99/1.59  tff(c_223, plain, (![A_100]: (k3_xboole_0(A_100, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_218])).
% 2.99/1.59  tff(c_10, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.99/1.59  tff(c_231, plain, (![A_100]: (k5_xboole_0(A_100, k1_xboole_0)=k4_xboole_0(A_100, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_223, c_10])).
% 2.99/1.59  tff(c_245, plain, (![A_100]: (k4_xboole_0(A_100, k1_xboole_0)=A_100)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_231])).
% 2.99/1.59  tff(c_310, plain, (![A_103, B_104]: (k4_xboole_0(A_103, k4_xboole_0(A_103, B_104))=k3_xboole_0(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.99/1.59  tff(c_328, plain, (![A_100]: (k4_xboole_0(A_100, A_100)=k3_xboole_0(A_100, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_245, c_310])).
% 2.99/1.59  tff(c_331, plain, (![A_100]: (k4_xboole_0(A_100, A_100)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_222, c_328])).
% 2.99/1.59  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.99/1.59  tff(c_135, plain, (![A_87, B_88]: (k5_xboole_0(A_87, k3_xboole_0(A_87, B_88))=k4_xboole_0(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.99/1.59  tff(c_144, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_135])).
% 2.99/1.59  tff(c_68, plain, (r1_tarski(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.99/1.59  tff(c_125, plain, (![A_83, B_84]: (k3_xboole_0(A_83, B_84)=A_83 | ~r1_tarski(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.99/1.59  tff(c_129, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_68, c_125])).
% 2.99/1.59  tff(c_167, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_129, c_10])).
% 2.99/1.59  tff(c_170, plain, (k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_167])).
% 2.99/1.59  tff(c_515, plain, (k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_331, c_170])).
% 2.99/1.59  tff(c_20, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.99/1.59  tff(c_522, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))=k5_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_515, c_20])).
% 2.99/1.59  tff(c_526, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))=k2_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_522])).
% 2.99/1.59  tff(c_1058, plain, (k1_enumset1('#skF_6', '#skF_7', '#skF_5')=k2_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1052, c_526])).
% 2.99/1.59  tff(c_24, plain, (![E_26, A_20, B_21]: (r2_hidden(E_26, k1_enumset1(A_20, B_21, E_26)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.99/1.59  tff(c_1089, plain, (r2_hidden('#skF_5', k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1058, c_24])).
% 2.99/1.59  tff(c_358, plain, (![C_106, B_107, A_108]: (k1_enumset1(C_106, B_107, A_108)=k1_enumset1(A_108, B_107, C_106))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.99/1.59  tff(c_374, plain, (![C_106, B_107]: (k1_enumset1(C_106, B_107, B_107)=k2_tarski(B_107, C_106))), inference(superposition, [status(thm), theory('equality')], [c_358, c_52])).
% 2.99/1.59  tff(c_665, plain, (![E_128, C_129, B_130, A_131]: (E_128=C_129 | E_128=B_130 | E_128=A_131 | ~r2_hidden(E_128, k1_enumset1(A_131, B_130, C_129)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.99/1.59  tff(c_672, plain, (![E_128, B_107, C_106]: (E_128=B_107 | E_128=B_107 | E_128=C_106 | ~r2_hidden(E_128, k2_tarski(B_107, C_106)))), inference(superposition, [status(thm), theory('equality')], [c_374, c_665])).
% 2.99/1.59  tff(c_1107, plain, ('#skF_5'='#skF_6' | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_1089, c_672])).
% 2.99/1.59  tff(c_1114, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_66, c_66, c_1107])).
% 2.99/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.59  
% 2.99/1.59  Inference rules
% 2.99/1.59  ----------------------
% 2.99/1.59  #Ref     : 0
% 2.99/1.59  #Sup     : 248
% 2.99/1.59  #Fact    : 0
% 2.99/1.59  #Define  : 0
% 2.99/1.59  #Split   : 1
% 2.99/1.59  #Chain   : 0
% 2.99/1.59  #Close   : 0
% 2.99/1.59  
% 2.99/1.59  Ordering : KBO
% 2.99/1.59  
% 2.99/1.59  Simplification rules
% 2.99/1.59  ----------------------
% 2.99/1.59  #Subsume      : 13
% 2.99/1.59  #Demod        : 135
% 2.99/1.59  #Tautology    : 172
% 2.99/1.59  #SimpNegUnit  : 4
% 2.99/1.59  #BackRed      : 2
% 2.99/1.59  
% 2.99/1.59  #Partial instantiations: 0
% 2.99/1.59  #Strategies tried      : 1
% 2.99/1.59  
% 2.99/1.59  Timing (in seconds)
% 2.99/1.59  ----------------------
% 2.99/1.59  Preprocessing        : 0.45
% 2.99/1.59  Parsing              : 0.27
% 2.99/1.60  CNF conversion       : 0.02
% 2.99/1.60  Main loop            : 0.37
% 2.99/1.60  Inferencing          : 0.13
% 2.99/1.60  Reduction            : 0.13
% 2.99/1.60  Demodulation         : 0.10
% 2.99/1.60  BG Simplification    : 0.02
% 2.99/1.60  Subsumption          : 0.06
% 2.99/1.60  Abstraction          : 0.02
% 2.99/1.60  MUC search           : 0.00
% 2.99/1.60  Cooper               : 0.00
% 2.99/1.60  Total                : 0.85
% 2.99/1.60  Index Insertion      : 0.00
% 2.99/1.60  Index Deletion       : 0.00
% 2.99/1.60  Index Matching       : 0.00
% 2.99/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
