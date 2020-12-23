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
% DateTime   : Thu Dec  3 09:57:22 EST 2020

% Result     : Theorem 5.52s
% Output     : CNFRefutation 5.52s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 185 expanded)
%              Number of leaves         :   34 (  76 expanded)
%              Depth                    :   17
%              Number of atoms          :   90 ( 291 expanded)
%              Number of equality atoms :   54 ( 134 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_80,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_82,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_53,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
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

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_98,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_76,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_96,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_101,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_52,plain,(
    ! [A_27] : k2_tarski(A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_100,plain,(
    ! [A_54,B_55] : k1_enumset1(A_54,A_54,B_55) = k2_tarski(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_26,plain,(
    ! [E_21,A_15,B_16] : r2_hidden(E_21,k1_enumset1(A_15,B_16,E_21)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_118,plain,(
    ! [B_56,A_57] : r2_hidden(B_56,k2_tarski(A_57,B_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_26])).

tff(c_121,plain,(
    ! [A_27] : r2_hidden(A_27,k1_tarski(A_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_118])).

tff(c_16,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_92,plain,(
    ! [A_42,B_43] : r1_tarski(k3_xboole_0(A_42,B_43),A_42) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_95,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_92])).

tff(c_165,plain,(
    ! [B_70,A_71] :
      ( B_70 = A_71
      | ~ r1_tarski(B_70,A_71)
      | ~ r1_tarski(A_71,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_178,plain,(
    ! [A_72] :
      ( k1_xboole_0 = A_72
      | ~ r1_tarski(A_72,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_95,c_165])).

tff(c_193,plain,(
    ! [B_9] : k3_xboole_0(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_178])).

tff(c_18,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_243,plain,(
    ! [A_77,B_78] : k4_xboole_0(A_77,k4_xboole_0(A_77,B_78)) = k3_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_333,plain,(
    ! [A_94,B_95] : k4_xboole_0(A_94,k3_xboole_0(A_94,B_95)) = k3_xboole_0(A_94,k4_xboole_0(A_94,B_95)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_243])).

tff(c_345,plain,(
    ! [B_9] : k3_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,B_9)) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_333])).

tff(c_351,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_345])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( r1_xboole_0(A_13,B_14)
      | k4_xboole_0(A_13,B_14) != A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_269,plain,(
    ! [A_84,B_85,C_86] :
      ( ~ r1_xboole_0(A_84,B_85)
      | ~ r2_hidden(C_86,B_85)
      | ~ r2_hidden(C_86,A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_477,plain,(
    ! [C_105,B_106,A_107] :
      ( ~ r2_hidden(C_105,B_106)
      | ~ r2_hidden(C_105,A_107)
      | k4_xboole_0(A_107,B_106) != A_107 ) ),
    inference(resolution,[status(thm)],[c_22,c_269])).

tff(c_4993,plain,(
    ! [A_9468,B_9469,A_9470] :
      ( ~ r2_hidden('#skF_1'(A_9468,B_9469),A_9470)
      | k4_xboole_0(A_9470,B_9469) != A_9470
      | r1_xboole_0(A_9468,B_9469) ) ),
    inference(resolution,[status(thm)],[c_4,c_477])).

tff(c_5047,plain,(
    ! [B_9555,A_9556] :
      ( k4_xboole_0(B_9555,B_9555) != B_9555
      | r1_xboole_0(A_9556,B_9555) ) ),
    inference(resolution,[status(thm)],[c_4,c_4993])).

tff(c_5062,plain,(
    ! [A_9641] : r1_xboole_0(A_9641,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_5047])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = A_13
      | ~ r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_5135,plain,(
    ! [A_9812] : k4_xboole_0(A_9812,k1_xboole_0) = A_9812 ),
    inference(resolution,[status(thm)],[c_5062,c_20])).

tff(c_5151,plain,(
    ! [A_9812] : k4_xboole_0(A_9812,A_9812) = k3_xboole_0(A_9812,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5135,c_18])).

tff(c_5223,plain,(
    ! [A_9982] : k4_xboole_0(A_9982,A_9982) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_5151])).

tff(c_497,plain,(
    ! [A_27,A_107] :
      ( ~ r2_hidden(A_27,A_107)
      | k4_xboole_0(A_107,k1_tarski(A_27)) != A_107 ) ),
    inference(resolution,[status(thm)],[c_121,c_477])).

tff(c_5264,plain,(
    ! [A_27] :
      ( ~ r2_hidden(A_27,k1_tarski(A_27))
      | k1_tarski(A_27) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5223,c_497])).

tff(c_5299,plain,(
    ! [A_27] : k1_tarski(A_27) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_5264])).

tff(c_62,plain,(
    ! [A_37] : k1_setfam_1(k1_tarski(A_37)) = A_37 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_48,plain,(
    ! [A_22,B_23] : k2_xboole_0(k1_tarski(A_22),k1_tarski(B_23)) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_452,plain,(
    ! [A_103,B_104] :
      ( k3_xboole_0(k1_setfam_1(A_103),k1_setfam_1(B_104)) = k1_setfam_1(k2_xboole_0(A_103,B_104))
      | k1_xboole_0 = B_104
      | k1_xboole_0 = A_103 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_473,plain,(
    ! [A_103,A_37] :
      ( k1_setfam_1(k2_xboole_0(A_103,k1_tarski(A_37))) = k3_xboole_0(k1_setfam_1(A_103),A_37)
      | k1_tarski(A_37) = k1_xboole_0
      | k1_xboole_0 = A_103 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_452])).

tff(c_5369,plain,(
    ! [A_10409,A_10410] :
      ( k1_setfam_1(k2_xboole_0(A_10409,k1_tarski(A_10410))) = k3_xboole_0(k1_setfam_1(A_10409),A_10410)
      | k1_xboole_0 = A_10409 ) ),
    inference(negUnitSimplification,[status(thm)],[c_5299,c_473])).

tff(c_5410,plain,(
    ! [A_22,B_23] :
      ( k3_xboole_0(k1_setfam_1(k1_tarski(A_22)),B_23) = k1_setfam_1(k2_tarski(A_22,B_23))
      | k1_tarski(A_22) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_5369])).

tff(c_5423,plain,(
    ! [A_22,B_23] :
      ( k1_setfam_1(k2_tarski(A_22,B_23)) = k3_xboole_0(A_22,B_23)
      | k1_tarski(A_22) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_5410])).

tff(c_5424,plain,(
    ! [A_22,B_23] : k1_setfam_1(k2_tarski(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(negUnitSimplification,[status(thm)],[c_5299,c_5423])).

tff(c_64,plain,(
    k1_setfam_1(k2_tarski('#skF_4','#skF_5')) != k3_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_5804,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5424,c_64])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:01:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.52/2.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.52/2.05  
% 5.52/2.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.52/2.06  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 5.52/2.06  
% 5.52/2.06  %Foreground sorts:
% 5.52/2.06  
% 5.52/2.06  
% 5.52/2.06  %Background operators:
% 5.52/2.06  
% 5.52/2.06  
% 5.52/2.06  %Foreground operators:
% 5.52/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.52/2.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.52/2.06  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.52/2.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.52/2.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.52/2.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.52/2.06  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.52/2.06  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.52/2.06  tff('#skF_5', type, '#skF_5': $i).
% 5.52/2.06  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 5.52/2.06  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.52/2.06  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.52/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.52/2.06  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.52/2.06  tff('#skF_4', type, '#skF_4': $i).
% 5.52/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.52/2.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.52/2.06  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.52/2.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.52/2.06  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.52/2.06  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.52/2.06  
% 5.52/2.07  tff(f_80, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.52/2.07  tff(f_82, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 5.52/2.07  tff(f_74, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 5.52/2.07  tff(f_53, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 5.52/2.07  tff(f_51, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.52/2.07  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.52/2.07  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.52/2.07  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.52/2.07  tff(f_59, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 5.52/2.07  tff(f_98, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 5.52/2.07  tff(f_76, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 5.52/2.07  tff(f_96, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_setfam_1)).
% 5.52/2.07  tff(f_101, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.52/2.07  tff(c_52, plain, (![A_27]: (k2_tarski(A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.52/2.07  tff(c_100, plain, (![A_54, B_55]: (k1_enumset1(A_54, A_54, B_55)=k2_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.52/2.07  tff(c_26, plain, (![E_21, A_15, B_16]: (r2_hidden(E_21, k1_enumset1(A_15, B_16, E_21)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.52/2.07  tff(c_118, plain, (![B_56, A_57]: (r2_hidden(B_56, k2_tarski(A_57, B_56)))), inference(superposition, [status(thm), theory('equality')], [c_100, c_26])).
% 5.52/2.07  tff(c_121, plain, (![A_27]: (r2_hidden(A_27, k1_tarski(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_118])).
% 5.52/2.07  tff(c_16, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.52/2.07  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.52/2.07  tff(c_92, plain, (![A_42, B_43]: (r1_tarski(k3_xboole_0(A_42, B_43), A_42))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.52/2.07  tff(c_95, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(superposition, [status(thm), theory('equality')], [c_16, c_92])).
% 5.52/2.07  tff(c_165, plain, (![B_70, A_71]: (B_70=A_71 | ~r1_tarski(B_70, A_71) | ~r1_tarski(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.52/2.07  tff(c_178, plain, (![A_72]: (k1_xboole_0=A_72 | ~r1_tarski(A_72, k1_xboole_0))), inference(resolution, [status(thm)], [c_95, c_165])).
% 5.52/2.07  tff(c_193, plain, (![B_9]: (k3_xboole_0(k1_xboole_0, B_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_178])).
% 5.52/2.07  tff(c_18, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.52/2.07  tff(c_243, plain, (![A_77, B_78]: (k4_xboole_0(A_77, k4_xboole_0(A_77, B_78))=k3_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.52/2.07  tff(c_333, plain, (![A_94, B_95]: (k4_xboole_0(A_94, k3_xboole_0(A_94, B_95))=k3_xboole_0(A_94, k4_xboole_0(A_94, B_95)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_243])).
% 5.52/2.07  tff(c_345, plain, (![B_9]: (k3_xboole_0(k1_xboole_0, k4_xboole_0(k1_xboole_0, B_9))=k4_xboole_0(k1_xboole_0, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_193, c_333])).
% 5.52/2.07  tff(c_351, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_193, c_345])).
% 5.52/2.07  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.52/2.07  tff(c_22, plain, (![A_13, B_14]: (r1_xboole_0(A_13, B_14) | k4_xboole_0(A_13, B_14)!=A_13)), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.52/2.07  tff(c_269, plain, (![A_84, B_85, C_86]: (~r1_xboole_0(A_84, B_85) | ~r2_hidden(C_86, B_85) | ~r2_hidden(C_86, A_84))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.52/2.07  tff(c_477, plain, (![C_105, B_106, A_107]: (~r2_hidden(C_105, B_106) | ~r2_hidden(C_105, A_107) | k4_xboole_0(A_107, B_106)!=A_107)), inference(resolution, [status(thm)], [c_22, c_269])).
% 5.52/2.07  tff(c_4993, plain, (![A_9468, B_9469, A_9470]: (~r2_hidden('#skF_1'(A_9468, B_9469), A_9470) | k4_xboole_0(A_9470, B_9469)!=A_9470 | r1_xboole_0(A_9468, B_9469))), inference(resolution, [status(thm)], [c_4, c_477])).
% 5.52/2.07  tff(c_5047, plain, (![B_9555, A_9556]: (k4_xboole_0(B_9555, B_9555)!=B_9555 | r1_xboole_0(A_9556, B_9555))), inference(resolution, [status(thm)], [c_4, c_4993])).
% 5.52/2.07  tff(c_5062, plain, (![A_9641]: (r1_xboole_0(A_9641, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_351, c_5047])).
% 5.52/2.07  tff(c_20, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=A_13 | ~r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.52/2.07  tff(c_5135, plain, (![A_9812]: (k4_xboole_0(A_9812, k1_xboole_0)=A_9812)), inference(resolution, [status(thm)], [c_5062, c_20])).
% 5.52/2.07  tff(c_5151, plain, (![A_9812]: (k4_xboole_0(A_9812, A_9812)=k3_xboole_0(A_9812, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_5135, c_18])).
% 5.52/2.07  tff(c_5223, plain, (![A_9982]: (k4_xboole_0(A_9982, A_9982)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_5151])).
% 5.52/2.07  tff(c_497, plain, (![A_27, A_107]: (~r2_hidden(A_27, A_107) | k4_xboole_0(A_107, k1_tarski(A_27))!=A_107)), inference(resolution, [status(thm)], [c_121, c_477])).
% 5.52/2.07  tff(c_5264, plain, (![A_27]: (~r2_hidden(A_27, k1_tarski(A_27)) | k1_tarski(A_27)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5223, c_497])).
% 5.52/2.07  tff(c_5299, plain, (![A_27]: (k1_tarski(A_27)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_121, c_5264])).
% 5.52/2.07  tff(c_62, plain, (![A_37]: (k1_setfam_1(k1_tarski(A_37))=A_37)), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.52/2.07  tff(c_48, plain, (![A_22, B_23]: (k2_xboole_0(k1_tarski(A_22), k1_tarski(B_23))=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.52/2.07  tff(c_452, plain, (![A_103, B_104]: (k3_xboole_0(k1_setfam_1(A_103), k1_setfam_1(B_104))=k1_setfam_1(k2_xboole_0(A_103, B_104)) | k1_xboole_0=B_104 | k1_xboole_0=A_103)), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.52/2.07  tff(c_473, plain, (![A_103, A_37]: (k1_setfam_1(k2_xboole_0(A_103, k1_tarski(A_37)))=k3_xboole_0(k1_setfam_1(A_103), A_37) | k1_tarski(A_37)=k1_xboole_0 | k1_xboole_0=A_103)), inference(superposition, [status(thm), theory('equality')], [c_62, c_452])).
% 5.52/2.07  tff(c_5369, plain, (![A_10409, A_10410]: (k1_setfam_1(k2_xboole_0(A_10409, k1_tarski(A_10410)))=k3_xboole_0(k1_setfam_1(A_10409), A_10410) | k1_xboole_0=A_10409)), inference(negUnitSimplification, [status(thm)], [c_5299, c_473])).
% 5.52/2.07  tff(c_5410, plain, (![A_22, B_23]: (k3_xboole_0(k1_setfam_1(k1_tarski(A_22)), B_23)=k1_setfam_1(k2_tarski(A_22, B_23)) | k1_tarski(A_22)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_48, c_5369])).
% 5.52/2.07  tff(c_5423, plain, (![A_22, B_23]: (k1_setfam_1(k2_tarski(A_22, B_23))=k3_xboole_0(A_22, B_23) | k1_tarski(A_22)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_5410])).
% 5.52/2.07  tff(c_5424, plain, (![A_22, B_23]: (k1_setfam_1(k2_tarski(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(negUnitSimplification, [status(thm)], [c_5299, c_5423])).
% 5.52/2.07  tff(c_64, plain, (k1_setfam_1(k2_tarski('#skF_4', '#skF_5'))!=k3_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.52/2.07  tff(c_5804, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5424, c_64])).
% 5.52/2.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.52/2.07  
% 5.52/2.07  Inference rules
% 5.52/2.07  ----------------------
% 5.52/2.07  #Ref     : 0
% 5.52/2.07  #Sup     : 806
% 5.52/2.07  #Fact    : 24
% 5.52/2.07  #Define  : 0
% 5.52/2.07  #Split   : 1
% 5.52/2.07  #Chain   : 0
% 5.52/2.07  #Close   : 0
% 5.52/2.07  
% 5.52/2.07  Ordering : KBO
% 5.52/2.07  
% 5.52/2.07  Simplification rules
% 5.52/2.07  ----------------------
% 5.52/2.07  #Subsume      : 144
% 5.52/2.07  #Demod        : 198
% 5.52/2.07  #Tautology    : 258
% 5.52/2.07  #SimpNegUnit  : 25
% 5.52/2.07  #BackRed      : 9
% 5.52/2.07  
% 5.52/2.07  #Partial instantiations: 5700
% 5.52/2.07  #Strategies tried      : 1
% 5.52/2.07  
% 5.52/2.07  Timing (in seconds)
% 5.52/2.07  ----------------------
% 5.52/2.07  Preprocessing        : 0.32
% 5.52/2.07  Parsing              : 0.16
% 5.52/2.07  CNF conversion       : 0.03
% 5.52/2.07  Main loop            : 0.99
% 5.52/2.07  Inferencing          : 0.55
% 5.52/2.07  Reduction            : 0.22
% 5.52/2.07  Demodulation         : 0.16
% 5.52/2.07  BG Simplification    : 0.04
% 5.52/2.07  Subsumption          : 0.13
% 5.52/2.07  Abstraction          : 0.05
% 5.52/2.07  MUC search           : 0.00
% 5.52/2.07  Cooper               : 0.00
% 5.52/2.07  Total                : 1.35
% 5.52/2.07  Index Insertion      : 0.00
% 5.52/2.07  Index Deletion       : 0.00
% 5.52/2.07  Index Matching       : 0.00
% 5.52/2.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
