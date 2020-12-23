%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:39 EST 2020

% Result     : Theorem 3.43s
% Output     : CNFRefutation 3.43s
% Verified   : 
% Statistics : Number of formulae       :   61 (  72 expanded)
%              Number of leaves         :   35 (  40 expanded)
%              Depth                    :    7
%              Number of atoms          :   56 (  78 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_73,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_75,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_52,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_78,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_62,plain,(
    ! [A_29] : k2_tarski(A_29,A_29) = k1_tarski(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_200,plain,(
    ! [A_84,B_85] : k1_enumset1(A_84,A_84,B_85) = k2_tarski(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_40,plain,(
    ! [E_28,A_22,B_23] : r2_hidden(E_28,k1_enumset1(A_22,B_23,E_28)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_218,plain,(
    ! [B_86,A_87] : r2_hidden(B_86,k2_tarski(A_87,B_86)) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_40])).

tff(c_221,plain,(
    ! [A_29] : r2_hidden(A_29,k1_tarski(A_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_218])).

tff(c_32,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_292,plain,(
    ! [A_111,B_112] : k5_xboole_0(k5_xboole_0(A_111,B_112),k3_xboole_0(A_111,B_112)) = k2_xboole_0(A_111,B_112) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_922,plain,(
    ! [B_139,A_140] : k5_xboole_0(k5_xboole_0(B_139,A_140),k3_xboole_0(A_140,B_139)) = k2_xboole_0(A_140,B_139) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_292])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_313,plain,(
    ! [A_1,B_2] : k5_xboole_0(k5_xboole_0(A_1,B_2),k3_xboole_0(B_2,A_1)) = k2_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_292])).

tff(c_934,plain,(
    ! [B_139,A_140] : k2_xboole_0(B_139,A_140) = k2_xboole_0(A_140,B_139) ),
    inference(superposition,[status(thm),theory(equality)],[c_922,c_313])).

tff(c_80,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_237,plain,(
    ! [A_97,B_98] :
      ( r2_xboole_0(A_97,B_98)
      | B_98 = A_97
      | ~ r1_tarski(A_97,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_30,plain,(
    ! [B_14,A_13] :
      ( ~ r2_xboole_0(B_14,A_13)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_252,plain,(
    ! [B_99,A_100] :
      ( ~ r1_tarski(B_99,A_100)
      | B_99 = A_100
      | ~ r1_tarski(A_100,B_99) ) ),
    inference(resolution,[status(thm)],[c_237,c_30])).

tff(c_260,plain,
    ( k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') = '#skF_6'
    | ~ r1_tarski('#skF_6',k2_xboole_0(k1_tarski('#skF_5'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_80,c_252])).

tff(c_283,plain,(
    ~ r1_tarski('#skF_6',k2_xboole_0(k1_tarski('#skF_5'),'#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_260])).

tff(c_1045,plain,(
    ~ r1_tarski('#skF_6',k2_xboole_0('#skF_6',k1_tarski('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_934,c_283])).

tff(c_1049,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1045])).

tff(c_1050,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_10,plain,(
    ! [D_10,A_5,B_6] :
      ( ~ r2_hidden(D_10,A_5)
      | r2_hidden(D_10,k2_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1081,plain,(
    ! [D_141] :
      ( ~ r2_hidden(D_141,k1_tarski('#skF_5'))
      | r2_hidden(D_141,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1050,c_10])).

tff(c_1085,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_221,c_1081])).

tff(c_1089,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1085])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:30:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.43/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.57  
% 3.43/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.58  %$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 3.43/1.58  
% 3.43/1.58  %Foreground sorts:
% 3.43/1.58  
% 3.43/1.58  
% 3.43/1.58  %Background operators:
% 3.43/1.58  
% 3.43/1.58  
% 3.43/1.58  %Foreground operators:
% 3.43/1.58  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.43/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.43/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.43/1.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.43/1.58  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.43/1.58  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.43/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.43/1.58  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.43/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.43/1.58  tff('#skF_5', type, '#skF_5': $i).
% 3.43/1.58  tff('#skF_6', type, '#skF_6': $i).
% 3.43/1.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.43/1.58  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.43/1.58  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.43/1.58  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.43/1.58  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.43/1.58  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.43/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.43/1.58  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.43/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.43/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.43/1.58  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.43/1.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.43/1.58  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.43/1.58  
% 3.43/1.59  tff(f_92, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 3.43/1.59  tff(f_73, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.43/1.59  tff(f_75, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.43/1.59  tff(f_71, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.43/1.59  tff(f_52, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.43/1.59  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.43/1.59  tff(f_56, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 3.43/1.59  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.43/1.59  tff(f_45, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.43/1.59  tff(f_50, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_xboole_1)).
% 3.43/1.59  tff(f_38, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.43/1.59  tff(c_78, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.43/1.59  tff(c_62, plain, (![A_29]: (k2_tarski(A_29, A_29)=k1_tarski(A_29))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.43/1.59  tff(c_200, plain, (![A_84, B_85]: (k1_enumset1(A_84, A_84, B_85)=k2_tarski(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.43/1.59  tff(c_40, plain, (![E_28, A_22, B_23]: (r2_hidden(E_28, k1_enumset1(A_22, B_23, E_28)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.43/1.59  tff(c_218, plain, (![B_86, A_87]: (r2_hidden(B_86, k2_tarski(A_87, B_86)))), inference(superposition, [status(thm), theory('equality')], [c_200, c_40])).
% 3.43/1.59  tff(c_221, plain, (![A_29]: (r2_hidden(A_29, k1_tarski(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_218])).
% 3.43/1.59  tff(c_32, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.43/1.59  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.43/1.59  tff(c_292, plain, (![A_111, B_112]: (k5_xboole_0(k5_xboole_0(A_111, B_112), k3_xboole_0(A_111, B_112))=k2_xboole_0(A_111, B_112))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.43/1.59  tff(c_922, plain, (![B_139, A_140]: (k5_xboole_0(k5_xboole_0(B_139, A_140), k3_xboole_0(A_140, B_139))=k2_xboole_0(A_140, B_139))), inference(superposition, [status(thm), theory('equality')], [c_4, c_292])).
% 3.43/1.59  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.43/1.59  tff(c_313, plain, (![A_1, B_2]: (k5_xboole_0(k5_xboole_0(A_1, B_2), k3_xboole_0(B_2, A_1))=k2_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_292])).
% 3.43/1.59  tff(c_934, plain, (![B_139, A_140]: (k2_xboole_0(B_139, A_140)=k2_xboole_0(A_140, B_139))), inference(superposition, [status(thm), theory('equality')], [c_922, c_313])).
% 3.43/1.59  tff(c_80, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.43/1.59  tff(c_237, plain, (![A_97, B_98]: (r2_xboole_0(A_97, B_98) | B_98=A_97 | ~r1_tarski(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.43/1.59  tff(c_30, plain, (![B_14, A_13]: (~r2_xboole_0(B_14, A_13) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.43/1.59  tff(c_252, plain, (![B_99, A_100]: (~r1_tarski(B_99, A_100) | B_99=A_100 | ~r1_tarski(A_100, B_99))), inference(resolution, [status(thm)], [c_237, c_30])).
% 3.43/1.59  tff(c_260, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')='#skF_6' | ~r1_tarski('#skF_6', k2_xboole_0(k1_tarski('#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_80, c_252])).
% 3.43/1.59  tff(c_283, plain, (~r1_tarski('#skF_6', k2_xboole_0(k1_tarski('#skF_5'), '#skF_6'))), inference(splitLeft, [status(thm)], [c_260])).
% 3.43/1.59  tff(c_1045, plain, (~r1_tarski('#skF_6', k2_xboole_0('#skF_6', k1_tarski('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_934, c_283])).
% 3.43/1.59  tff(c_1049, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_1045])).
% 3.43/1.59  tff(c_1050, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_260])).
% 3.43/1.59  tff(c_10, plain, (![D_10, A_5, B_6]: (~r2_hidden(D_10, A_5) | r2_hidden(D_10, k2_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.43/1.59  tff(c_1081, plain, (![D_141]: (~r2_hidden(D_141, k1_tarski('#skF_5')) | r2_hidden(D_141, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1050, c_10])).
% 3.43/1.59  tff(c_1085, plain, (r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_221, c_1081])).
% 3.43/1.59  tff(c_1089, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_1085])).
% 3.43/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.59  
% 3.43/1.59  Inference rules
% 3.43/1.59  ----------------------
% 3.43/1.59  #Ref     : 0
% 3.43/1.59  #Sup     : 265
% 3.43/1.59  #Fact    : 0
% 3.43/1.59  #Define  : 0
% 3.43/1.59  #Split   : 2
% 3.43/1.59  #Chain   : 0
% 3.43/1.59  #Close   : 0
% 3.43/1.59  
% 3.43/1.59  Ordering : KBO
% 3.43/1.59  
% 3.43/1.59  Simplification rules
% 3.43/1.59  ----------------------
% 3.43/1.59  #Subsume      : 9
% 3.43/1.59  #Demod        : 86
% 3.43/1.59  #Tautology    : 84
% 3.43/1.59  #SimpNegUnit  : 1
% 3.43/1.59  #BackRed      : 3
% 3.43/1.59  
% 3.43/1.59  #Partial instantiations: 0
% 3.43/1.59  #Strategies tried      : 1
% 3.43/1.59  
% 3.43/1.59  Timing (in seconds)
% 3.43/1.59  ----------------------
% 3.43/1.59  Preprocessing        : 0.36
% 3.43/1.59  Parsing              : 0.18
% 3.43/1.59  CNF conversion       : 0.03
% 3.43/1.59  Main loop            : 0.45
% 3.43/1.59  Inferencing          : 0.13
% 3.43/1.59  Reduction            : 0.19
% 3.43/1.59  Demodulation         : 0.16
% 3.43/1.59  BG Simplification    : 0.03
% 3.43/1.59  Subsumption          : 0.07
% 3.43/1.59  Abstraction          : 0.03
% 3.43/1.59  MUC search           : 0.00
% 3.43/1.59  Cooper               : 0.00
% 3.43/1.59  Total                : 0.83
% 3.43/1.59  Index Insertion      : 0.00
% 3.43/1.59  Index Deletion       : 0.00
% 3.43/1.59  Index Matching       : 0.00
% 3.43/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
