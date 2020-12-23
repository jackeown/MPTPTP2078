%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:07 EST 2020

% Result     : Theorem 9.33s
% Output     : CNFRefutation 9.33s
% Verified   : 
% Statistics : Number of formulae       :   51 (  60 expanded)
%              Number of leaves         :   28 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   53 (  66 expanded)
%              Number of equality atoms :   29 (  39 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_40,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
        | k4_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

tff(c_20,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_196,plain,(
    ! [B_69,A_70] :
      ( k3_xboole_0(B_69,k1_tarski(A_70)) = k1_tarski(A_70)
      | ~ r2_hidden(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_133,plain,(
    ! [A_57,B_58] : k5_xboole_0(A_57,k3_xboole_0(A_57,B_58)) = k4_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_142,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_133])).

tff(c_202,plain,(
    ! [A_70,B_69] :
      ( k5_xboole_0(k1_tarski(A_70),k1_tarski(A_70)) = k4_xboole_0(k1_tarski(A_70),B_69)
      | ~ r2_hidden(A_70,B_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_142])).

tff(c_226,plain,(
    ! [A_71,B_72] :
      ( k4_xboole_0(k1_tarski(A_71),B_72) = k1_xboole_0
      | ~ r2_hidden(A_71,B_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_202])).

tff(c_62,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_240,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_62])).

tff(c_115,plain,(
    ! [A_55,B_56] : k1_enumset1(A_55,A_55,B_56) = k2_tarski(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_26,plain,(
    ! [E_18,A_12,C_14] : r2_hidden(E_18,k1_enumset1(A_12,E_18,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_124,plain,(
    ! [A_55,B_56] : r2_hidden(A_55,k2_tarski(A_55,B_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_26])).

tff(c_14,plain,(
    ! [A_3,C_5,B_4] :
      ( r2_hidden(A_3,C_5)
      | ~ r2_hidden(A_3,B_4)
      | r2_hidden(A_3,k5_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_58,plain,(
    ! [B_41,A_40] :
      ( k3_xboole_0(B_41,k1_tarski(A_40)) = k1_tarski(A_40)
      | ~ r2_hidden(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_384,plain,(
    ! [A_96,B_97,C_98] : k5_xboole_0(k3_xboole_0(A_96,B_97),k3_xboole_0(C_98,B_97)) = k3_xboole_0(k5_xboole_0(A_96,C_98),B_97) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_419,plain,(
    ! [A_40,C_98,B_41] :
      ( k5_xboole_0(k1_tarski(A_40),k3_xboole_0(C_98,k1_tarski(A_40))) = k3_xboole_0(k5_xboole_0(B_41,C_98),k1_tarski(A_40))
      | ~ r2_hidden(A_40,B_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_384])).

tff(c_5245,plain,(
    ! [B_252,C_253,A_254] :
      ( k3_xboole_0(k5_xboole_0(B_252,C_253),k1_tarski(A_254)) = k4_xboole_0(k1_tarski(A_254),C_253)
      | ~ r2_hidden(A_254,B_252) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_419])).

tff(c_11903,plain,(
    ! [A_413,C_414,B_415] :
      ( k4_xboole_0(k1_tarski(A_413),C_414) = k1_tarski(A_413)
      | ~ r2_hidden(A_413,k5_xboole_0(B_415,C_414))
      | ~ r2_hidden(A_413,B_415) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5245,c_58])).

tff(c_11986,plain,(
    ! [A_416,C_417,B_418] :
      ( k4_xboole_0(k1_tarski(A_416),C_417) = k1_tarski(A_416)
      | r2_hidden(A_416,C_417)
      | ~ r2_hidden(A_416,B_418) ) ),
    inference(resolution,[status(thm)],[c_14,c_11903])).

tff(c_12065,plain,(
    ! [A_419,C_420] :
      ( k4_xboole_0(k1_tarski(A_419),C_420) = k1_tarski(A_419)
      | r2_hidden(A_419,C_420) ) ),
    inference(resolution,[status(thm)],[c_124,c_11986])).

tff(c_60,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_12181,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12065,c_60])).

tff(c_12222,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_12181])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:40:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.33/3.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.33/3.56  
% 9.33/3.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.33/3.56  %$ r2_hidden > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 9.33/3.56  
% 9.33/3.56  %Foreground sorts:
% 9.33/3.56  
% 9.33/3.56  
% 9.33/3.56  %Background operators:
% 9.33/3.56  
% 9.33/3.56  
% 9.33/3.56  %Foreground operators:
% 9.33/3.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.33/3.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.33/3.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.33/3.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.33/3.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.33/3.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.33/3.56  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.33/3.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.33/3.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.33/3.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 9.33/3.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.33/3.56  tff('#skF_3', type, '#skF_3': $i).
% 9.33/3.56  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.33/3.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.33/3.56  tff('#skF_4', type, '#skF_4': $i).
% 9.33/3.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.33/3.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.33/3.56  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.33/3.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 9.33/3.56  
% 9.33/3.57  tff(f_40, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 9.33/3.57  tff(f_71, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 9.33/3.57  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.33/3.57  tff(f_36, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.33/3.57  tff(f_76, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) | (k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 9.33/3.57  tff(f_59, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 9.33/3.57  tff(f_55, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 9.33/3.57  tff(f_34, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 9.33/3.57  tff(f_38, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_xboole_1)).
% 9.33/3.57  tff(c_20, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.33/3.57  tff(c_196, plain, (![B_69, A_70]: (k3_xboole_0(B_69, k1_tarski(A_70))=k1_tarski(A_70) | ~r2_hidden(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.33/3.57  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.33/3.57  tff(c_133, plain, (![A_57, B_58]: (k5_xboole_0(A_57, k3_xboole_0(A_57, B_58))=k4_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.33/3.57  tff(c_142, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_133])).
% 9.33/3.57  tff(c_202, plain, (![A_70, B_69]: (k5_xboole_0(k1_tarski(A_70), k1_tarski(A_70))=k4_xboole_0(k1_tarski(A_70), B_69) | ~r2_hidden(A_70, B_69))), inference(superposition, [status(thm), theory('equality')], [c_196, c_142])).
% 9.33/3.57  tff(c_226, plain, (![A_71, B_72]: (k4_xboole_0(k1_tarski(A_71), B_72)=k1_xboole_0 | ~r2_hidden(A_71, B_72))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_202])).
% 9.33/3.57  tff(c_62, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.33/3.57  tff(c_240, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_226, c_62])).
% 9.33/3.57  tff(c_115, plain, (![A_55, B_56]: (k1_enumset1(A_55, A_55, B_56)=k2_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.33/3.57  tff(c_26, plain, (![E_18, A_12, C_14]: (r2_hidden(E_18, k1_enumset1(A_12, E_18, C_14)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.33/3.57  tff(c_124, plain, (![A_55, B_56]: (r2_hidden(A_55, k2_tarski(A_55, B_56)))), inference(superposition, [status(thm), theory('equality')], [c_115, c_26])).
% 9.33/3.57  tff(c_14, plain, (![A_3, C_5, B_4]: (r2_hidden(A_3, C_5) | ~r2_hidden(A_3, B_4) | r2_hidden(A_3, k5_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.33/3.57  tff(c_58, plain, (![B_41, A_40]: (k3_xboole_0(B_41, k1_tarski(A_40))=k1_tarski(A_40) | ~r2_hidden(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.33/3.57  tff(c_384, plain, (![A_96, B_97, C_98]: (k5_xboole_0(k3_xboole_0(A_96, B_97), k3_xboole_0(C_98, B_97))=k3_xboole_0(k5_xboole_0(A_96, C_98), B_97))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.33/3.57  tff(c_419, plain, (![A_40, C_98, B_41]: (k5_xboole_0(k1_tarski(A_40), k3_xboole_0(C_98, k1_tarski(A_40)))=k3_xboole_0(k5_xboole_0(B_41, C_98), k1_tarski(A_40)) | ~r2_hidden(A_40, B_41))), inference(superposition, [status(thm), theory('equality')], [c_58, c_384])).
% 9.33/3.57  tff(c_5245, plain, (![B_252, C_253, A_254]: (k3_xboole_0(k5_xboole_0(B_252, C_253), k1_tarski(A_254))=k4_xboole_0(k1_tarski(A_254), C_253) | ~r2_hidden(A_254, B_252))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_419])).
% 9.33/3.57  tff(c_11903, plain, (![A_413, C_414, B_415]: (k4_xboole_0(k1_tarski(A_413), C_414)=k1_tarski(A_413) | ~r2_hidden(A_413, k5_xboole_0(B_415, C_414)) | ~r2_hidden(A_413, B_415))), inference(superposition, [status(thm), theory('equality')], [c_5245, c_58])).
% 9.33/3.57  tff(c_11986, plain, (![A_416, C_417, B_418]: (k4_xboole_0(k1_tarski(A_416), C_417)=k1_tarski(A_416) | r2_hidden(A_416, C_417) | ~r2_hidden(A_416, B_418))), inference(resolution, [status(thm)], [c_14, c_11903])).
% 9.33/3.57  tff(c_12065, plain, (![A_419, C_420]: (k4_xboole_0(k1_tarski(A_419), C_420)=k1_tarski(A_419) | r2_hidden(A_419, C_420))), inference(resolution, [status(thm)], [c_124, c_11986])).
% 9.33/3.57  tff(c_60, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.33/3.57  tff(c_12181, plain, (r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12065, c_60])).
% 9.33/3.57  tff(c_12222, plain, $false, inference(negUnitSimplification, [status(thm)], [c_240, c_12181])).
% 9.33/3.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.33/3.57  
% 9.33/3.57  Inference rules
% 9.33/3.57  ----------------------
% 9.33/3.57  #Ref     : 0
% 9.33/3.57  #Sup     : 2999
% 9.33/3.57  #Fact    : 2
% 9.33/3.57  #Define  : 0
% 9.33/3.57  #Split   : 0
% 9.33/3.57  #Chain   : 0
% 9.33/3.57  #Close   : 0
% 9.33/3.57  
% 9.33/3.57  Ordering : KBO
% 9.33/3.57  
% 9.33/3.57  Simplification rules
% 9.33/3.57  ----------------------
% 9.33/3.57  #Subsume      : 746
% 9.33/3.57  #Demod        : 2669
% 9.33/3.57  #Tautology    : 612
% 9.33/3.57  #SimpNegUnit  : 216
% 9.33/3.57  #BackRed      : 6
% 9.33/3.57  
% 9.33/3.57  #Partial instantiations: 0
% 9.33/3.57  #Strategies tried      : 1
% 9.33/3.57  
% 9.33/3.57  Timing (in seconds)
% 9.33/3.57  ----------------------
% 9.33/3.57  Preprocessing        : 0.34
% 9.33/3.57  Parsing              : 0.18
% 9.33/3.57  CNF conversion       : 0.02
% 9.33/3.58  Main loop            : 2.48
% 9.33/3.58  Inferencing          : 0.59
% 9.33/3.58  Reduction            : 1.14
% 9.33/3.58  Demodulation         : 0.96
% 9.33/3.58  BG Simplification    : 0.10
% 9.33/3.58  Subsumption          : 0.53
% 9.33/3.58  Abstraction          : 0.13
% 9.33/3.58  MUC search           : 0.00
% 9.33/3.58  Cooper               : 0.00
% 9.33/3.58  Total                : 2.84
% 9.33/3.58  Index Insertion      : 0.00
% 9.33/3.58  Index Deletion       : 0.00
% 9.33/3.58  Index Matching       : 0.00
% 9.33/3.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
