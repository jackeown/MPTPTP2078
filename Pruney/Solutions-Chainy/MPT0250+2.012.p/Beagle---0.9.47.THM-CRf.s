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
% DateTime   : Thu Dec  3 09:50:33 EST 2020

% Result     : Theorem 5.62s
% Output     : CNFRefutation 5.62s
% Verified   : 
% Statistics : Number of formulae       :   52 (  61 expanded)
%              Number of leaves         :   28 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   48 (  64 expanded)
%              Number of equality atoms :   15 (  24 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_75,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

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

tff(f_73,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_58,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_14,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_109,plain,(
    ! [A_64,B_65] : k3_tarski(k2_tarski(A_64,B_65)) = k2_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_209,plain,(
    ! [A_78,B_79] : k3_tarski(k2_tarski(A_78,B_79)) = k2_xboole_0(B_79,A_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_109])).

tff(c_56,plain,(
    ! [A_47,B_48] : k3_tarski(k2_tarski(A_47,B_48)) = k2_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_215,plain,(
    ! [B_79,A_78] : k2_xboole_0(B_79,A_78) = k2_xboole_0(A_78,B_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_56])).

tff(c_60,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_4'),'#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_238,plain,(
    r1_tarski(k2_xboole_0('#skF_5',k1_tarski('#skF_4')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_60])).

tff(c_150,plain,(
    ! [A_67,B_68] : k1_enumset1(A_67,A_67,B_68) = k2_tarski(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    ! [E_16,A_10,B_11] : r2_hidden(E_16,k1_enumset1(A_10,B_11,E_16)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_156,plain,(
    ! [B_68,A_67] : r2_hidden(B_68,k2_tarski(A_67,B_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_18])).

tff(c_54,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(A_45,k3_tarski(B_46))
      | ~ r2_hidden(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_40,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_168,plain,(
    ! [B_69,A_70] : r2_hidden(B_69,k2_tarski(A_70,B_69)) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_18])).

tff(c_177,plain,(
    ! [A_17] : r2_hidden(A_17,k1_tarski(A_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_168])).

tff(c_283,plain,(
    ! [C_84,B_85,A_86] :
      ( r2_hidden(C_84,B_85)
      | ~ r2_hidden(C_84,A_86)
      | ~ r1_tarski(A_86,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_305,plain,(
    ! [A_87,B_88] :
      ( r2_hidden(A_87,B_88)
      | ~ r1_tarski(k1_tarski(A_87),B_88) ) ),
    inference(resolution,[status(thm)],[c_177,c_283])).

tff(c_361,plain,(
    ! [A_95,B_96] :
      ( r2_hidden(A_95,k3_tarski(B_96))
      | ~ r2_hidden(k1_tarski(A_95),B_96) ) ),
    inference(resolution,[status(thm)],[c_54,c_305])).

tff(c_373,plain,(
    ! [A_95,A_67] : r2_hidden(A_95,k3_tarski(k2_tarski(A_67,k1_tarski(A_95)))) ),
    inference(resolution,[status(thm)],[c_156,c_361])).

tff(c_424,plain,(
    ! [A_102,A_103] : r2_hidden(A_102,k2_xboole_0(A_103,k1_tarski(A_102))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_373])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5794,plain,(
    ! [A_12530,B_12531,A_12532] :
      ( r2_hidden(A_12530,B_12531)
      | ~ r1_tarski(k2_xboole_0(A_12532,k1_tarski(A_12530)),B_12531) ) ),
    inference(resolution,[status(thm)],[c_424,c_2])).

tff(c_5811,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_238,c_5794])).

tff(c_5838,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_5811])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:41:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.62/2.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.62/2.18  
% 5.62/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.62/2.19  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 5.62/2.19  
% 5.62/2.19  %Foreground sorts:
% 5.62/2.19  
% 5.62/2.19  
% 5.62/2.19  %Background operators:
% 5.62/2.19  
% 5.62/2.19  
% 5.62/2.19  %Foreground operators:
% 5.62/2.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.62/2.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.62/2.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.62/2.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.62/2.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.62/2.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.62/2.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.62/2.19  tff('#skF_5', type, '#skF_5': $i).
% 5.62/2.19  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 5.62/2.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.62/2.19  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.62/2.19  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.62/2.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.62/2.19  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.62/2.19  tff('#skF_4', type, '#skF_4': $i).
% 5.62/2.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.62/2.19  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.62/2.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.62/2.19  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.62/2.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.62/2.19  
% 5.62/2.20  tff(f_80, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 5.62/2.20  tff(f_40, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.62/2.20  tff(f_75, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.62/2.20  tff(f_59, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 5.62/2.20  tff(f_55, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 5.62/2.20  tff(f_73, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 5.62/2.20  tff(f_57, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.62/2.20  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.62/2.20  tff(c_58, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.62/2.20  tff(c_14, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.62/2.20  tff(c_109, plain, (![A_64, B_65]: (k3_tarski(k2_tarski(A_64, B_65))=k2_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.62/2.20  tff(c_209, plain, (![A_78, B_79]: (k3_tarski(k2_tarski(A_78, B_79))=k2_xboole_0(B_79, A_78))), inference(superposition, [status(thm), theory('equality')], [c_14, c_109])).
% 5.62/2.20  tff(c_56, plain, (![A_47, B_48]: (k3_tarski(k2_tarski(A_47, B_48))=k2_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.62/2.20  tff(c_215, plain, (![B_79, A_78]: (k2_xboole_0(B_79, A_78)=k2_xboole_0(A_78, B_79))), inference(superposition, [status(thm), theory('equality')], [c_209, c_56])).
% 5.62/2.20  tff(c_60, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_4'), '#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.62/2.20  tff(c_238, plain, (r1_tarski(k2_xboole_0('#skF_5', k1_tarski('#skF_4')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_215, c_60])).
% 5.62/2.20  tff(c_150, plain, (![A_67, B_68]: (k1_enumset1(A_67, A_67, B_68)=k2_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.62/2.20  tff(c_18, plain, (![E_16, A_10, B_11]: (r2_hidden(E_16, k1_enumset1(A_10, B_11, E_16)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.62/2.20  tff(c_156, plain, (![B_68, A_67]: (r2_hidden(B_68, k2_tarski(A_67, B_68)))), inference(superposition, [status(thm), theory('equality')], [c_150, c_18])).
% 5.62/2.20  tff(c_54, plain, (![A_45, B_46]: (r1_tarski(A_45, k3_tarski(B_46)) | ~r2_hidden(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.62/2.20  tff(c_40, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.62/2.20  tff(c_168, plain, (![B_69, A_70]: (r2_hidden(B_69, k2_tarski(A_70, B_69)))), inference(superposition, [status(thm), theory('equality')], [c_150, c_18])).
% 5.62/2.20  tff(c_177, plain, (![A_17]: (r2_hidden(A_17, k1_tarski(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_168])).
% 5.62/2.20  tff(c_283, plain, (![C_84, B_85, A_86]: (r2_hidden(C_84, B_85) | ~r2_hidden(C_84, A_86) | ~r1_tarski(A_86, B_85))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.62/2.20  tff(c_305, plain, (![A_87, B_88]: (r2_hidden(A_87, B_88) | ~r1_tarski(k1_tarski(A_87), B_88))), inference(resolution, [status(thm)], [c_177, c_283])).
% 5.62/2.20  tff(c_361, plain, (![A_95, B_96]: (r2_hidden(A_95, k3_tarski(B_96)) | ~r2_hidden(k1_tarski(A_95), B_96))), inference(resolution, [status(thm)], [c_54, c_305])).
% 5.62/2.20  tff(c_373, plain, (![A_95, A_67]: (r2_hidden(A_95, k3_tarski(k2_tarski(A_67, k1_tarski(A_95)))))), inference(resolution, [status(thm)], [c_156, c_361])).
% 5.62/2.20  tff(c_424, plain, (![A_102, A_103]: (r2_hidden(A_102, k2_xboole_0(A_103, k1_tarski(A_102))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_373])).
% 5.62/2.20  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.62/2.20  tff(c_5794, plain, (![A_12530, B_12531, A_12532]: (r2_hidden(A_12530, B_12531) | ~r1_tarski(k2_xboole_0(A_12532, k1_tarski(A_12530)), B_12531))), inference(resolution, [status(thm)], [c_424, c_2])).
% 5.62/2.20  tff(c_5811, plain, (r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_238, c_5794])).
% 5.62/2.20  tff(c_5838, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_5811])).
% 5.62/2.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.62/2.20  
% 5.62/2.20  Inference rules
% 5.62/2.20  ----------------------
% 5.62/2.20  #Ref     : 0
% 5.62/2.20  #Sup     : 655
% 5.62/2.20  #Fact    : 18
% 5.62/2.20  #Define  : 0
% 5.62/2.20  #Split   : 1
% 5.62/2.20  #Chain   : 0
% 5.62/2.20  #Close   : 0
% 5.62/2.20  
% 5.62/2.20  Ordering : KBO
% 5.62/2.20  
% 5.62/2.20  Simplification rules
% 5.62/2.20  ----------------------
% 5.62/2.20  #Subsume      : 92
% 5.62/2.20  #Demod        : 171
% 5.62/2.20  #Tautology    : 192
% 5.62/2.20  #SimpNegUnit  : 1
% 5.62/2.20  #BackRed      : 1
% 5.62/2.20  
% 5.62/2.20  #Partial instantiations: 3780
% 5.62/2.20  #Strategies tried      : 1
% 5.62/2.20  
% 5.62/2.20  Timing (in seconds)
% 5.62/2.20  ----------------------
% 5.62/2.20  Preprocessing        : 0.37
% 5.62/2.20  Parsing              : 0.18
% 5.62/2.20  CNF conversion       : 0.03
% 5.62/2.20  Main loop            : 1.00
% 5.62/2.20  Inferencing          : 0.54
% 5.62/2.20  Reduction            : 0.25
% 5.62/2.20  Demodulation         : 0.20
% 5.62/2.20  BG Simplification    : 0.04
% 5.62/2.20  Subsumption          : 0.12
% 5.62/2.20  Abstraction          : 0.05
% 5.62/2.20  MUC search           : 0.00
% 5.62/2.20  Cooper               : 0.00
% 5.62/2.20  Total                : 1.40
% 5.62/2.20  Index Insertion      : 0.00
% 5.62/2.20  Index Deletion       : 0.00
% 5.62/2.20  Index Matching       : 0.00
% 5.62/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
