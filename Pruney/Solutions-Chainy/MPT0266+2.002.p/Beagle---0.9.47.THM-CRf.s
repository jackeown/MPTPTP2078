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
% DateTime   : Thu Dec  3 09:52:26 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :   55 (  63 expanded)
%              Number of leaves         :   31 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   43 (  52 expanded)
%              Number of equality atoms :   24 (  32 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k3_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_69,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_54,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_56,plain,(
    k3_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_14,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_127,plain,(
    ! [A_65,B_66] : k3_tarski(k2_tarski(A_65,B_66)) = k2_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_187,plain,(
    ! [A_75,B_76] : k3_tarski(k2_tarski(A_75,B_76)) = k2_xboole_0(B_76,A_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_127])).

tff(c_52,plain,(
    ! [A_48,B_49] : k3_tarski(k2_tarski(A_48,B_49)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_193,plain,(
    ! [B_76,A_75] : k2_xboole_0(B_76,A_75) = k2_xboole_0(A_75,B_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_52])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_306,plain,(
    ! [A_94,B_95] : k5_xboole_0(k5_xboole_0(A_94,B_95),k2_xboole_0(A_94,B_95)) = k3_xboole_0(A_94,B_95) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_422,plain,(
    ! [A_114,B_115] : k5_xboole_0(k5_xboole_0(A_114,B_115),k2_xboole_0(B_115,A_114)) = k3_xboole_0(B_115,A_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_306])).

tff(c_514,plain,(
    ! [B_120,A_121] : k5_xboole_0(k2_xboole_0(B_120,A_121),k5_xboole_0(A_121,B_120)) = k3_xboole_0(B_120,A_121) ),
    inference(superposition,[status(thm),theory(equality)],[c_422,c_2])).

tff(c_589,plain,(
    ! [B_127,A_128] : k5_xboole_0(k2_xboole_0(B_127,A_128),k5_xboole_0(B_127,A_128)) = k3_xboole_0(A_128,B_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_514])).

tff(c_342,plain,(
    ! [A_94,B_95] : k5_xboole_0(k2_xboole_0(A_94,B_95),k5_xboole_0(A_94,B_95)) = k3_xboole_0(A_94,B_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_306])).

tff(c_671,plain,(
    ! [B_135,A_136] : k3_xboole_0(B_135,A_136) = k3_xboole_0(A_136,B_135) ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_342])).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_722,plain,(
    ! [B_137,A_138] : r1_tarski(k3_xboole_0(B_137,A_138),A_138) ),
    inference(superposition,[status(thm),theory(equality)],[c_671,c_10])).

tff(c_731,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_722])).

tff(c_142,plain,(
    ! [A_67,B_68] : k1_enumset1(A_67,A_67,B_68) = k2_tarski(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22,plain,(
    ! [E_20,B_15,C_16] : r2_hidden(E_20,k1_enumset1(E_20,B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_154,plain,(
    ! [A_67,B_68] : r2_hidden(A_67,k2_tarski(A_67,B_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_22])).

tff(c_252,plain,(
    ! [C_82,B_83,A_84] :
      ( r2_hidden(C_82,B_83)
      | ~ r2_hidden(C_82,A_84)
      | ~ r1_tarski(A_84,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_266,plain,(
    ! [A_67,B_83,B_68] :
      ( r2_hidden(A_67,B_83)
      | ~ r1_tarski(k2_tarski(A_67,B_68),B_83) ) ),
    inference(resolution,[status(thm)],[c_154,c_252])).

tff(c_740,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_731,c_266])).

tff(c_745,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_740])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:35:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.56  
% 3.06/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.56  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 3.06/1.56  
% 3.06/1.56  %Foreground sorts:
% 3.06/1.56  
% 3.06/1.56  
% 3.06/1.56  %Background operators:
% 3.06/1.56  
% 3.06/1.56  
% 3.06/1.56  %Foreground operators:
% 3.06/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.06/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.06/1.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.06/1.56  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.06/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.06/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.06/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.06/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.06/1.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.06/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.06/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.06/1.56  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.06/1.56  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.06/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.06/1.56  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.06/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.06/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.06/1.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.06/1.56  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.06/1.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.06/1.56  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.06/1.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.06/1.56  
% 3.06/1.57  tff(f_74, negated_conjecture, ~(![A, B, C]: ((k3_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 3.06/1.57  tff(f_40, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.06/1.57  tff(f_69, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.06/1.57  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.06/1.57  tff(f_38, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.06/1.57  tff(f_36, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.06/1.57  tff(f_57, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.06/1.57  tff(f_55, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.06/1.57  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.06/1.57  tff(c_54, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.06/1.57  tff(c_56, plain, (k3_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.06/1.57  tff(c_14, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.06/1.57  tff(c_127, plain, (![A_65, B_66]: (k3_tarski(k2_tarski(A_65, B_66))=k2_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.06/1.57  tff(c_187, plain, (![A_75, B_76]: (k3_tarski(k2_tarski(A_75, B_76))=k2_xboole_0(B_76, A_75))), inference(superposition, [status(thm), theory('equality')], [c_14, c_127])).
% 3.06/1.57  tff(c_52, plain, (![A_48, B_49]: (k3_tarski(k2_tarski(A_48, B_49))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.06/1.57  tff(c_193, plain, (![B_76, A_75]: (k2_xboole_0(B_76, A_75)=k2_xboole_0(A_75, B_76))), inference(superposition, [status(thm), theory('equality')], [c_187, c_52])).
% 3.06/1.57  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.06/1.57  tff(c_306, plain, (![A_94, B_95]: (k5_xboole_0(k5_xboole_0(A_94, B_95), k2_xboole_0(A_94, B_95))=k3_xboole_0(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.06/1.57  tff(c_422, plain, (![A_114, B_115]: (k5_xboole_0(k5_xboole_0(A_114, B_115), k2_xboole_0(B_115, A_114))=k3_xboole_0(B_115, A_114))), inference(superposition, [status(thm), theory('equality')], [c_2, c_306])).
% 3.06/1.57  tff(c_514, plain, (![B_120, A_121]: (k5_xboole_0(k2_xboole_0(B_120, A_121), k5_xboole_0(A_121, B_120))=k3_xboole_0(B_120, A_121))), inference(superposition, [status(thm), theory('equality')], [c_422, c_2])).
% 3.06/1.57  tff(c_589, plain, (![B_127, A_128]: (k5_xboole_0(k2_xboole_0(B_127, A_128), k5_xboole_0(B_127, A_128))=k3_xboole_0(A_128, B_127))), inference(superposition, [status(thm), theory('equality')], [c_193, c_514])).
% 3.06/1.57  tff(c_342, plain, (![A_94, B_95]: (k5_xboole_0(k2_xboole_0(A_94, B_95), k5_xboole_0(A_94, B_95))=k3_xboole_0(A_94, B_95))), inference(superposition, [status(thm), theory('equality')], [c_2, c_306])).
% 3.06/1.57  tff(c_671, plain, (![B_135, A_136]: (k3_xboole_0(B_135, A_136)=k3_xboole_0(A_136, B_135))), inference(superposition, [status(thm), theory('equality')], [c_589, c_342])).
% 3.06/1.57  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.06/1.57  tff(c_722, plain, (![B_137, A_138]: (r1_tarski(k3_xboole_0(B_137, A_138), A_138))), inference(superposition, [status(thm), theory('equality')], [c_671, c_10])).
% 3.06/1.57  tff(c_731, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_56, c_722])).
% 3.06/1.57  tff(c_142, plain, (![A_67, B_68]: (k1_enumset1(A_67, A_67, B_68)=k2_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.06/1.57  tff(c_22, plain, (![E_20, B_15, C_16]: (r2_hidden(E_20, k1_enumset1(E_20, B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.06/1.57  tff(c_154, plain, (![A_67, B_68]: (r2_hidden(A_67, k2_tarski(A_67, B_68)))), inference(superposition, [status(thm), theory('equality')], [c_142, c_22])).
% 3.06/1.57  tff(c_252, plain, (![C_82, B_83, A_84]: (r2_hidden(C_82, B_83) | ~r2_hidden(C_82, A_84) | ~r1_tarski(A_84, B_83))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.06/1.57  tff(c_266, plain, (![A_67, B_83, B_68]: (r2_hidden(A_67, B_83) | ~r1_tarski(k2_tarski(A_67, B_68), B_83))), inference(resolution, [status(thm)], [c_154, c_252])).
% 3.06/1.57  tff(c_740, plain, (r2_hidden('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_731, c_266])).
% 3.06/1.57  tff(c_745, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_740])).
% 3.06/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.57  
% 3.06/1.57  Inference rules
% 3.06/1.57  ----------------------
% 3.06/1.57  #Ref     : 0
% 3.06/1.57  #Sup     : 173
% 3.06/1.57  #Fact    : 0
% 3.06/1.57  #Define  : 0
% 3.06/1.57  #Split   : 0
% 3.06/1.57  #Chain   : 0
% 3.06/1.57  #Close   : 0
% 3.06/1.57  
% 3.06/1.57  Ordering : KBO
% 3.06/1.57  
% 3.06/1.57  Simplification rules
% 3.06/1.57  ----------------------
% 3.06/1.57  #Subsume      : 8
% 3.06/1.57  #Demod        : 54
% 3.06/1.57  #Tautology    : 99
% 3.06/1.57  #SimpNegUnit  : 1
% 3.06/1.57  #BackRed      : 0
% 3.06/1.57  
% 3.06/1.57  #Partial instantiations: 0
% 3.06/1.57  #Strategies tried      : 1
% 3.06/1.57  
% 3.06/1.57  Timing (in seconds)
% 3.06/1.57  ----------------------
% 3.06/1.58  Preprocessing        : 0.39
% 3.06/1.58  Parsing              : 0.21
% 3.06/1.58  CNF conversion       : 0.03
% 3.06/1.58  Main loop            : 0.40
% 3.06/1.58  Inferencing          : 0.12
% 3.06/1.58  Reduction            : 0.16
% 3.06/1.58  Demodulation         : 0.13
% 3.06/1.58  BG Simplification    : 0.02
% 3.06/1.58  Subsumption          : 0.06
% 3.06/1.58  Abstraction          : 0.02
% 3.06/1.58  MUC search           : 0.00
% 3.06/1.58  Cooper               : 0.00
% 3.06/1.58  Total                : 0.83
% 3.06/1.58  Index Insertion      : 0.00
% 3.06/1.58  Index Deletion       : 0.00
% 3.06/1.58  Index Matching       : 0.00
% 3.06/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
