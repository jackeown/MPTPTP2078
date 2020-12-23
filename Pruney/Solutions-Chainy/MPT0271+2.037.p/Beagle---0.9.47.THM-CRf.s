%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:05 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   50 (  70 expanded)
%              Number of leaves         :   20 (  33 expanded)
%              Depth                    :    5
%              Number of atoms          :   57 (  95 expanded)
%              Number of equality atoms :   17 (  33 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
      <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_20,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_34,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_24,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_68,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_59,plain,(
    ! [A_20,C_21,B_22] :
      ( r2_hidden(A_20,C_21)
      | ~ r1_tarski(k2_tarski(A_20,B_22),C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_73,plain,(
    ! [A_23,C_24] :
      ( r2_hidden(A_23,C_24)
      | ~ r1_tarski(k1_tarski(A_23),C_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_59])).

tff(c_88,plain,(
    ! [A_28,B_29] :
      ( r2_hidden(A_28,B_29)
      | k4_xboole_0(k1_tarski(A_28),B_29) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_73])).

tff(c_91,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_88])).

tff(c_95,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_91])).

tff(c_96,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_123,plain,(
    ! [A_43,B_44,C_45] :
      ( r1_tarski(k2_tarski(A_43,B_44),C_45)
      | ~ r2_hidden(B_44,C_45)
      | ~ r2_hidden(A_43,C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_139,plain,(
    ! [A_46,C_47] :
      ( r1_tarski(k1_tarski(A_46),C_47)
      | ~ r2_hidden(A_46,C_47)
      | ~ r2_hidden(A_46,C_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_123])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_148,plain,(
    ! [A_48,C_49] :
      ( k4_xboole_0(k1_tarski(A_48),C_49) = k1_xboole_0
      | ~ r2_hidden(A_48,C_49) ) ),
    inference(resolution,[status(thm)],[c_139,c_4])).

tff(c_97,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_22,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_114,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_22])).

tff(c_154,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_114])).

tff(c_168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_154])).

tff(c_169,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_231,plain,(
    ! [A_74,B_75,C_76] :
      ( r1_tarski(k2_tarski(A_74,B_75),C_76)
      | ~ r2_hidden(B_75,C_76)
      | ~ r2_hidden(A_74,C_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_247,plain,(
    ! [A_77,C_78] :
      ( r1_tarski(k1_tarski(A_77),C_78)
      | ~ r2_hidden(A_77,C_78)
      | ~ r2_hidden(A_77,C_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_231])).

tff(c_256,plain,(
    ! [A_79,C_80] :
      ( k4_xboole_0(k1_tarski(A_79),C_80) = k1_xboole_0
      | ~ r2_hidden(A_79,C_80) ) ),
    inference(resolution,[status(thm)],[c_247,c_4])).

tff(c_170,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_18,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_182,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_18])).

tff(c_265,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_182])).

tff(c_274,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_265])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:45:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.25  
% 1.90/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.26  %$ r2_hidden > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.90/1.26  
% 1.90/1.26  %Foreground sorts:
% 1.90/1.26  
% 1.90/1.26  
% 1.90/1.26  %Background operators:
% 1.90/1.26  
% 1.90/1.26  
% 1.90/1.26  %Foreground operators:
% 1.90/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.90/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.90/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.90/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.90/1.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.90/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.90/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.90/1.26  tff('#skF_2', type, '#skF_2': $i).
% 1.90/1.26  tff('#skF_3', type, '#skF_3': $i).
% 1.90/1.26  tff('#skF_1', type, '#skF_1': $i).
% 1.90/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.26  tff('#skF_4', type, '#skF_4': $i).
% 1.90/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.90/1.26  
% 1.90/1.27  tff(f_46, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 1.90/1.27  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.90/1.27  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.90/1.27  tff(f_41, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.90/1.27  tff(c_20, plain, (r2_hidden('#skF_1', '#skF_2') | ~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.90/1.27  tff(c_34, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_20])).
% 1.90/1.27  tff(c_24, plain, (r2_hidden('#skF_1', '#skF_2') | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.90/1.27  tff(c_68, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_24])).
% 1.90/1.27  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.90/1.27  tff(c_8, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.90/1.27  tff(c_59, plain, (![A_20, C_21, B_22]: (r2_hidden(A_20, C_21) | ~r1_tarski(k2_tarski(A_20, B_22), C_21))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.90/1.27  tff(c_73, plain, (![A_23, C_24]: (r2_hidden(A_23, C_24) | ~r1_tarski(k1_tarski(A_23), C_24))), inference(superposition, [status(thm), theory('equality')], [c_8, c_59])).
% 1.90/1.27  tff(c_88, plain, (![A_28, B_29]: (r2_hidden(A_28, B_29) | k4_xboole_0(k1_tarski(A_28), B_29)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_73])).
% 1.90/1.27  tff(c_91, plain, (r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_68, c_88])).
% 1.90/1.27  tff(c_95, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_91])).
% 1.90/1.27  tff(c_96, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_24])).
% 1.90/1.27  tff(c_123, plain, (![A_43, B_44, C_45]: (r1_tarski(k2_tarski(A_43, B_44), C_45) | ~r2_hidden(B_44, C_45) | ~r2_hidden(A_43, C_45))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.90/1.27  tff(c_139, plain, (![A_46, C_47]: (r1_tarski(k1_tarski(A_46), C_47) | ~r2_hidden(A_46, C_47) | ~r2_hidden(A_46, C_47))), inference(superposition, [status(thm), theory('equality')], [c_8, c_123])).
% 1.90/1.27  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.90/1.27  tff(c_148, plain, (![A_48, C_49]: (k4_xboole_0(k1_tarski(A_48), C_49)=k1_xboole_0 | ~r2_hidden(A_48, C_49))), inference(resolution, [status(thm)], [c_139, c_4])).
% 1.90/1.27  tff(c_97, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_24])).
% 1.90/1.27  tff(c_22, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0 | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.90/1.27  tff(c_114, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_97, c_22])).
% 1.90/1.27  tff(c_154, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_148, c_114])).
% 1.90/1.27  tff(c_168, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_154])).
% 1.90/1.27  tff(c_169, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_20])).
% 1.90/1.27  tff(c_231, plain, (![A_74, B_75, C_76]: (r1_tarski(k2_tarski(A_74, B_75), C_76) | ~r2_hidden(B_75, C_76) | ~r2_hidden(A_74, C_76))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.90/1.27  tff(c_247, plain, (![A_77, C_78]: (r1_tarski(k1_tarski(A_77), C_78) | ~r2_hidden(A_77, C_78) | ~r2_hidden(A_77, C_78))), inference(superposition, [status(thm), theory('equality')], [c_8, c_231])).
% 1.90/1.27  tff(c_256, plain, (![A_79, C_80]: (k4_xboole_0(k1_tarski(A_79), C_80)=k1_xboole_0 | ~r2_hidden(A_79, C_80))), inference(resolution, [status(thm)], [c_247, c_4])).
% 1.90/1.27  tff(c_170, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_20])).
% 1.90/1.27  tff(c_18, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0 | ~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.90/1.27  tff(c_182, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_170, c_18])).
% 1.90/1.27  tff(c_265, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_256, c_182])).
% 1.90/1.27  tff(c_274, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_169, c_265])).
% 1.90/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.27  
% 1.90/1.27  Inference rules
% 1.90/1.27  ----------------------
% 1.90/1.27  #Ref     : 0
% 1.90/1.27  #Sup     : 53
% 1.90/1.27  #Fact    : 0
% 1.90/1.27  #Define  : 0
% 1.90/1.27  #Split   : 2
% 1.90/1.27  #Chain   : 0
% 1.90/1.27  #Close   : 0
% 1.90/1.27  
% 1.90/1.27  Ordering : KBO
% 1.90/1.27  
% 1.90/1.27  Simplification rules
% 1.90/1.27  ----------------------
% 1.90/1.27  #Subsume      : 9
% 1.90/1.27  #Demod        : 4
% 1.90/1.27  #Tautology    : 24
% 1.90/1.27  #SimpNegUnit  : 2
% 1.90/1.27  #BackRed      : 0
% 1.90/1.27  
% 1.90/1.27  #Partial instantiations: 0
% 1.90/1.27  #Strategies tried      : 1
% 1.90/1.27  
% 1.90/1.27  Timing (in seconds)
% 1.90/1.27  ----------------------
% 1.90/1.27  Preprocessing        : 0.29
% 1.90/1.27  Parsing              : 0.16
% 1.90/1.27  CNF conversion       : 0.02
% 1.90/1.27  Main loop            : 0.17
% 1.90/1.27  Inferencing          : 0.08
% 1.90/1.27  Reduction            : 0.05
% 1.90/1.27  Demodulation         : 0.03
% 1.90/1.27  BG Simplification    : 0.01
% 1.90/1.27  Subsumption          : 0.02
% 1.90/1.27  Abstraction          : 0.01
% 1.90/1.27  MUC search           : 0.00
% 1.90/1.27  Cooper               : 0.00
% 1.90/1.27  Total                : 0.49
% 1.90/1.27  Index Insertion      : 0.00
% 1.90/1.27  Index Deletion       : 0.00
% 1.90/1.27  Index Matching       : 0.00
% 1.90/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
