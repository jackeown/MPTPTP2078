%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:29 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 192 expanded)
%              Number of leaves         :   18 (  73 expanded)
%              Depth                    :   15
%              Number of atoms          :   56 ( 463 expanded)
%              Number of equality atoms :   13 (  48 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_59,negated_conjecture,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_47,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_30,plain,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_200,plain,(
    ! [A_67,B_68] :
      ( r2_hidden('#skF_3'(A_67,B_68),A_67)
      | r2_hidden('#skF_4'(A_67,B_68),B_68)
      | k3_tarski(A_67) = B_68 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_14,plain,(
    ! [A_9,C_24] :
      ( r2_hidden('#skF_5'(A_9,k3_tarski(A_9),C_24),A_9)
      | ~ r2_hidden(C_24,k3_tarski(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_107,plain,(
    ! [A_52,C_53] :
      ( r2_hidden('#skF_5'(A_52,k3_tarski(A_52),C_53),A_52)
      | ~ r2_hidden(C_53,k3_tarski(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_38,plain,(
    ! [A_29,B_30] : r1_xboole_0(k4_xboole_0(A_29,B_30),B_30) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_41,plain,(
    ! [A_6] : r1_xboole_0(k1_xboole_0,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_38])).

tff(c_45,plain,(
    ! [A_36,B_37,C_38] :
      ( ~ r1_xboole_0(A_36,B_37)
      | ~ r2_hidden(C_38,B_37)
      | ~ r2_hidden(C_38,A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_52,plain,(
    ! [C_39,A_40] :
      ( ~ r2_hidden(C_39,A_40)
      | ~ r2_hidden(C_39,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_41,c_45])).

tff(c_80,plain,(
    ! [A_47,B_48] :
      ( ~ r2_hidden('#skF_1'(A_47,B_48),k1_xboole_0)
      | r1_xboole_0(A_47,B_48) ) ),
    inference(resolution,[status(thm)],[c_4,c_52])).

tff(c_92,plain,(
    ! [A_49] : r1_xboole_0(A_49,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_80])).

tff(c_2,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_95,plain,(
    ! [C_5,A_49] :
      ( ~ r2_hidden(C_5,k1_xboole_0)
      | ~ r2_hidden(C_5,A_49) ) ),
    inference(resolution,[status(thm)],[c_92,c_2])).

tff(c_124,plain,(
    ! [C_56,A_57] :
      ( ~ r2_hidden('#skF_5'(k1_xboole_0,k3_tarski(k1_xboole_0),C_56),A_57)
      | ~ r2_hidden(C_56,k3_tarski(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_107,c_95])).

tff(c_134,plain,(
    ! [C_24] : ~ r2_hidden(C_24,k3_tarski(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_14,c_124])).

tff(c_375,plain,(
    ! [A_88] :
      ( r2_hidden('#skF_3'(A_88,k3_tarski(k1_xboole_0)),A_88)
      | k3_tarski(k1_xboole_0) = k3_tarski(A_88) ) ),
    inference(resolution,[status(thm)],[c_200,c_134])).

tff(c_414,plain,(
    k3_tarski(k3_tarski(k1_xboole_0)) = k3_tarski(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_375,c_134])).

tff(c_243,plain,(
    ! [B_68] :
      ( r2_hidden('#skF_4'(k3_tarski(k1_xboole_0),B_68),B_68)
      | k3_tarski(k3_tarski(k1_xboole_0)) = B_68 ) ),
    inference(resolution,[status(thm)],[c_200,c_134])).

tff(c_469,plain,(
    ! [B_68] :
      ( r2_hidden('#skF_4'(k3_tarski(k1_xboole_0),B_68),B_68)
      | k3_tarski(k1_xboole_0) = B_68 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_414,c_243])).

tff(c_470,plain,(
    ! [B_92] :
      ( r2_hidden('#skF_4'(k3_tarski(k1_xboole_0),B_92),B_92)
      | k3_tarski(k1_xboole_0) = B_92 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_414,c_243])).

tff(c_481,plain,(
    ! [A_49] :
      ( ~ r2_hidden('#skF_4'(k3_tarski(k1_xboole_0),k1_xboole_0),A_49)
      | k3_tarski(k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_470,c_95])).

tff(c_500,plain,(
    ! [A_93] : ~ r2_hidden('#skF_4'(k3_tarski(k1_xboole_0),k1_xboole_0),A_93) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_481])).

tff(c_504,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_469,c_500])).

tff(c_514,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_504])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:47:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.30  
% 2.11/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.30  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 2.11/1.30  
% 2.11/1.30  %Foreground sorts:
% 2.11/1.30  
% 2.11/1.30  
% 2.11/1.30  %Background operators:
% 2.11/1.30  
% 2.11/1.30  
% 2.11/1.30  %Foreground operators:
% 2.11/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.11/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.11/1.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.11/1.30  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.11/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.11/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.11/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.11/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.11/1.30  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.11/1.30  
% 2.43/1.31  tff(f_59, negated_conjecture, ~(k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.43/1.31  tff(f_57, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 2.43/1.31  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.43/1.31  tff(f_45, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.43/1.31  tff(f_47, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.43/1.31  tff(c_30, plain, (k3_tarski(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.43/1.31  tff(c_200, plain, (![A_67, B_68]: (r2_hidden('#skF_3'(A_67, B_68), A_67) | r2_hidden('#skF_4'(A_67, B_68), B_68) | k3_tarski(A_67)=B_68)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.43/1.31  tff(c_14, plain, (![A_9, C_24]: (r2_hidden('#skF_5'(A_9, k3_tarski(A_9), C_24), A_9) | ~r2_hidden(C_24, k3_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.43/1.31  tff(c_107, plain, (![A_52, C_53]: (r2_hidden('#skF_5'(A_52, k3_tarski(A_52), C_53), A_52) | ~r2_hidden(C_53, k3_tarski(A_52)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.43/1.31  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.43/1.31  tff(c_8, plain, (![A_6]: (k4_xboole_0(k1_xboole_0, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.43/1.31  tff(c_38, plain, (![A_29, B_30]: (r1_xboole_0(k4_xboole_0(A_29, B_30), B_30))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.43/1.31  tff(c_41, plain, (![A_6]: (r1_xboole_0(k1_xboole_0, A_6))), inference(superposition, [status(thm), theory('equality')], [c_8, c_38])).
% 2.43/1.31  tff(c_45, plain, (![A_36, B_37, C_38]: (~r1_xboole_0(A_36, B_37) | ~r2_hidden(C_38, B_37) | ~r2_hidden(C_38, A_36))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.43/1.31  tff(c_52, plain, (![C_39, A_40]: (~r2_hidden(C_39, A_40) | ~r2_hidden(C_39, k1_xboole_0))), inference(resolution, [status(thm)], [c_41, c_45])).
% 2.43/1.31  tff(c_80, plain, (![A_47, B_48]: (~r2_hidden('#skF_1'(A_47, B_48), k1_xboole_0) | r1_xboole_0(A_47, B_48))), inference(resolution, [status(thm)], [c_4, c_52])).
% 2.43/1.31  tff(c_92, plain, (![A_49]: (r1_xboole_0(A_49, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_80])).
% 2.43/1.31  tff(c_2, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.43/1.31  tff(c_95, plain, (![C_5, A_49]: (~r2_hidden(C_5, k1_xboole_0) | ~r2_hidden(C_5, A_49))), inference(resolution, [status(thm)], [c_92, c_2])).
% 2.43/1.31  tff(c_124, plain, (![C_56, A_57]: (~r2_hidden('#skF_5'(k1_xboole_0, k3_tarski(k1_xboole_0), C_56), A_57) | ~r2_hidden(C_56, k3_tarski(k1_xboole_0)))), inference(resolution, [status(thm)], [c_107, c_95])).
% 2.43/1.31  tff(c_134, plain, (![C_24]: (~r2_hidden(C_24, k3_tarski(k1_xboole_0)))), inference(resolution, [status(thm)], [c_14, c_124])).
% 2.43/1.31  tff(c_375, plain, (![A_88]: (r2_hidden('#skF_3'(A_88, k3_tarski(k1_xboole_0)), A_88) | k3_tarski(k1_xboole_0)=k3_tarski(A_88))), inference(resolution, [status(thm)], [c_200, c_134])).
% 2.43/1.31  tff(c_414, plain, (k3_tarski(k3_tarski(k1_xboole_0))=k3_tarski(k1_xboole_0)), inference(resolution, [status(thm)], [c_375, c_134])).
% 2.43/1.31  tff(c_243, plain, (![B_68]: (r2_hidden('#skF_4'(k3_tarski(k1_xboole_0), B_68), B_68) | k3_tarski(k3_tarski(k1_xboole_0))=B_68)), inference(resolution, [status(thm)], [c_200, c_134])).
% 2.43/1.31  tff(c_469, plain, (![B_68]: (r2_hidden('#skF_4'(k3_tarski(k1_xboole_0), B_68), B_68) | k3_tarski(k1_xboole_0)=B_68)), inference(demodulation, [status(thm), theory('equality')], [c_414, c_243])).
% 2.43/1.31  tff(c_470, plain, (![B_92]: (r2_hidden('#skF_4'(k3_tarski(k1_xboole_0), B_92), B_92) | k3_tarski(k1_xboole_0)=B_92)), inference(demodulation, [status(thm), theory('equality')], [c_414, c_243])).
% 2.43/1.31  tff(c_481, plain, (![A_49]: (~r2_hidden('#skF_4'(k3_tarski(k1_xboole_0), k1_xboole_0), A_49) | k3_tarski(k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_470, c_95])).
% 2.43/1.31  tff(c_500, plain, (![A_93]: (~r2_hidden('#skF_4'(k3_tarski(k1_xboole_0), k1_xboole_0), A_93))), inference(negUnitSimplification, [status(thm)], [c_30, c_481])).
% 2.43/1.31  tff(c_504, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_469, c_500])).
% 2.43/1.31  tff(c_514, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_504])).
% 2.43/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.31  
% 2.43/1.31  Inference rules
% 2.43/1.31  ----------------------
% 2.43/1.31  #Ref     : 0
% 2.43/1.31  #Sup     : 96
% 2.43/1.31  #Fact    : 0
% 2.43/1.31  #Define  : 0
% 2.43/1.31  #Split   : 0
% 2.43/1.31  #Chain   : 0
% 2.43/1.31  #Close   : 0
% 2.43/1.31  
% 2.43/1.31  Ordering : KBO
% 2.43/1.31  
% 2.43/1.31  Simplification rules
% 2.43/1.31  ----------------------
% 2.43/1.31  #Subsume      : 26
% 2.43/1.31  #Demod        : 77
% 2.43/1.31  #Tautology    : 23
% 2.43/1.31  #SimpNegUnit  : 4
% 2.43/1.31  #BackRed      : 15
% 2.43/1.31  
% 2.43/1.31  #Partial instantiations: 0
% 2.43/1.31  #Strategies tried      : 1
% 2.43/1.31  
% 2.43/1.31  Timing (in seconds)
% 2.43/1.31  ----------------------
% 2.43/1.32  Preprocessing        : 0.28
% 2.43/1.32  Parsing              : 0.15
% 2.43/1.32  CNF conversion       : 0.02
% 2.43/1.32  Main loop            : 0.27
% 2.43/1.32  Inferencing          : 0.11
% 2.43/1.32  Reduction            : 0.07
% 2.43/1.32  Demodulation         : 0.05
% 2.43/1.32  BG Simplification    : 0.01
% 2.43/1.32  Subsumption          : 0.05
% 2.43/1.32  Abstraction          : 0.01
% 2.43/1.32  MUC search           : 0.00
% 2.43/1.32  Cooper               : 0.00
% 2.43/1.32  Total                : 0.58
% 2.43/1.32  Index Insertion      : 0.00
% 2.43/1.32  Index Deletion       : 0.00
% 2.43/1.32  Index Matching       : 0.00
% 2.43/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
