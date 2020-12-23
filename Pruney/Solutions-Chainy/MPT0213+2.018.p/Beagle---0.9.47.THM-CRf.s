%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:29 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   34 ( 107 expanded)
%              Number of leaves         :   16 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :   43 ( 232 expanded)
%              Number of equality atoms :   11 (  34 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_57,negated_conjecture,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

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

tff(c_28,plain,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_113,plain,(
    ! [A_50,B_51] :
      ( r2_hidden('#skF_3'(A_50,B_51),A_50)
      | r2_hidden('#skF_4'(A_50,B_51),B_51)
      | k3_tarski(A_50) = B_51 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12,plain,(
    ! [A_7,C_22] :
      ( r2_hidden('#skF_5'(A_7,k3_tarski(A_7),C_22),A_7)
      | ~ r2_hidden(C_22,k3_tarski(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_69,plain,(
    ! [A_42,C_43] :
      ( r2_hidden('#skF_5'(A_42,k3_tarski(A_42),C_43),A_42)
      | ~ r2_hidden(C_43,k3_tarski(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_32,plain,(
    ! [A_31,B_32,C_33] :
      ( ~ r1_xboole_0(A_31,B_32)
      | ~ r2_hidden(C_33,B_32)
      | ~ r2_hidden(C_33,A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_35,plain,(
    ! [C_33,A_6] :
      ( ~ r2_hidden(C_33,k1_xboole_0)
      | ~ r2_hidden(C_33,A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_32])).

tff(c_82,plain,(
    ! [C_46,A_47] :
      ( ~ r2_hidden('#skF_5'(k1_xboole_0,k3_tarski(k1_xboole_0),C_46),A_47)
      | ~ r2_hidden(C_46,k3_tarski(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_69,c_35])).

tff(c_92,plain,(
    ! [C_22] : ~ r2_hidden(C_22,k3_tarski(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_12,c_82])).

tff(c_323,plain,(
    ! [A_78] :
      ( r2_hidden('#skF_3'(A_78,k3_tarski(k1_xboole_0)),A_78)
      | k3_tarski(k1_xboole_0) = k3_tarski(A_78) ) ),
    inference(resolution,[status(thm)],[c_113,c_92])).

tff(c_358,plain,(
    k3_tarski(k3_tarski(k1_xboole_0)) = k3_tarski(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_323,c_92])).

tff(c_130,plain,(
    ! [B_51] :
      ( r2_hidden('#skF_4'(k3_tarski(k1_xboole_0),B_51),B_51)
      | k3_tarski(k3_tarski(k1_xboole_0)) = B_51 ) ),
    inference(resolution,[status(thm)],[c_113,c_92])).

tff(c_412,plain,(
    ! [B_51] :
      ( r2_hidden('#skF_4'(k3_tarski(k1_xboole_0),B_51),B_51)
      | k3_tarski(k1_xboole_0) = B_51 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_130])).

tff(c_413,plain,(
    ! [B_82] :
      ( r2_hidden('#skF_4'(k3_tarski(k1_xboole_0),B_82),B_82)
      | k3_tarski(k1_xboole_0) = B_82 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_130])).

tff(c_424,plain,(
    ! [A_6] :
      ( ~ r2_hidden('#skF_4'(k3_tarski(k1_xboole_0),k1_xboole_0),A_6)
      | k3_tarski(k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_413,c_35])).

tff(c_438,plain,(
    ! [A_83] : ~ r2_hidden('#skF_4'(k3_tarski(k1_xboole_0),k1_xboole_0),A_83) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_424])).

tff(c_442,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_412,c_438])).

tff(c_452,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_442])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:03:55 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.27  
% 2.16/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.27  %$ r2_hidden > r1_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 2.16/1.27  
% 2.16/1.27  %Foreground sorts:
% 2.16/1.27  
% 2.16/1.27  
% 2.16/1.27  %Background operators:
% 2.16/1.27  
% 2.16/1.27  
% 2.16/1.27  %Foreground operators:
% 2.16/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.27  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.16/1.27  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.16/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.16/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.27  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.16/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.16/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.16/1.27  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.16/1.27  
% 2.16/1.28  tff(f_57, negated_conjecture, ~(k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.16/1.28  tff(f_55, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 2.16/1.28  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.16/1.28  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.16/1.28  tff(c_28, plain, (k3_tarski(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.16/1.28  tff(c_113, plain, (![A_50, B_51]: (r2_hidden('#skF_3'(A_50, B_51), A_50) | r2_hidden('#skF_4'(A_50, B_51), B_51) | k3_tarski(A_50)=B_51)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.16/1.28  tff(c_12, plain, (![A_7, C_22]: (r2_hidden('#skF_5'(A_7, k3_tarski(A_7), C_22), A_7) | ~r2_hidden(C_22, k3_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.16/1.28  tff(c_69, plain, (![A_42, C_43]: (r2_hidden('#skF_5'(A_42, k3_tarski(A_42), C_43), A_42) | ~r2_hidden(C_43, k3_tarski(A_42)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.16/1.28  tff(c_8, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.16/1.28  tff(c_32, plain, (![A_31, B_32, C_33]: (~r1_xboole_0(A_31, B_32) | ~r2_hidden(C_33, B_32) | ~r2_hidden(C_33, A_31))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.16/1.28  tff(c_35, plain, (![C_33, A_6]: (~r2_hidden(C_33, k1_xboole_0) | ~r2_hidden(C_33, A_6))), inference(resolution, [status(thm)], [c_8, c_32])).
% 2.16/1.28  tff(c_82, plain, (![C_46, A_47]: (~r2_hidden('#skF_5'(k1_xboole_0, k3_tarski(k1_xboole_0), C_46), A_47) | ~r2_hidden(C_46, k3_tarski(k1_xboole_0)))), inference(resolution, [status(thm)], [c_69, c_35])).
% 2.16/1.28  tff(c_92, plain, (![C_22]: (~r2_hidden(C_22, k3_tarski(k1_xboole_0)))), inference(resolution, [status(thm)], [c_12, c_82])).
% 2.16/1.28  tff(c_323, plain, (![A_78]: (r2_hidden('#skF_3'(A_78, k3_tarski(k1_xboole_0)), A_78) | k3_tarski(k1_xboole_0)=k3_tarski(A_78))), inference(resolution, [status(thm)], [c_113, c_92])).
% 2.16/1.28  tff(c_358, plain, (k3_tarski(k3_tarski(k1_xboole_0))=k3_tarski(k1_xboole_0)), inference(resolution, [status(thm)], [c_323, c_92])).
% 2.16/1.28  tff(c_130, plain, (![B_51]: (r2_hidden('#skF_4'(k3_tarski(k1_xboole_0), B_51), B_51) | k3_tarski(k3_tarski(k1_xboole_0))=B_51)), inference(resolution, [status(thm)], [c_113, c_92])).
% 2.16/1.28  tff(c_412, plain, (![B_51]: (r2_hidden('#skF_4'(k3_tarski(k1_xboole_0), B_51), B_51) | k3_tarski(k1_xboole_0)=B_51)), inference(demodulation, [status(thm), theory('equality')], [c_358, c_130])).
% 2.16/1.28  tff(c_413, plain, (![B_82]: (r2_hidden('#skF_4'(k3_tarski(k1_xboole_0), B_82), B_82) | k3_tarski(k1_xboole_0)=B_82)), inference(demodulation, [status(thm), theory('equality')], [c_358, c_130])).
% 2.16/1.28  tff(c_424, plain, (![A_6]: (~r2_hidden('#skF_4'(k3_tarski(k1_xboole_0), k1_xboole_0), A_6) | k3_tarski(k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_413, c_35])).
% 2.16/1.28  tff(c_438, plain, (![A_83]: (~r2_hidden('#skF_4'(k3_tarski(k1_xboole_0), k1_xboole_0), A_83))), inference(negUnitSimplification, [status(thm)], [c_28, c_424])).
% 2.16/1.28  tff(c_442, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_412, c_438])).
% 2.16/1.28  tff(c_452, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_442])).
% 2.16/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.28  
% 2.16/1.28  Inference rules
% 2.16/1.28  ----------------------
% 2.16/1.28  #Ref     : 0
% 2.16/1.28  #Sup     : 82
% 2.16/1.28  #Fact    : 0
% 2.16/1.28  #Define  : 0
% 2.16/1.28  #Split   : 0
% 2.16/1.28  #Chain   : 0
% 2.16/1.28  #Close   : 0
% 2.16/1.28  
% 2.16/1.28  Ordering : KBO
% 2.16/1.28  
% 2.16/1.28  Simplification rules
% 2.16/1.28  ----------------------
% 2.16/1.28  #Subsume      : 24
% 2.16/1.28  #Demod        : 77
% 2.16/1.28  #Tautology    : 21
% 2.16/1.28  #SimpNegUnit  : 4
% 2.16/1.28  #BackRed      : 15
% 2.16/1.28  
% 2.16/1.28  #Partial instantiations: 0
% 2.16/1.28  #Strategies tried      : 1
% 2.16/1.28  
% 2.16/1.28  Timing (in seconds)
% 2.16/1.28  ----------------------
% 2.16/1.29  Preprocessing        : 0.28
% 2.16/1.29  Parsing              : 0.15
% 2.16/1.29  CNF conversion       : 0.02
% 2.16/1.29  Main loop            : 0.27
% 2.16/1.29  Inferencing          : 0.11
% 2.16/1.29  Reduction            : 0.07
% 2.16/1.29  Demodulation         : 0.05
% 2.16/1.29  BG Simplification    : 0.01
% 2.16/1.29  Subsumption          : 0.06
% 2.16/1.29  Abstraction          : 0.01
% 2.16/1.29  MUC search           : 0.00
% 2.16/1.29  Cooper               : 0.00
% 2.16/1.29  Total                : 0.57
% 2.16/1.29  Index Insertion      : 0.00
% 2.16/1.29  Index Deletion       : 0.00
% 2.16/1.29  Index Matching       : 0.00
% 2.16/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
