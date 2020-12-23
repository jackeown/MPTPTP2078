%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:27 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   42 (  80 expanded)
%              Number of leaves         :   21 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :   50 ( 144 expanded)
%              Number of equality atoms :   16 (  36 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k3_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_6 > #skF_3 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_60,negated_conjecture,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_48,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_52,plain,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_256,plain,(
    ! [A_77,B_78] :
      ( r2_hidden('#skF_4'(A_77,B_78),A_77)
      | r2_hidden('#skF_5'(A_77,B_78),B_78)
      | k3_tarski(A_77) = B_78 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_36,plain,(
    ! [A_12,C_27] :
      ( r2_hidden('#skF_6'(A_12,k3_tarski(A_12),C_27),A_12)
      | ~ r2_hidden(C_27,k3_tarski(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_130,plain,(
    ! [A_55,C_56] :
      ( r2_hidden('#skF_6'(A_55,k3_tarski(A_55),C_56),A_55)
      | ~ r2_hidden(C_56,k3_tarski(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_32,plain,(
    ! [A_11] : k4_xboole_0(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_108,plain,(
    ! [D_43,B_44,A_45] :
      ( ~ r2_hidden(D_43,B_44)
      | ~ r2_hidden(D_43,k4_xboole_0(A_45,B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_114,plain,(
    ! [D_43,A_11] :
      ( ~ r2_hidden(D_43,A_11)
      | ~ r2_hidden(D_43,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_108])).

tff(c_208,plain,(
    ! [A_67,C_68] :
      ( ~ r2_hidden('#skF_6'(A_67,k3_tarski(A_67),C_68),k1_xboole_0)
      | ~ r2_hidden(C_68,k3_tarski(A_67)) ) ),
    inference(resolution,[status(thm)],[c_130,c_114])).

tff(c_213,plain,(
    ! [C_27] : ~ r2_hidden(C_27,k3_tarski(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_36,c_208])).

tff(c_364,plain,(
    ! [B_79] :
      ( r2_hidden('#skF_5'(k3_tarski(k1_xboole_0),B_79),B_79)
      | k3_tarski(k3_tarski(k1_xboole_0)) = B_79 ) ),
    inference(resolution,[status(thm)],[c_256,c_213])).

tff(c_414,plain,(
    k3_tarski(k3_tarski(k1_xboole_0)) = k3_tarski(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_364,c_213])).

tff(c_346,plain,(
    ! [B_78] :
      ( r2_hidden('#skF_5'(k3_tarski(k1_xboole_0),B_78),B_78)
      | k3_tarski(k3_tarski(k1_xboole_0)) = B_78 ) ),
    inference(resolution,[status(thm)],[c_256,c_213])).

tff(c_448,plain,(
    ! [B_80] :
      ( r2_hidden('#skF_5'(k3_tarski(k1_xboole_0),B_80),B_80)
      | k3_tarski(k1_xboole_0) = B_80 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_414,c_346])).

tff(c_26,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_67,plain,(
    ! [A_35,B_36] :
      ( k4_xboole_0(A_35,B_36) = k1_xboole_0
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_75,plain,(
    ! [B_8] : k4_xboole_0(B_8,B_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_67])).

tff(c_101,plain,(
    ! [D_40,A_41,B_42] :
      ( r2_hidden(D_40,A_41)
      | ~ r2_hidden(D_40,k4_xboole_0(A_41,B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_104,plain,(
    ! [D_40,B_8] :
      ( r2_hidden(D_40,B_8)
      | ~ r2_hidden(D_40,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_101])).

tff(c_461,plain,(
    ! [B_8] :
      ( r2_hidden('#skF_5'(k3_tarski(k1_xboole_0),k1_xboole_0),B_8)
      | k3_tarski(k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_448,c_104])).

tff(c_489,plain,(
    ! [B_83] : r2_hidden('#skF_5'(k3_tarski(k1_xboole_0),k1_xboole_0),B_83) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_461])).

tff(c_513,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_489,c_213])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:00:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.33  
% 2.36/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.33  %$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k3_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_6 > #skF_3 > #skF_2 > #skF_5 > #skF_4
% 2.36/1.33  
% 2.36/1.33  %Foreground sorts:
% 2.36/1.33  
% 2.36/1.33  
% 2.36/1.33  %Background operators:
% 2.36/1.33  
% 2.36/1.33  
% 2.36/1.33  %Foreground operators:
% 2.36/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.36/1.33  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 2.36/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.36/1.33  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.36/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.36/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.36/1.33  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.36/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.36/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.36/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.36/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.33  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.36/1.33  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.36/1.33  
% 2.36/1.34  tff(f_60, negated_conjecture, ~(k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.36/1.34  tff(f_58, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 2.36/1.34  tff(f_48, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.36/1.34  tff(f_36, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.36/1.34  tff(f_42, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.36/1.34  tff(f_46, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.36/1.34  tff(c_52, plain, (k3_tarski(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.36/1.34  tff(c_256, plain, (![A_77, B_78]: (r2_hidden('#skF_4'(A_77, B_78), A_77) | r2_hidden('#skF_5'(A_77, B_78), B_78) | k3_tarski(A_77)=B_78)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.36/1.34  tff(c_36, plain, (![A_12, C_27]: (r2_hidden('#skF_6'(A_12, k3_tarski(A_12), C_27), A_12) | ~r2_hidden(C_27, k3_tarski(A_12)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.36/1.34  tff(c_130, plain, (![A_55, C_56]: (r2_hidden('#skF_6'(A_55, k3_tarski(A_55), C_56), A_55) | ~r2_hidden(C_56, k3_tarski(A_55)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.36/1.34  tff(c_32, plain, (![A_11]: (k4_xboole_0(k1_xboole_0, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.36/1.34  tff(c_108, plain, (![D_43, B_44, A_45]: (~r2_hidden(D_43, B_44) | ~r2_hidden(D_43, k4_xboole_0(A_45, B_44)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.36/1.34  tff(c_114, plain, (![D_43, A_11]: (~r2_hidden(D_43, A_11) | ~r2_hidden(D_43, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_108])).
% 2.36/1.34  tff(c_208, plain, (![A_67, C_68]: (~r2_hidden('#skF_6'(A_67, k3_tarski(A_67), C_68), k1_xboole_0) | ~r2_hidden(C_68, k3_tarski(A_67)))), inference(resolution, [status(thm)], [c_130, c_114])).
% 2.36/1.34  tff(c_213, plain, (![C_27]: (~r2_hidden(C_27, k3_tarski(k1_xboole_0)))), inference(resolution, [status(thm)], [c_36, c_208])).
% 2.36/1.34  tff(c_364, plain, (![B_79]: (r2_hidden('#skF_5'(k3_tarski(k1_xboole_0), B_79), B_79) | k3_tarski(k3_tarski(k1_xboole_0))=B_79)), inference(resolution, [status(thm)], [c_256, c_213])).
% 2.36/1.34  tff(c_414, plain, (k3_tarski(k3_tarski(k1_xboole_0))=k3_tarski(k1_xboole_0)), inference(resolution, [status(thm)], [c_364, c_213])).
% 2.36/1.34  tff(c_346, plain, (![B_78]: (r2_hidden('#skF_5'(k3_tarski(k1_xboole_0), B_78), B_78) | k3_tarski(k3_tarski(k1_xboole_0))=B_78)), inference(resolution, [status(thm)], [c_256, c_213])).
% 2.36/1.34  tff(c_448, plain, (![B_80]: (r2_hidden('#skF_5'(k3_tarski(k1_xboole_0), B_80), B_80) | k3_tarski(k1_xboole_0)=B_80)), inference(demodulation, [status(thm), theory('equality')], [c_414, c_346])).
% 2.36/1.34  tff(c_26, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.36/1.34  tff(c_67, plain, (![A_35, B_36]: (k4_xboole_0(A_35, B_36)=k1_xboole_0 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.36/1.34  tff(c_75, plain, (![B_8]: (k4_xboole_0(B_8, B_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_67])).
% 2.36/1.34  tff(c_101, plain, (![D_40, A_41, B_42]: (r2_hidden(D_40, A_41) | ~r2_hidden(D_40, k4_xboole_0(A_41, B_42)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.36/1.34  tff(c_104, plain, (![D_40, B_8]: (r2_hidden(D_40, B_8) | ~r2_hidden(D_40, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_75, c_101])).
% 2.36/1.34  tff(c_461, plain, (![B_8]: (r2_hidden('#skF_5'(k3_tarski(k1_xboole_0), k1_xboole_0), B_8) | k3_tarski(k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_448, c_104])).
% 2.36/1.34  tff(c_489, plain, (![B_83]: (r2_hidden('#skF_5'(k3_tarski(k1_xboole_0), k1_xboole_0), B_83))), inference(negUnitSimplification, [status(thm)], [c_52, c_461])).
% 2.36/1.34  tff(c_513, plain, $false, inference(resolution, [status(thm)], [c_489, c_213])).
% 2.36/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.34  
% 2.36/1.34  Inference rules
% 2.36/1.34  ----------------------
% 2.36/1.34  #Ref     : 0
% 2.36/1.34  #Sup     : 101
% 2.36/1.34  #Fact    : 0
% 2.36/1.34  #Define  : 0
% 2.36/1.34  #Split   : 0
% 2.36/1.34  #Chain   : 0
% 2.36/1.34  #Close   : 0
% 2.36/1.34  
% 2.36/1.34  Ordering : KBO
% 2.36/1.34  
% 2.36/1.34  Simplification rules
% 2.36/1.34  ----------------------
% 2.36/1.34  #Subsume      : 12
% 2.36/1.34  #Demod        : 26
% 2.36/1.34  #Tautology    : 25
% 2.36/1.34  #SimpNegUnit  : 2
% 2.36/1.34  #BackRed      : 6
% 2.36/1.34  
% 2.36/1.34  #Partial instantiations: 0
% 2.36/1.34  #Strategies tried      : 1
% 2.36/1.34  
% 2.36/1.34  Timing (in seconds)
% 2.36/1.34  ----------------------
% 2.36/1.35  Preprocessing        : 0.30
% 2.36/1.35  Parsing              : 0.15
% 2.36/1.35  CNF conversion       : 0.02
% 2.36/1.35  Main loop            : 0.26
% 2.36/1.35  Inferencing          : 0.09
% 2.36/1.35  Reduction            : 0.07
% 2.36/1.35  Demodulation         : 0.05
% 2.36/1.35  BG Simplification    : 0.02
% 2.36/1.35  Subsumption          : 0.06
% 2.36/1.35  Abstraction          : 0.02
% 2.36/1.35  MUC search           : 0.00
% 2.36/1.35  Cooper               : 0.00
% 2.36/1.35  Total                : 0.59
% 2.36/1.35  Index Insertion      : 0.00
% 2.36/1.35  Index Deletion       : 0.00
% 2.36/1.35  Index Matching       : 0.00
% 2.36/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
