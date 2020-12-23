%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:18 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :   38 (  40 expanded)
%              Number of leaves         :   19 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :   39 (  43 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_41,plain,(
    ! [B_22,A_23] :
      ( r1_xboole_0(B_22,A_23)
      | ~ r1_xboole_0(A_23,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_50,plain,(
    r1_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_41])).

tff(c_69,plain,(
    ! [A_27,B_28] :
      ( k3_xboole_0(A_27,B_28) = k1_xboole_0
      | ~ r1_xboole_0(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_90,plain,(
    k3_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_69])).

tff(c_186,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k3_xboole_0(A_39,B_40)) = k4_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_216,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k4_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_186])).

tff(c_228,plain,(
    k4_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_216])).

tff(c_682,plain,(
    ! [A_68,B_69,C_70] : k4_xboole_0(k4_xboole_0(A_68,B_69),C_70) = k4_xboole_0(A_68,k2_xboole_0(B_69,C_70)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2693,plain,(
    ! [C_107] : k4_xboole_0('#skF_2',k2_xboole_0('#skF_1',C_107)) = k4_xboole_0('#skF_2',C_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_682])).

tff(c_22,plain,(
    ! [A_16,B_17] : r1_xboole_0(k4_xboole_0(A_16,B_17),B_17) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_524,plain,(
    ! [A_54,B_55,C_56] :
      ( r1_xboole_0(A_54,B_55)
      | ~ r1_xboole_0(A_54,k2_xboole_0(B_55,C_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_551,plain,(
    ! [A_57,B_58,C_59] : r1_xboole_0(k4_xboole_0(A_57,k2_xboole_0(B_58,C_59)),B_58) ),
    inference(resolution,[status(thm)],[c_22,c_524])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_571,plain,(
    ! [B_58,A_57,C_59] : r1_xboole_0(B_58,k4_xboole_0(A_57,k2_xboole_0(B_58,C_59))) ),
    inference(resolution,[status(thm)],[c_551,c_6])).

tff(c_2721,plain,(
    ! [C_107] : r1_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_107)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2693,c_571])).

tff(c_24,plain,(
    ~ r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2770,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2721,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:39:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.42/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.58  
% 3.42/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.58  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.42/1.58  
% 3.42/1.58  %Foreground sorts:
% 3.42/1.58  
% 3.42/1.58  
% 3.42/1.58  %Background operators:
% 3.42/1.58  
% 3.42/1.58  
% 3.42/1.58  %Foreground operators:
% 3.42/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.42/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.42/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.42/1.58  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.42/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.42/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.42/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.42/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.42/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.42/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.42/1.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.42/1.59  
% 3.42/1.59  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.42/1.59  tff(f_64, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_xboole_1)).
% 3.42/1.59  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.42/1.59  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.42/1.59  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 3.42/1.59  tff(f_37, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.42/1.59  tff(f_59, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.42/1.59  tff(f_57, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 3.42/1.59  tff(c_8, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.42/1.59  tff(c_26, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.42/1.59  tff(c_41, plain, (![B_22, A_23]: (r1_xboole_0(B_22, A_23) | ~r1_xboole_0(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.42/1.59  tff(c_50, plain, (r1_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_26, c_41])).
% 3.42/1.59  tff(c_69, plain, (![A_27, B_28]: (k3_xboole_0(A_27, B_28)=k1_xboole_0 | ~r1_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.42/1.59  tff(c_90, plain, (k3_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_69])).
% 3.42/1.59  tff(c_186, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k3_xboole_0(A_39, B_40))=k4_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.42/1.59  tff(c_216, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k4_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_90, c_186])).
% 3.42/1.59  tff(c_228, plain, (k4_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_216])).
% 3.42/1.59  tff(c_682, plain, (![A_68, B_69, C_70]: (k4_xboole_0(k4_xboole_0(A_68, B_69), C_70)=k4_xboole_0(A_68, k2_xboole_0(B_69, C_70)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.42/1.59  tff(c_2693, plain, (![C_107]: (k4_xboole_0('#skF_2', k2_xboole_0('#skF_1', C_107))=k4_xboole_0('#skF_2', C_107))), inference(superposition, [status(thm), theory('equality')], [c_228, c_682])).
% 3.42/1.59  tff(c_22, plain, (![A_16, B_17]: (r1_xboole_0(k4_xboole_0(A_16, B_17), B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.42/1.59  tff(c_524, plain, (![A_54, B_55, C_56]: (r1_xboole_0(A_54, B_55) | ~r1_xboole_0(A_54, k2_xboole_0(B_55, C_56)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.42/1.59  tff(c_551, plain, (![A_57, B_58, C_59]: (r1_xboole_0(k4_xboole_0(A_57, k2_xboole_0(B_58, C_59)), B_58))), inference(resolution, [status(thm)], [c_22, c_524])).
% 3.42/1.59  tff(c_6, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.42/1.59  tff(c_571, plain, (![B_58, A_57, C_59]: (r1_xboole_0(B_58, k4_xboole_0(A_57, k2_xboole_0(B_58, C_59))))), inference(resolution, [status(thm)], [c_551, c_6])).
% 3.42/1.59  tff(c_2721, plain, (![C_107]: (r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_107)))), inference(superposition, [status(thm), theory('equality')], [c_2693, c_571])).
% 3.42/1.59  tff(c_24, plain, (~r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.42/1.59  tff(c_2770, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2721, c_24])).
% 3.42/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.59  
% 3.42/1.59  Inference rules
% 3.42/1.59  ----------------------
% 3.42/1.59  #Ref     : 0
% 3.42/1.59  #Sup     : 690
% 3.42/1.59  #Fact    : 0
% 3.42/1.59  #Define  : 0
% 3.42/1.59  #Split   : 0
% 3.42/1.59  #Chain   : 0
% 3.42/1.59  #Close   : 0
% 3.42/1.59  
% 3.42/1.59  Ordering : KBO
% 3.42/1.59  
% 3.42/1.59  Simplification rules
% 3.42/1.59  ----------------------
% 3.42/1.59  #Subsume      : 1
% 3.42/1.59  #Demod        : 507
% 3.42/1.59  #Tautology    : 481
% 3.42/1.59  #SimpNegUnit  : 0
% 3.42/1.59  #BackRed      : 1
% 3.42/1.59  
% 3.42/1.59  #Partial instantiations: 0
% 3.42/1.59  #Strategies tried      : 1
% 3.42/1.59  
% 3.42/1.59  Timing (in seconds)
% 3.42/1.59  ----------------------
% 3.42/1.60  Preprocessing        : 0.28
% 3.42/1.60  Parsing              : 0.15
% 3.42/1.60  CNF conversion       : 0.02
% 3.42/1.60  Main loop            : 0.57
% 3.42/1.60  Inferencing          : 0.20
% 3.42/1.60  Reduction            : 0.21
% 3.42/1.60  Demodulation         : 0.17
% 3.42/1.60  BG Simplification    : 0.02
% 3.42/1.60  Subsumption          : 0.09
% 3.42/1.60  Abstraction          : 0.03
% 3.42/1.60  MUC search           : 0.00
% 3.42/1.60  Cooper               : 0.00
% 3.42/1.60  Total                : 0.87
% 3.42/1.60  Index Insertion      : 0.00
% 3.42/1.60  Index Deletion       : 0.00
% 3.42/1.60  Index Matching       : 0.00
% 3.42/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
