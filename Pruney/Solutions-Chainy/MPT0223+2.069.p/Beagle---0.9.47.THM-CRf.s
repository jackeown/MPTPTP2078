%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:25 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   37 (  43 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :    5
%              Number of atoms          :   33 (  46 expanded)
%              Number of equality atoms :   15 (  20 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_58,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_60,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_32,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_60,plain,(
    ! [A_35,B_36] : k1_enumset1(A_35,A_35,B_36) = k2_tarski(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14,plain,(
    ! [E_14,B_9,C_10] : r2_hidden(E_14,k1_enumset1(E_14,B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_78,plain,(
    ! [A_37,B_38] : r2_hidden(A_37,k2_tarski(A_37,B_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_14])).

tff(c_81,plain,(
    ! [A_15] : r2_hidden(A_15,k1_tarski(A_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_78])).

tff(c_40,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_38,plain,(
    ! [A_21,B_22] :
      ( r1_xboole_0(k1_tarski(A_21),k1_tarski(B_22))
      | B_22 = A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_42,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_82,plain,(
    ! [A_39,B_40,C_41] :
      ( ~ r1_xboole_0(A_39,B_40)
      | ~ r2_hidden(C_41,k3_xboole_0(A_39,B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_85,plain,(
    ! [C_41] :
      ( ~ r1_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5'))
      | ~ r2_hidden(C_41,k1_tarski('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_82])).

tff(c_125,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_128,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_125])).

tff(c_132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_128])).

tff(c_135,plain,(
    ! [C_52] : ~ r2_hidden(C_52,k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_140,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_81,c_135])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:08:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.20  
% 1.98/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.20  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.98/1.20  
% 1.98/1.20  %Foreground sorts:
% 1.98/1.20  
% 1.98/1.20  
% 1.98/1.20  %Background operators:
% 1.98/1.20  
% 1.98/1.20  
% 1.98/1.20  %Foreground operators:
% 1.98/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.98/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.98/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.98/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.98/1.20  tff('#skF_5', type, '#skF_5': $i).
% 1.98/1.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 1.98/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.98/1.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.98/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.98/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.98/1.20  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 1.98/1.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.98/1.20  
% 1.98/1.21  tff(f_58, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.98/1.21  tff(f_60, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.98/1.21  tff(f_56, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 1.98/1.21  tff(f_72, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 1.98/1.21  tff(f_67, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 1.98/1.21  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.98/1.21  tff(c_32, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.98/1.21  tff(c_60, plain, (![A_35, B_36]: (k1_enumset1(A_35, A_35, B_36)=k2_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.98/1.21  tff(c_14, plain, (![E_14, B_9, C_10]: (r2_hidden(E_14, k1_enumset1(E_14, B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.98/1.21  tff(c_78, plain, (![A_37, B_38]: (r2_hidden(A_37, k2_tarski(A_37, B_38)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_14])).
% 1.98/1.21  tff(c_81, plain, (![A_15]: (r2_hidden(A_15, k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_78])).
% 1.98/1.21  tff(c_40, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.98/1.21  tff(c_38, plain, (![A_21, B_22]: (r1_xboole_0(k1_tarski(A_21), k1_tarski(B_22)) | B_22=A_21)), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.98/1.21  tff(c_42, plain, (k3_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.98/1.21  tff(c_82, plain, (![A_39, B_40, C_41]: (~r1_xboole_0(A_39, B_40) | ~r2_hidden(C_41, k3_xboole_0(A_39, B_40)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.98/1.21  tff(c_85, plain, (![C_41]: (~r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5')) | ~r2_hidden(C_41, k1_tarski('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_42, c_82])).
% 1.98/1.21  tff(c_125, plain, (~r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))), inference(splitLeft, [status(thm)], [c_85])).
% 1.98/1.21  tff(c_128, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_38, c_125])).
% 1.98/1.21  tff(c_132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_128])).
% 1.98/1.21  tff(c_135, plain, (![C_52]: (~r2_hidden(C_52, k1_tarski('#skF_4')))), inference(splitRight, [status(thm)], [c_85])).
% 1.98/1.21  tff(c_140, plain, $false, inference(resolution, [status(thm)], [c_81, c_135])).
% 1.98/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.21  
% 1.98/1.21  Inference rules
% 1.98/1.21  ----------------------
% 1.98/1.21  #Ref     : 0
% 1.98/1.21  #Sup     : 22
% 1.98/1.21  #Fact    : 0
% 1.98/1.21  #Define  : 0
% 1.98/1.21  #Split   : 1
% 1.98/1.21  #Chain   : 0
% 1.98/1.21  #Close   : 0
% 1.98/1.21  
% 1.98/1.21  Ordering : KBO
% 1.98/1.21  
% 1.98/1.21  Simplification rules
% 1.98/1.21  ----------------------
% 1.98/1.21  #Subsume      : 0
% 1.98/1.21  #Demod        : 2
% 1.98/1.21  #Tautology    : 13
% 1.98/1.21  #SimpNegUnit  : 1
% 1.98/1.21  #BackRed      : 0
% 1.98/1.21  
% 1.98/1.21  #Partial instantiations: 0
% 1.98/1.21  #Strategies tried      : 1
% 1.98/1.21  
% 1.98/1.21  Timing (in seconds)
% 1.98/1.21  ----------------------
% 1.98/1.22  Preprocessing        : 0.32
% 1.98/1.22  Parsing              : 0.16
% 1.98/1.22  CNF conversion       : 0.02
% 1.98/1.22  Main loop            : 0.14
% 1.98/1.22  Inferencing          : 0.04
% 1.98/1.22  Reduction            : 0.04
% 1.98/1.22  Demodulation         : 0.03
% 1.98/1.22  BG Simplification    : 0.01
% 1.98/1.22  Subsumption          : 0.03
% 1.98/1.22  Abstraction          : 0.01
% 1.98/1.22  MUC search           : 0.00
% 1.98/1.22  Cooper               : 0.00
% 1.98/1.22  Total                : 0.48
% 1.98/1.22  Index Insertion      : 0.00
% 1.98/1.22  Index Deletion       : 0.00
% 1.98/1.22  Index Matching       : 0.00
% 1.98/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
