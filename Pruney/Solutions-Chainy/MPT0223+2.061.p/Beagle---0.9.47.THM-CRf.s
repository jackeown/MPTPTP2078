%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:24 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   42 (  56 expanded)
%              Number of leaves         :   22 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 (  74 expanded)
%              Number of equality atoms :   23 (  41 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_60,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

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
      ( r1_xboole_0(k1_tarski(A_21),B_22)
      | r2_hidden(A_21,B_22) ) ),
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

tff(c_129,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_38,c_125])).

tff(c_34,plain,(
    ! [A_16,B_17] : k1_enumset1(A_16,A_16,B_17) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_147,plain,(
    ! [E_54,C_55,B_56,A_57] :
      ( E_54 = C_55
      | E_54 = B_56
      | E_54 = A_57
      | ~ r2_hidden(E_54,k1_enumset1(A_57,B_56,C_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_166,plain,(
    ! [E_58,B_59,A_60] :
      ( E_58 = B_59
      | E_58 = A_60
      | E_58 = A_60
      | ~ r2_hidden(E_58,k2_tarski(A_60,B_59)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_147])).

tff(c_180,plain,(
    ! [E_61,A_62] :
      ( E_61 = A_62
      | E_61 = A_62
      | E_61 = A_62
      | ~ r2_hidden(E_61,k1_tarski(A_62)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_166])).

tff(c_186,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_129,c_180])).

tff(c_194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_40,c_40,c_186])).

tff(c_216,plain,(
    ! [C_67] : ~ r2_hidden(C_67,k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_221,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_81,c_216])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:49:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.21  
% 2.03/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.21  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.03/1.21  
% 2.03/1.21  %Foreground sorts:
% 2.03/1.21  
% 2.03/1.21  
% 2.03/1.21  %Background operators:
% 2.03/1.21  
% 2.03/1.21  
% 2.03/1.21  %Foreground operators:
% 2.03/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.03/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.03/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.03/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.03/1.21  tff('#skF_5', type, '#skF_5': $i).
% 2.03/1.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.03/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.03/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.03/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.21  tff('#skF_4', type, '#skF_4': $i).
% 2.03/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.03/1.21  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.03/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.03/1.21  
% 2.03/1.22  tff(f_58, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.03/1.22  tff(f_60, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.03/1.22  tff(f_56, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.03/1.22  tff(f_72, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 2.03/1.22  tff(f_67, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.03/1.22  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.03/1.22  tff(c_32, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.03/1.22  tff(c_60, plain, (![A_35, B_36]: (k1_enumset1(A_35, A_35, B_36)=k2_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.03/1.22  tff(c_14, plain, (![E_14, B_9, C_10]: (r2_hidden(E_14, k1_enumset1(E_14, B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.03/1.22  tff(c_78, plain, (![A_37, B_38]: (r2_hidden(A_37, k2_tarski(A_37, B_38)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_14])).
% 2.03/1.22  tff(c_81, plain, (![A_15]: (r2_hidden(A_15, k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_78])).
% 2.03/1.22  tff(c_40, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.03/1.22  tff(c_38, plain, (![A_21, B_22]: (r1_xboole_0(k1_tarski(A_21), B_22) | r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.03/1.22  tff(c_42, plain, (k3_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.03/1.22  tff(c_82, plain, (![A_39, B_40, C_41]: (~r1_xboole_0(A_39, B_40) | ~r2_hidden(C_41, k3_xboole_0(A_39, B_40)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.03/1.22  tff(c_85, plain, (![C_41]: (~r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5')) | ~r2_hidden(C_41, k1_tarski('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_42, c_82])).
% 2.03/1.22  tff(c_125, plain, (~r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))), inference(splitLeft, [status(thm)], [c_85])).
% 2.03/1.22  tff(c_129, plain, (r2_hidden('#skF_4', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_125])).
% 2.03/1.22  tff(c_34, plain, (![A_16, B_17]: (k1_enumset1(A_16, A_16, B_17)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.03/1.22  tff(c_147, plain, (![E_54, C_55, B_56, A_57]: (E_54=C_55 | E_54=B_56 | E_54=A_57 | ~r2_hidden(E_54, k1_enumset1(A_57, B_56, C_55)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.03/1.22  tff(c_166, plain, (![E_58, B_59, A_60]: (E_58=B_59 | E_58=A_60 | E_58=A_60 | ~r2_hidden(E_58, k2_tarski(A_60, B_59)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_147])).
% 2.03/1.22  tff(c_180, plain, (![E_61, A_62]: (E_61=A_62 | E_61=A_62 | E_61=A_62 | ~r2_hidden(E_61, k1_tarski(A_62)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_166])).
% 2.03/1.22  tff(c_186, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_129, c_180])).
% 2.03/1.22  tff(c_194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_40, c_40, c_186])).
% 2.03/1.22  tff(c_216, plain, (![C_67]: (~r2_hidden(C_67, k1_tarski('#skF_4')))), inference(splitRight, [status(thm)], [c_85])).
% 2.03/1.22  tff(c_221, plain, $false, inference(resolution, [status(thm)], [c_81, c_216])).
% 2.03/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.22  
% 2.03/1.22  Inference rules
% 2.03/1.22  ----------------------
% 2.03/1.22  #Ref     : 0
% 2.03/1.22  #Sup     : 40
% 2.03/1.22  #Fact    : 0
% 2.03/1.22  #Define  : 0
% 2.03/1.22  #Split   : 1
% 2.03/1.22  #Chain   : 0
% 2.03/1.22  #Close   : 0
% 2.03/1.22  
% 2.03/1.22  Ordering : KBO
% 2.03/1.22  
% 2.03/1.22  Simplification rules
% 2.03/1.22  ----------------------
% 2.03/1.22  #Subsume      : 0
% 2.03/1.22  #Demod        : 3
% 2.03/1.22  #Tautology    : 24
% 2.03/1.22  #SimpNegUnit  : 2
% 2.03/1.22  #BackRed      : 0
% 2.03/1.22  
% 2.03/1.22  #Partial instantiations: 0
% 2.03/1.22  #Strategies tried      : 1
% 2.03/1.22  
% 2.03/1.22  Timing (in seconds)
% 2.03/1.22  ----------------------
% 2.03/1.22  Preprocessing        : 0.30
% 2.03/1.22  Parsing              : 0.15
% 2.03/1.22  CNF conversion       : 0.02
% 2.03/1.22  Main loop            : 0.17
% 2.03/1.22  Inferencing          : 0.06
% 2.03/1.22  Reduction            : 0.05
% 2.03/1.22  Demodulation         : 0.04
% 2.03/1.22  BG Simplification    : 0.01
% 2.03/1.22  Subsumption          : 0.03
% 2.03/1.22  Abstraction          : 0.01
% 2.03/1.23  MUC search           : 0.00
% 2.03/1.23  Cooper               : 0.00
% 2.03/1.23  Total                : 0.50
% 2.03/1.23  Index Insertion      : 0.00
% 2.03/1.23  Index Deletion       : 0.00
% 2.03/1.23  Index Matching       : 0.00
% 2.03/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
