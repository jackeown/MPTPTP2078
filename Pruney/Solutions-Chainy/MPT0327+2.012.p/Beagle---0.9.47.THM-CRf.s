%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:32 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   37 (  55 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   32 (  51 expanded)
%              Number of equality atoms :   20 (  38 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_41,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & r2_hidden(C,B) )
     => k2_xboole_0(k2_tarski(A,C),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_22,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10,plain,(
    ! [B_11,A_10] : k2_tarski(B_11,A_10) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_65,plain,(
    ! [A_23,B_24] : k3_tarski(k2_tarski(A_23,B_24)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_109,plain,(
    ! [B_28,A_29] : k3_tarski(k2_tarski(B_28,A_29)) = k2_xboole_0(A_29,B_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_65])).

tff(c_16,plain,(
    ! [A_15,B_16] : k3_tarski(k2_tarski(A_15,B_16)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_115,plain,(
    ! [B_28,A_29] : k2_xboole_0(B_28,A_29) = k2_xboole_0(A_29,B_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_16])).

tff(c_12,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_338,plain,(
    ! [A_44,C_45,B_46] :
      ( k2_xboole_0(k2_tarski(A_44,C_45),B_46) = B_46
      | ~ r2_hidden(C_45,B_46)
      | ~ r2_hidden(A_44,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_566,plain,(
    ! [A_52,B_53] :
      ( k2_xboole_0(k1_tarski(A_52),B_53) = B_53
      | ~ r2_hidden(A_52,B_53)
      | ~ r2_hidden(A_52,B_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_338])).

tff(c_621,plain,(
    ! [B_54,A_55] :
      ( k2_xboole_0(B_54,k1_tarski(A_55)) = B_54
      | ~ r2_hidden(A_55,B_54)
      | ~ r2_hidden(A_55,B_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_566])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_168,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k4_xboole_0('#skF_2',k1_tarski('#skF_1'))) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_20])).

tff(c_179,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_168])).

tff(c_180,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_179])).

tff(c_647,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_621,c_180])).

tff(c_687,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_647])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:40:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.35  
% 2.44/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.35  %$ r2_hidden > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 2.44/1.35  
% 2.44/1.35  %Foreground sorts:
% 2.44/1.35  
% 2.44/1.35  
% 2.44/1.35  %Background operators:
% 2.44/1.35  
% 2.44/1.35  
% 2.44/1.35  %Foreground operators:
% 2.44/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.44/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.44/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.44/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.44/1.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.44/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.44/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.44/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.44/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.44/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.44/1.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.44/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.44/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.44/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.44/1.35  
% 2.44/1.36  tff(f_52, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 2.44/1.36  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.44/1.36  tff(f_41, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.44/1.36  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.44/1.36  tff(f_47, axiom, (![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k2_xboole_0(k2_tarski(A, C), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 2.44/1.36  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.44/1.36  tff(c_22, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.44/1.36  tff(c_10, plain, (![B_11, A_10]: (k2_tarski(B_11, A_10)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.44/1.36  tff(c_65, plain, (![A_23, B_24]: (k3_tarski(k2_tarski(A_23, B_24))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.44/1.36  tff(c_109, plain, (![B_28, A_29]: (k3_tarski(k2_tarski(B_28, A_29))=k2_xboole_0(A_29, B_28))), inference(superposition, [status(thm), theory('equality')], [c_10, c_65])).
% 2.44/1.36  tff(c_16, plain, (![A_15, B_16]: (k3_tarski(k2_tarski(A_15, B_16))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.44/1.36  tff(c_115, plain, (![B_28, A_29]: (k2_xboole_0(B_28, A_29)=k2_xboole_0(A_29, B_28))), inference(superposition, [status(thm), theory('equality')], [c_109, c_16])).
% 2.44/1.36  tff(c_12, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.44/1.36  tff(c_338, plain, (![A_44, C_45, B_46]: (k2_xboole_0(k2_tarski(A_44, C_45), B_46)=B_46 | ~r2_hidden(C_45, B_46) | ~r2_hidden(A_44, B_46))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.44/1.36  tff(c_566, plain, (![A_52, B_53]: (k2_xboole_0(k1_tarski(A_52), B_53)=B_53 | ~r2_hidden(A_52, B_53) | ~r2_hidden(A_52, B_53))), inference(superposition, [status(thm), theory('equality')], [c_12, c_338])).
% 2.44/1.36  tff(c_621, plain, (![B_54, A_55]: (k2_xboole_0(B_54, k1_tarski(A_55))=B_54 | ~r2_hidden(A_55, B_54) | ~r2_hidden(A_55, B_54))), inference(superposition, [status(thm), theory('equality')], [c_115, c_566])).
% 2.44/1.36  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.44/1.36  tff(c_20, plain, (k2_xboole_0(k4_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.44/1.36  tff(c_168, plain, (k2_xboole_0(k1_tarski('#skF_1'), k4_xboole_0('#skF_2', k1_tarski('#skF_1')))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_115, c_20])).
% 2.44/1.36  tff(c_179, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4, c_168])).
% 2.44/1.36  tff(c_180, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_115, c_179])).
% 2.44/1.36  tff(c_647, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_621, c_180])).
% 2.44/1.36  tff(c_687, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_647])).
% 2.44/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.36  
% 2.44/1.36  Inference rules
% 2.44/1.36  ----------------------
% 2.44/1.36  #Ref     : 0
% 2.44/1.36  #Sup     : 169
% 2.44/1.36  #Fact    : 0
% 2.44/1.36  #Define  : 0
% 2.44/1.36  #Split   : 0
% 2.44/1.36  #Chain   : 0
% 2.44/1.36  #Close   : 0
% 2.44/1.36  
% 2.44/1.36  Ordering : KBO
% 2.44/1.36  
% 2.44/1.36  Simplification rules
% 2.44/1.36  ----------------------
% 2.44/1.36  #Subsume      : 4
% 2.44/1.36  #Demod        : 46
% 2.44/1.36  #Tautology    : 75
% 2.44/1.36  #SimpNegUnit  : 0
% 2.44/1.36  #BackRed      : 1
% 2.44/1.36  
% 2.44/1.36  #Partial instantiations: 0
% 2.44/1.36  #Strategies tried      : 1
% 2.44/1.36  
% 2.44/1.36  Timing (in seconds)
% 2.44/1.36  ----------------------
% 2.44/1.37  Preprocessing        : 0.30
% 2.44/1.37  Parsing              : 0.17
% 2.44/1.37  CNF conversion       : 0.02
% 2.44/1.37  Main loop            : 0.28
% 2.44/1.37  Inferencing          : 0.11
% 2.44/1.37  Reduction            : 0.11
% 2.44/1.37  Demodulation         : 0.09
% 2.44/1.37  BG Simplification    : 0.02
% 2.44/1.37  Subsumption          : 0.04
% 2.44/1.37  Abstraction          : 0.02
% 2.44/1.37  MUC search           : 0.00
% 2.44/1.37  Cooper               : 0.00
% 2.44/1.37  Total                : 0.61
% 2.44/1.37  Index Insertion      : 0.00
% 2.44/1.37  Index Deletion       : 0.00
% 2.44/1.37  Index Matching       : 0.00
% 2.44/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
