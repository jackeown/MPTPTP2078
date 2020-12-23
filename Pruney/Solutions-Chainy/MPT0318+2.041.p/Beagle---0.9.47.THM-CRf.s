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
% DateTime   : Thu Dec  3 09:54:07 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   39 (  67 expanded)
%              Number of leaves         :   17 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   43 ( 107 expanded)
%              Number of equality atoms :   33 (  97 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(c_12,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18,plain,
    ( k2_zfmisc_1('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_85,plain,(
    k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( k1_xboole_0 = B_6
      | k1_xboole_0 = A_5
      | k2_zfmisc_1(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_89,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_8])).

tff(c_94,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_89])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r2_hidden(B_4,A_3)
      | k3_xboole_0(A_3,k1_tarski(B_4)) != k1_tarski(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_101,plain,(
    ! [A_3] :
      ( r2_hidden('#skF_2',A_3)
      | k3_xboole_0(A_3,k1_xboole_0) != k1_tarski('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_6])).

tff(c_111,plain,(
    ! [A_3] : r2_hidden('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_2,c_101])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [B_8,A_7] :
      ( ~ r2_hidden(B_8,A_7)
      | k4_xboole_0(A_7,k1_tarski(B_8)) != A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_104,plain,(
    ! [A_7] :
      ( ~ r2_hidden('#skF_2',A_7)
      | k4_xboole_0(A_7,k1_xboole_0) != A_7 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_14])).

tff(c_113,plain,(
    ! [A_7] : ~ r2_hidden('#skF_2',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_104])).

tff(c_118,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_113])).

tff(c_119,plain,(
    k2_zfmisc_1('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_124,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_8])).

tff(c_129,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_124])).

tff(c_120,plain,(
    k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_131,plain,(
    k2_zfmisc_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_120])).

tff(c_135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_131])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 20:46:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.14  
% 1.67/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.14  %$ r2_hidden > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.67/1.14  
% 1.67/1.14  %Foreground sorts:
% 1.67/1.14  
% 1.67/1.14  
% 1.67/1.14  %Background operators:
% 1.67/1.14  
% 1.67/1.14  
% 1.67/1.14  %Foreground operators:
% 1.67/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.67/1.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.67/1.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.67/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.67/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.67/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.67/1.14  
% 1.67/1.15  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.67/1.15  tff(f_54, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 1.67/1.15  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.67/1.15  tff(f_33, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 1.67/1.15  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.67/1.15  tff(f_44, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.67/1.15  tff(c_12, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.67/1.15  tff(c_20, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.67/1.15  tff(c_18, plain, (k2_zfmisc_1('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.67/1.15  tff(c_85, plain, (k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_18])).
% 1.67/1.15  tff(c_8, plain, (![B_6, A_5]: (k1_xboole_0=B_6 | k1_xboole_0=A_5 | k2_zfmisc_1(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.67/1.15  tff(c_89, plain, (k1_xboole_0='#skF_1' | k1_tarski('#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_85, c_8])).
% 1.67/1.15  tff(c_94, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_20, c_89])).
% 1.67/1.15  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.67/1.15  tff(c_6, plain, (![B_4, A_3]: (r2_hidden(B_4, A_3) | k3_xboole_0(A_3, k1_tarski(B_4))!=k1_tarski(B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.67/1.15  tff(c_101, plain, (![A_3]: (r2_hidden('#skF_2', A_3) | k3_xboole_0(A_3, k1_xboole_0)!=k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_94, c_6])).
% 1.67/1.15  tff(c_111, plain, (![A_3]: (r2_hidden('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_2, c_101])).
% 1.67/1.15  tff(c_4, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.67/1.15  tff(c_14, plain, (![B_8, A_7]: (~r2_hidden(B_8, A_7) | k4_xboole_0(A_7, k1_tarski(B_8))!=A_7)), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.67/1.15  tff(c_104, plain, (![A_7]: (~r2_hidden('#skF_2', A_7) | k4_xboole_0(A_7, k1_xboole_0)!=A_7)), inference(superposition, [status(thm), theory('equality')], [c_94, c_14])).
% 1.67/1.15  tff(c_113, plain, (![A_7]: (~r2_hidden('#skF_2', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_104])).
% 1.67/1.15  tff(c_118, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_111, c_113])).
% 1.67/1.15  tff(c_119, plain, (k2_zfmisc_1('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_18])).
% 1.67/1.15  tff(c_124, plain, (k1_tarski('#skF_2')=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_119, c_8])).
% 1.67/1.15  tff(c_129, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_20, c_124])).
% 1.67/1.15  tff(c_120, plain, (k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_18])).
% 1.67/1.15  tff(c_131, plain, (k2_zfmisc_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_129, c_120])).
% 1.67/1.15  tff(c_135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_131])).
% 1.67/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.15  
% 1.67/1.15  Inference rules
% 1.67/1.15  ----------------------
% 1.67/1.15  #Ref     : 0
% 1.67/1.15  #Sup     : 26
% 1.67/1.15  #Fact    : 0
% 1.67/1.15  #Define  : 0
% 1.67/1.15  #Split   : 1
% 1.67/1.15  #Chain   : 0
% 1.67/1.15  #Close   : 0
% 1.67/1.15  
% 1.67/1.15  Ordering : KBO
% 1.67/1.15  
% 1.67/1.15  Simplification rules
% 1.67/1.15  ----------------------
% 1.67/1.15  #Subsume      : 0
% 1.67/1.15  #Demod        : 10
% 1.67/1.15  #Tautology    : 23
% 1.67/1.15  #SimpNegUnit  : 2
% 1.67/1.15  #BackRed      : 3
% 1.67/1.15  
% 1.67/1.15  #Partial instantiations: 0
% 1.67/1.15  #Strategies tried      : 1
% 1.67/1.15  
% 1.67/1.15  Timing (in seconds)
% 1.67/1.15  ----------------------
% 1.67/1.16  Preprocessing        : 0.29
% 1.67/1.16  Parsing              : 0.15
% 1.67/1.16  CNF conversion       : 0.02
% 1.67/1.16  Main loop            : 0.11
% 1.67/1.16  Inferencing          : 0.04
% 1.67/1.16  Reduction            : 0.04
% 1.67/1.16  Demodulation         : 0.02
% 1.67/1.16  BG Simplification    : 0.01
% 1.67/1.16  Subsumption          : 0.02
% 1.67/1.16  Abstraction          : 0.01
% 1.67/1.16  MUC search           : 0.00
% 1.67/1.16  Cooper               : 0.00
% 1.67/1.16  Total                : 0.43
% 1.67/1.16  Index Insertion      : 0.00
% 1.67/1.16  Index Deletion       : 0.00
% 1.67/1.16  Index Matching       : 0.00
% 1.67/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
