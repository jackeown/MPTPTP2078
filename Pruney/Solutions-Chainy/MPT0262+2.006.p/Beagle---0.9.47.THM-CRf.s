%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:13 EST 2020

% Result     : Theorem 5.50s
% Output     : CNFRefutation 5.82s
% Verified   : 
% Statistics : Number of formulae       :   35 (  46 expanded)
%              Number of leaves         :   18 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   47 (  68 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r2_hidden(A,B)
          & ~ r2_hidden(C,B)
          & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_24,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_22,plain,(
    ~ r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_156,plain,(
    ! [A_54,B_55] :
      ( k4_xboole_0(k1_tarski(A_54),B_55) = k1_tarski(A_54)
      | r2_hidden(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_xboole_0(k4_xboole_0(A_6,B_7),B_7) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_35,plain,(
    ! [B_16,A_17] :
      ( r1_xboole_0(B_16,A_17)
      | ~ r1_xboole_0(A_17,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_38,plain,(
    ! [B_7,A_6] : r1_xboole_0(B_7,k4_xboole_0(A_6,B_7)) ),
    inference(resolution,[status(thm)],[c_10,c_35])).

tff(c_197,plain,(
    ! [B_55,A_54] :
      ( r1_xboole_0(B_55,k1_tarski(A_54))
      | r2_hidden(A_54,B_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_38])).

tff(c_12,plain,(
    ! [A_8,B_9] : k2_xboole_0(k1_tarski(A_8),k1_tarski(B_9)) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_227,plain,(
    ! [A_60,C_61,B_62] :
      ( ~ r1_xboole_0(A_60,C_61)
      | ~ r1_xboole_0(A_60,B_62)
      | r1_xboole_0(A_60,k2_xboole_0(B_62,C_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_531,plain,(
    ! [A_124,B_125,A_126] :
      ( ~ r1_xboole_0(A_124,k1_tarski(B_125))
      | ~ r1_xboole_0(A_124,k1_tarski(A_126))
      | r1_xboole_0(A_124,k2_tarski(A_126,B_125)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_227])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_611,plain,(
    ! [A_149,B_150,A_151] :
      ( r1_xboole_0(k2_tarski(A_149,B_150),A_151)
      | ~ r1_xboole_0(A_151,k1_tarski(B_150))
      | ~ r1_xboole_0(A_151,k1_tarski(A_149)) ) ),
    inference(resolution,[status(thm)],[c_531,c_2])).

tff(c_1537,plain,(
    ! [A_335,A_336,B_337] :
      ( r1_xboole_0(k2_tarski(A_335,A_336),B_337)
      | ~ r1_xboole_0(B_337,k1_tarski(A_335))
      | r2_hidden(A_336,B_337) ) ),
    inference(resolution,[status(thm)],[c_197,c_611])).

tff(c_1654,plain,(
    ! [A_338,A_339,B_340] :
      ( r1_xboole_0(k2_tarski(A_338,A_339),B_340)
      | r2_hidden(A_339,B_340)
      | r2_hidden(A_338,B_340) ) ),
    inference(resolution,[status(thm)],[c_197,c_1537])).

tff(c_20,plain,(
    ~ r1_xboole_0(k2_tarski('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1685,plain,
    ( r2_hidden('#skF_3','#skF_2')
    | r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_1654,c_20])).

tff(c_1701,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_1685])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:12:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.50/2.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.50/2.38  
% 5.50/2.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.50/2.38  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 5.50/2.38  
% 5.50/2.38  %Foreground sorts:
% 5.50/2.38  
% 5.50/2.38  
% 5.50/2.38  %Background operators:
% 5.50/2.38  
% 5.50/2.38  
% 5.50/2.38  %Foreground operators:
% 5.50/2.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.50/2.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.50/2.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.50/2.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.50/2.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.50/2.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.50/2.38  tff('#skF_2', type, '#skF_2': $i).
% 5.50/2.38  tff('#skF_3', type, '#skF_3': $i).
% 5.50/2.38  tff('#skF_1', type, '#skF_1': $i).
% 5.50/2.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.50/2.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.50/2.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.50/2.38  
% 5.82/2.40  tff(f_67, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 5.82/2.40  tff(f_56, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 5.82/2.40  tff(f_47, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 5.82/2.40  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 5.82/2.40  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 5.82/2.40  tff(f_45, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 5.82/2.40  tff(c_24, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.82/2.40  tff(c_22, plain, (~r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.82/2.40  tff(c_156, plain, (![A_54, B_55]: (k4_xboole_0(k1_tarski(A_54), B_55)=k1_tarski(A_54) | r2_hidden(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.82/2.40  tff(c_10, plain, (![A_6, B_7]: (r1_xboole_0(k4_xboole_0(A_6, B_7), B_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.82/2.40  tff(c_35, plain, (![B_16, A_17]: (r1_xboole_0(B_16, A_17) | ~r1_xboole_0(A_17, B_16))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.82/2.40  tff(c_38, plain, (![B_7, A_6]: (r1_xboole_0(B_7, k4_xboole_0(A_6, B_7)))), inference(resolution, [status(thm)], [c_10, c_35])).
% 5.82/2.40  tff(c_197, plain, (![B_55, A_54]: (r1_xboole_0(B_55, k1_tarski(A_54)) | r2_hidden(A_54, B_55))), inference(superposition, [status(thm), theory('equality')], [c_156, c_38])).
% 5.82/2.40  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(k1_tarski(A_8), k1_tarski(B_9))=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.82/2.40  tff(c_227, plain, (![A_60, C_61, B_62]: (~r1_xboole_0(A_60, C_61) | ~r1_xboole_0(A_60, B_62) | r1_xboole_0(A_60, k2_xboole_0(B_62, C_61)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.82/2.40  tff(c_531, plain, (![A_124, B_125, A_126]: (~r1_xboole_0(A_124, k1_tarski(B_125)) | ~r1_xboole_0(A_124, k1_tarski(A_126)) | r1_xboole_0(A_124, k2_tarski(A_126, B_125)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_227])).
% 5.82/2.40  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.82/2.40  tff(c_611, plain, (![A_149, B_150, A_151]: (r1_xboole_0(k2_tarski(A_149, B_150), A_151) | ~r1_xboole_0(A_151, k1_tarski(B_150)) | ~r1_xboole_0(A_151, k1_tarski(A_149)))), inference(resolution, [status(thm)], [c_531, c_2])).
% 5.82/2.40  tff(c_1537, plain, (![A_335, A_336, B_337]: (r1_xboole_0(k2_tarski(A_335, A_336), B_337) | ~r1_xboole_0(B_337, k1_tarski(A_335)) | r2_hidden(A_336, B_337))), inference(resolution, [status(thm)], [c_197, c_611])).
% 5.82/2.40  tff(c_1654, plain, (![A_338, A_339, B_340]: (r1_xboole_0(k2_tarski(A_338, A_339), B_340) | r2_hidden(A_339, B_340) | r2_hidden(A_338, B_340))), inference(resolution, [status(thm)], [c_197, c_1537])).
% 5.82/2.40  tff(c_20, plain, (~r1_xboole_0(k2_tarski('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.82/2.40  tff(c_1685, plain, (r2_hidden('#skF_3', '#skF_2') | r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_1654, c_20])).
% 5.82/2.40  tff(c_1701, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_1685])).
% 5.82/2.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.82/2.40  
% 5.82/2.40  Inference rules
% 5.82/2.40  ----------------------
% 5.82/2.40  #Ref     : 0
% 5.82/2.40  #Sup     : 409
% 5.82/2.40  #Fact    : 0
% 5.82/2.40  #Define  : 0
% 5.82/2.40  #Split   : 0
% 5.82/2.40  #Chain   : 0
% 5.82/2.40  #Close   : 0
% 5.82/2.40  
% 5.82/2.40  Ordering : KBO
% 5.82/2.40  
% 5.82/2.40  Simplification rules
% 5.82/2.40  ----------------------
% 5.82/2.40  #Subsume      : 26
% 5.82/2.40  #Demod        : 54
% 5.82/2.40  #Tautology    : 64
% 5.82/2.40  #SimpNegUnit  : 1
% 5.82/2.40  #BackRed      : 0
% 5.82/2.40  
% 5.82/2.40  #Partial instantiations: 0
% 5.82/2.40  #Strategies tried      : 1
% 5.82/2.40  
% 5.82/2.40  Timing (in seconds)
% 5.82/2.40  ----------------------
% 5.83/2.40  Preprocessing        : 0.47
% 5.83/2.40  Parsing              : 0.25
% 5.83/2.40  CNF conversion       : 0.03
% 5.83/2.40  Main loop            : 1.13
% 5.83/2.41  Inferencing          : 0.38
% 5.83/2.41  Reduction            : 0.35
% 5.83/2.41  Demodulation         : 0.27
% 5.83/2.41  BG Simplification    : 0.04
% 5.83/2.41  Subsumption          : 0.28
% 5.83/2.41  Abstraction          : 0.04
% 5.83/2.41  MUC search           : 0.00
% 5.83/2.41  Cooper               : 0.00
% 5.83/2.41  Total                : 1.63
% 5.83/2.41  Index Insertion      : 0.00
% 5.83/2.41  Index Deletion       : 0.00
% 5.83/2.41  Index Matching       : 0.00
% 5.83/2.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
