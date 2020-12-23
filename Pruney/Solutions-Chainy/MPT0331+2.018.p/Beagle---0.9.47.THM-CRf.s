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
% DateTime   : Thu Dec  3 09:54:47 EST 2020

% Result     : Theorem 23.87s
% Output     : CNFRefutation 23.87s
% Verified   : 
% Statistics : Number of formulae       :   38 (  40 expanded)
%              Number of leaves         :   26 (  28 expanded)
%              Depth                    :    5
%              Number of atoms          :   33 (  39 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r2_hidden(A,C)
          & ~ r2_hidden(B,C)
          & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C)
        & ~ r1_xboole_0(k2_tarski(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l168_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

tff(c_44,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_42,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_947,plain,(
    ! [A_102,B_103,C_104] :
      ( r1_xboole_0(k2_tarski(A_102,B_103),C_104)
      | r2_hidden(B_103,C_104)
      | r2_hidden(A_102,C_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6972,plain,(
    ! [C_194,A_195,B_196] :
      ( r1_xboole_0(C_194,k2_tarski(A_195,B_196))
      | r2_hidden(B_196,C_194)
      | r2_hidden(A_195,C_194) ) ),
    inference(resolution,[status(thm)],[c_947,c_6])).

tff(c_10,plain,(
    ! [A_9,B_10] : k4_xboole_0(k2_xboole_0(A_9,B_10),B_10) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(k2_xboole_0(A_15,B_16),B_16) = A_15
      | ~ r1_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_45,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(A_15,B_16) = A_15
      | ~ r1_xboole_0(A_15,B_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_16])).

tff(c_59357,plain,(
    ! [C_387,A_388,B_389] :
      ( k4_xboole_0(C_387,k2_tarski(A_388,B_389)) = C_387
      | r2_hidden(B_389,C_387)
      | r2_hidden(A_388,C_387) ) ),
    inference(resolution,[status(thm)],[c_6972,c_45])).

tff(c_40,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_59428,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_59357,c_40])).

tff(c_59476,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_59428])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:22:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.87/16.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.87/16.36  
% 23.87/16.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.87/16.36  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 23.87/16.36  
% 23.87/16.36  %Foreground sorts:
% 23.87/16.36  
% 23.87/16.36  
% 23.87/16.36  %Background operators:
% 23.87/16.36  
% 23.87/16.36  
% 23.87/16.36  %Foreground operators:
% 23.87/16.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.87/16.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 23.87/16.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 23.87/16.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 23.87/16.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 23.87/16.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 23.87/16.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 23.87/16.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 23.87/16.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 23.87/16.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 23.87/16.36  tff('#skF_2', type, '#skF_2': $i).
% 23.87/16.36  tff('#skF_3', type, '#skF_3': $i).
% 23.87/16.36  tff('#skF_1', type, '#skF_1': $i).
% 23.87/16.36  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 23.87/16.36  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 23.87/16.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.87/16.36  tff(k3_tarski, type, k3_tarski: $i > $i).
% 23.87/16.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.87/16.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 23.87/16.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 23.87/16.36  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 23.87/16.36  
% 23.87/16.37  tff(f_86, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 23.87/16.37  tff(f_73, axiom, (![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~r1_xboole_0(k2_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l168_zfmisc_1)).
% 23.87/16.37  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 23.87/16.37  tff(f_37, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 23.87/16.37  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 23.87/16.37  tff(c_44, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 23.87/16.37  tff(c_42, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 23.87/16.37  tff(c_947, plain, (![A_102, B_103, C_104]: (r1_xboole_0(k2_tarski(A_102, B_103), C_104) | r2_hidden(B_103, C_104) | r2_hidden(A_102, C_104))), inference(cnfTransformation, [status(thm)], [f_73])).
% 23.87/16.37  tff(c_6, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 23.87/16.37  tff(c_6972, plain, (![C_194, A_195, B_196]: (r1_xboole_0(C_194, k2_tarski(A_195, B_196)) | r2_hidden(B_196, C_194) | r2_hidden(A_195, C_194))), inference(resolution, [status(thm)], [c_947, c_6])).
% 23.87/16.37  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(k2_xboole_0(A_9, B_10), B_10)=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 23.87/16.37  tff(c_16, plain, (![A_15, B_16]: (k4_xboole_0(k2_xboole_0(A_15, B_16), B_16)=A_15 | ~r1_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 23.87/16.37  tff(c_45, plain, (![A_15, B_16]: (k4_xboole_0(A_15, B_16)=A_15 | ~r1_xboole_0(A_15, B_16))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_16])).
% 23.87/16.37  tff(c_59357, plain, (![C_387, A_388, B_389]: (k4_xboole_0(C_387, k2_tarski(A_388, B_389))=C_387 | r2_hidden(B_389, C_387) | r2_hidden(A_388, C_387))), inference(resolution, [status(thm)], [c_6972, c_45])).
% 23.87/16.37  tff(c_40, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_86])).
% 23.87/16.37  tff(c_59428, plain, (r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_59357, c_40])).
% 23.87/16.37  tff(c_59476, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_59428])).
% 23.87/16.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.87/16.37  
% 23.87/16.37  Inference rules
% 23.87/16.37  ----------------------
% 23.87/16.37  #Ref     : 0
% 23.87/16.37  #Sup     : 15689
% 23.87/16.37  #Fact    : 0
% 23.87/16.37  #Define  : 0
% 23.87/16.37  #Split   : 0
% 23.87/16.37  #Chain   : 0
% 23.87/16.37  #Close   : 0
% 23.87/16.37  
% 23.87/16.37  Ordering : KBO
% 23.87/16.37  
% 23.87/16.37  Simplification rules
% 23.87/16.37  ----------------------
% 23.87/16.37  #Subsume      : 859
% 23.87/16.37  #Demod        : 23295
% 23.87/16.37  #Tautology    : 5368
% 23.87/16.37  #SimpNegUnit  : 1
% 23.87/16.37  #BackRed      : 1
% 23.87/16.37  
% 23.87/16.37  #Partial instantiations: 0
% 23.87/16.37  #Strategies tried      : 1
% 23.87/16.37  
% 23.87/16.37  Timing (in seconds)
% 23.87/16.37  ----------------------
% 23.87/16.37  Preprocessing        : 0.32
% 23.87/16.38  Parsing              : 0.17
% 23.87/16.38  CNF conversion       : 0.02
% 23.87/16.38  Main loop            : 15.30
% 23.87/16.38  Inferencing          : 1.55
% 23.87/16.38  Reduction            : 11.49
% 23.87/16.38  Demodulation         : 11.05
% 23.87/16.38  BG Simplification    : 0.28
% 23.87/16.38  Subsumption          : 1.61
% 23.87/16.38  Abstraction          : 0.48
% 23.87/16.38  MUC search           : 0.00
% 23.87/16.38  Cooper               : 0.00
% 23.87/16.38  Total                : 15.64
% 23.87/16.38  Index Insertion      : 0.00
% 23.87/16.38  Index Deletion       : 0.00
% 23.87/16.38  Index Matching       : 0.00
% 23.87/16.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
