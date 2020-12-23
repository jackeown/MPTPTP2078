%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:29 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   28 (  32 expanded)
%              Number of leaves         :   13 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :   41 (  56 expanded)
%              Number of equality atoms :    8 (  11 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(B,C) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_47,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(c_10,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_35,plain,(
    ! [A_10,C_11,B_12] :
      ( r1_xboole_0(A_10,C_11)
      | ~ r1_xboole_0(B_12,C_11)
      | ~ r1_tarski(A_10,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_45,plain,(
    ! [A_13] :
      ( r1_xboole_0(A_13,'#skF_3')
      | ~ r1_tarski(A_13,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_12,c_35])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_71,plain,(
    ! [A_15] :
      ( r1_xboole_0('#skF_3',A_15)
      | ~ r1_tarski(A_15,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_45,c_2])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,C_5)
      | ~ r1_xboole_0(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_151,plain,(
    ! [A_26,A_27] :
      ( r1_xboole_0(A_26,A_27)
      | ~ r1_tarski(A_26,'#skF_3')
      | ~ r1_tarski(A_27,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_71,c_4])).

tff(c_8,plain,(
    ! [A_6] :
      ( ~ r1_xboole_0(A_6,A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_163,plain,(
    ! [A_28] :
      ( k1_xboole_0 = A_28
      | ~ r1_tarski(A_28,'#skF_3')
      | ~ r1_tarski(A_28,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_151,c_8])).

tff(c_166,plain,
    ( k1_xboole_0 = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_163])).

tff(c_169,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_166])).

tff(c_171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_169])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:30:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.58  
% 2.20/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.58  %$ r1_xboole_0 > r1_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.20/1.58  
% 2.20/1.58  %Foreground sorts:
% 2.20/1.58  
% 2.20/1.58  
% 2.20/1.58  %Background operators:
% 2.20/1.58  
% 2.20/1.58  
% 2.20/1.58  %Foreground operators:
% 2.20/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.20/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.20/1.58  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.20/1.58  tff('#skF_2', type, '#skF_2': $i).
% 2.20/1.58  tff('#skF_3', type, '#skF_3': $i).
% 2.20/1.58  tff('#skF_1', type, '#skF_1': $i).
% 2.20/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.58  
% 2.20/1.60  tff(f_56, negated_conjecture, ~(![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_xboole_1)).
% 2.20/1.60  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.20/1.60  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.20/1.60  tff(f_47, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.20/1.60  tff(c_10, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.20/1.60  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.20/1.60  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.20/1.60  tff(c_12, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.20/1.60  tff(c_35, plain, (![A_10, C_11, B_12]: (r1_xboole_0(A_10, C_11) | ~r1_xboole_0(B_12, C_11) | ~r1_tarski(A_10, B_12))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.20/1.60  tff(c_45, plain, (![A_13]: (r1_xboole_0(A_13, '#skF_3') | ~r1_tarski(A_13, '#skF_2'))), inference(resolution, [status(thm)], [c_12, c_35])).
% 2.20/1.60  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.20/1.60  tff(c_71, plain, (![A_15]: (r1_xboole_0('#skF_3', A_15) | ~r1_tarski(A_15, '#skF_2'))), inference(resolution, [status(thm)], [c_45, c_2])).
% 2.20/1.60  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, C_5) | ~r1_xboole_0(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.20/1.60  tff(c_151, plain, (![A_26, A_27]: (r1_xboole_0(A_26, A_27) | ~r1_tarski(A_26, '#skF_3') | ~r1_tarski(A_27, '#skF_2'))), inference(resolution, [status(thm)], [c_71, c_4])).
% 2.20/1.60  tff(c_8, plain, (![A_6]: (~r1_xboole_0(A_6, A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.20/1.60  tff(c_163, plain, (![A_28]: (k1_xboole_0=A_28 | ~r1_tarski(A_28, '#skF_3') | ~r1_tarski(A_28, '#skF_2'))), inference(resolution, [status(thm)], [c_151, c_8])).
% 2.20/1.60  tff(c_166, plain, (k1_xboole_0='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_16, c_163])).
% 2.20/1.60  tff(c_169, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_166])).
% 2.20/1.60  tff(c_171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_169])).
% 2.20/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.60  
% 2.20/1.60  Inference rules
% 2.20/1.60  ----------------------
% 2.20/1.60  #Ref     : 0
% 2.20/1.60  #Sup     : 36
% 2.20/1.60  #Fact    : 0
% 2.20/1.60  #Define  : 0
% 2.20/1.60  #Split   : 5
% 2.20/1.60  #Chain   : 0
% 2.20/1.60  #Close   : 0
% 2.20/1.60  
% 2.20/1.60  Ordering : KBO
% 2.20/1.60  
% 2.20/1.60  Simplification rules
% 2.20/1.60  ----------------------
% 2.20/1.60  #Subsume      : 7
% 2.20/1.60  #Demod        : 3
% 2.20/1.60  #Tautology    : 5
% 2.20/1.60  #SimpNegUnit  : 1
% 2.20/1.60  #BackRed      : 0
% 2.20/1.60  
% 2.20/1.60  #Partial instantiations: 0
% 2.20/1.60  #Strategies tried      : 1
% 2.20/1.60  
% 2.20/1.60  Timing (in seconds)
% 2.20/1.60  ----------------------
% 2.20/1.61  Preprocessing        : 0.42
% 2.20/1.61  Parsing              : 0.22
% 2.20/1.61  CNF conversion       : 0.03
% 2.20/1.61  Main loop            : 0.28
% 2.20/1.61  Inferencing          : 0.10
% 2.20/1.61  Reduction            : 0.07
% 2.20/1.61  Demodulation         : 0.05
% 2.20/1.61  BG Simplification    : 0.02
% 2.20/1.61  Subsumption          : 0.07
% 2.20/1.61  Abstraction          : 0.01
% 2.20/1.61  MUC search           : 0.00
% 2.20/1.61  Cooper               : 0.00
% 2.20/1.61  Total                : 0.74
% 2.20/1.61  Index Insertion      : 0.00
% 2.20/1.61  Index Deletion       : 0.00
% 2.20/1.61  Index Matching       : 0.00
% 2.20/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
