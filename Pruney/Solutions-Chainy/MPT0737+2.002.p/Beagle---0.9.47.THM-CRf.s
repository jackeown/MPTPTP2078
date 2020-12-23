%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:04 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   38 (  56 expanded)
%              Number of leaves         :   18 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   66 ( 108 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(r3_xboole_0,type,(
    r3_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r3_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        | r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_xboole_0)).

tff(f_73,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => r3_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_ordinal1)).

tff(f_43,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_65,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    ! [B_21,A_22] :
      ( ~ r1_tarski(B_21,A_22)
      | r3_xboole_0(A_22,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26,plain,(
    ~ r3_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_62,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_26])).

tff(c_30,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_28,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_33,plain,(
    ! [A_15] :
      ( v1_ordinal1(A_15)
      | ~ v3_ordinal1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_41,plain,(
    v1_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_33])).

tff(c_40,plain,(
    v1_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_33])).

tff(c_100,plain,(
    ! [B_29,A_30] :
      ( r2_hidden(B_29,A_30)
      | B_29 = A_30
      | r2_hidden(A_30,B_29)
      | ~ v3_ordinal1(B_29)
      | ~ v3_ordinal1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_18,plain,(
    ! [B_9,A_6] :
      ( r1_tarski(B_9,A_6)
      | ~ r2_hidden(B_9,A_6)
      | ~ v1_ordinal1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_109,plain,(
    ! [B_31,A_32] :
      ( r1_tarski(B_31,A_32)
      | ~ v1_ordinal1(A_32)
      | B_31 = A_32
      | r2_hidden(A_32,B_31)
      | ~ v3_ordinal1(B_31)
      | ~ v3_ordinal1(A_32) ) ),
    inference(resolution,[status(thm)],[c_100,c_18])).

tff(c_132,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | ~ v1_ordinal1(B_34)
      | r1_tarski(B_34,A_33)
      | ~ v1_ordinal1(A_33)
      | B_34 = A_33
      | ~ v3_ordinal1(B_34)
      | ~ v3_ordinal1(A_33) ) ),
    inference(resolution,[status(thm)],[c_109,c_18])).

tff(c_51,plain,(
    ! [A_17,B_18] :
      ( ~ r1_tarski(A_17,B_18)
      | r3_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_55,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_51,c_26])).

tff(c_142,plain,
    ( ~ v1_ordinal1('#skF_3')
    | r1_tarski('#skF_3','#skF_2')
    | ~ v1_ordinal1('#skF_2')
    | '#skF_2' = '#skF_3'
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_132,c_55])).

tff(c_157,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_41,c_40,c_142])).

tff(c_158,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_157])).

tff(c_165,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_62])).

tff(c_173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_165])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:06:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.17  
% 1.88/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.17  %$ r3_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_1 > #skF_2 > #skF_3
% 1.88/1.17  
% 1.88/1.17  %Foreground sorts:
% 1.88/1.17  
% 1.88/1.17  
% 1.88/1.17  %Background operators:
% 1.88/1.17  
% 1.88/1.17  
% 1.88/1.17  %Foreground operators:
% 1.88/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.88/1.17  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 1.88/1.17  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.88/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.17  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 1.88/1.17  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 1.88/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.17  tff(r3_xboole_0, type, r3_xboole_0: ($i * $i) > $o).
% 1.88/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.17  
% 1.88/1.18  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.88/1.18  tff(f_37, axiom, (![A, B]: (r3_xboole_0(A, B) <=> (r1_tarski(A, B) | r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_xboole_0)).
% 1.88/1.18  tff(f_73, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => r3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_ordinal1)).
% 1.88/1.18  tff(f_43, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 1.88/1.18  tff(f_65, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 1.88/1.18  tff(f_50, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 1.88/1.18  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.88/1.18  tff(c_58, plain, (![B_21, A_22]: (~r1_tarski(B_21, A_22) | r3_xboole_0(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.88/1.18  tff(c_26, plain, (~r3_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.88/1.18  tff(c_62, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_26])).
% 1.88/1.18  tff(c_30, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.88/1.18  tff(c_28, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.88/1.18  tff(c_33, plain, (![A_15]: (v1_ordinal1(A_15) | ~v3_ordinal1(A_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.88/1.18  tff(c_41, plain, (v1_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_30, c_33])).
% 1.88/1.18  tff(c_40, plain, (v1_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_33])).
% 1.88/1.18  tff(c_100, plain, (![B_29, A_30]: (r2_hidden(B_29, A_30) | B_29=A_30 | r2_hidden(A_30, B_29) | ~v3_ordinal1(B_29) | ~v3_ordinal1(A_30))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.88/1.18  tff(c_18, plain, (![B_9, A_6]: (r1_tarski(B_9, A_6) | ~r2_hidden(B_9, A_6) | ~v1_ordinal1(A_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.88/1.18  tff(c_109, plain, (![B_31, A_32]: (r1_tarski(B_31, A_32) | ~v1_ordinal1(A_32) | B_31=A_32 | r2_hidden(A_32, B_31) | ~v3_ordinal1(B_31) | ~v3_ordinal1(A_32))), inference(resolution, [status(thm)], [c_100, c_18])).
% 1.88/1.18  tff(c_132, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | ~v1_ordinal1(B_34) | r1_tarski(B_34, A_33) | ~v1_ordinal1(A_33) | B_34=A_33 | ~v3_ordinal1(B_34) | ~v3_ordinal1(A_33))), inference(resolution, [status(thm)], [c_109, c_18])).
% 1.88/1.18  tff(c_51, plain, (![A_17, B_18]: (~r1_tarski(A_17, B_18) | r3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.88/1.18  tff(c_55, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_51, c_26])).
% 1.88/1.18  tff(c_142, plain, (~v1_ordinal1('#skF_3') | r1_tarski('#skF_3', '#skF_2') | ~v1_ordinal1('#skF_2') | '#skF_2'='#skF_3' | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_132, c_55])).
% 1.88/1.18  tff(c_157, plain, (r1_tarski('#skF_3', '#skF_2') | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_41, c_40, c_142])).
% 1.88/1.18  tff(c_158, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_62, c_157])).
% 1.88/1.18  tff(c_165, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_62])).
% 1.88/1.18  tff(c_173, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_165])).
% 1.88/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.18  
% 1.88/1.18  Inference rules
% 1.88/1.18  ----------------------
% 1.88/1.18  #Ref     : 0
% 1.88/1.18  #Sup     : 19
% 1.88/1.18  #Fact    : 4
% 1.88/1.18  #Define  : 0
% 1.88/1.18  #Split   : 0
% 1.88/1.18  #Chain   : 0
% 1.88/1.18  #Close   : 0
% 1.88/1.18  
% 1.88/1.18  Ordering : KBO
% 1.88/1.18  
% 1.88/1.18  Simplification rules
% 1.88/1.18  ----------------------
% 1.88/1.18  #Subsume      : 3
% 1.88/1.18  #Demod        : 19
% 1.88/1.18  #Tautology    : 11
% 1.88/1.18  #SimpNegUnit  : 2
% 1.88/1.18  #BackRed      : 6
% 1.88/1.18  
% 1.88/1.18  #Partial instantiations: 0
% 1.88/1.18  #Strategies tried      : 1
% 1.88/1.18  
% 1.88/1.18  Timing (in seconds)
% 1.88/1.18  ----------------------
% 1.88/1.19  Preprocessing        : 0.26
% 1.88/1.19  Parsing              : 0.14
% 1.88/1.19  CNF conversion       : 0.02
% 1.88/1.19  Main loop            : 0.16
% 1.88/1.19  Inferencing          : 0.06
% 1.88/1.19  Reduction            : 0.04
% 1.88/1.19  Demodulation         : 0.03
% 1.88/1.19  BG Simplification    : 0.01
% 1.88/1.19  Subsumption          : 0.03
% 1.88/1.19  Abstraction          : 0.01
% 1.88/1.19  MUC search           : 0.00
% 1.88/1.19  Cooper               : 0.00
% 1.88/1.19  Total                : 0.44
% 1.88/1.19  Index Insertion      : 0.00
% 1.88/1.19  Index Deletion       : 0.00
% 1.88/1.19  Index Matching       : 0.00
% 1.88/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
