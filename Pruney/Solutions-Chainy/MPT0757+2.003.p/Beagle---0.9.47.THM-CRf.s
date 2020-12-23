%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:31 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   40 (  54 expanded)
%              Number of leaves         :   19 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   65 ( 115 expanded)
%              Number of equality atoms :    6 (  17 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_1 > #skF_2 > #skF_3

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

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ~ ( ~ r2_xboole_0(A,B)
                & A != B
                & ~ r2_xboole_0(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_ordinal1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_38,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_62,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

tff(c_32,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_30,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_83,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(A_25,B_26)
      | ~ r1_ordinal1(A_25,B_26)
      | ~ v3_ordinal1(B_26)
      | ~ v3_ordinal1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_26,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_55,plain,(
    ! [A_21,B_22] :
      ( r2_xboole_0(A_21,B_22)
      | B_22 = A_21
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    ~ r2_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_65,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_55,c_28])).

tff(c_74,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_65])).

tff(c_89,plain,
    ( ~ r1_ordinal1('#skF_2','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_83,c_74])).

tff(c_99,plain,(
    ~ r1_ordinal1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_89])).

tff(c_43,plain,(
    ! [A_16] :
      ( v1_ordinal1(A_16)
      | ~ v3_ordinal1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_51,plain,(
    v1_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_43])).

tff(c_106,plain,(
    ! [B_29,A_30] :
      ( r2_hidden(B_29,A_30)
      | r1_ordinal1(A_30,B_29)
      | ~ v3_ordinal1(B_29)
      | ~ v3_ordinal1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_12,plain,(
    ! [B_7,A_4] :
      ( r1_tarski(B_7,A_4)
      | ~ r2_hidden(B_7,A_4)
      | ~ v1_ordinal1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_111,plain,(
    ! [B_31,A_32] :
      ( r1_tarski(B_31,A_32)
      | ~ v1_ordinal1(A_32)
      | r1_ordinal1(A_32,B_31)
      | ~ v3_ordinal1(B_31)
      | ~ v3_ordinal1(A_32) ) ),
    inference(resolution,[status(thm)],[c_106,c_12])).

tff(c_24,plain,(
    ~ r2_xboole_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_68,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_55,c_24])).

tff(c_77,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_68])).

tff(c_117,plain,
    ( ~ v1_ordinal1('#skF_2')
    | r1_ordinal1('#skF_2','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_111,c_77])).

tff(c_128,plain,(
    r1_ordinal1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_51,c_117])).

tff(c_130,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_128])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:20:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.15  
% 1.69/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.16  %$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_1 > #skF_2 > #skF_3
% 1.69/1.16  
% 1.69/1.16  %Foreground sorts:
% 1.69/1.16  
% 1.69/1.16  
% 1.69/1.16  %Background operators:
% 1.69/1.16  
% 1.69/1.16  
% 1.69/1.16  %Foreground operators:
% 1.69/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.69/1.16  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 1.69/1.16  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.69/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.69/1.16  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 1.69/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.69/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.69/1.16  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 1.69/1.16  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 1.69/1.16  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.69/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.16  
% 1.69/1.17  tff(f_78, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_xboole_0(A, B) & ~(A = B)) & ~r2_xboole_0(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_ordinal1)).
% 1.69/1.17  tff(f_53, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 1.69/1.17  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.69/1.17  tff(f_38, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 1.69/1.17  tff(f_62, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 1.69/1.17  tff(f_45, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 1.69/1.17  tff(c_32, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.69/1.17  tff(c_30, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.69/1.17  tff(c_83, plain, (![A_25, B_26]: (r1_tarski(A_25, B_26) | ~r1_ordinal1(A_25, B_26) | ~v3_ordinal1(B_26) | ~v3_ordinal1(A_25))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.69/1.17  tff(c_26, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.69/1.17  tff(c_55, plain, (![A_21, B_22]: (r2_xboole_0(A_21, B_22) | B_22=A_21 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.69/1.17  tff(c_28, plain, (~r2_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.69/1.17  tff(c_65, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_55, c_28])).
% 1.69/1.17  tff(c_74, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_26, c_65])).
% 1.69/1.17  tff(c_89, plain, (~r1_ordinal1('#skF_2', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_83, c_74])).
% 1.69/1.17  tff(c_99, plain, (~r1_ordinal1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_89])).
% 1.69/1.17  tff(c_43, plain, (![A_16]: (v1_ordinal1(A_16) | ~v3_ordinal1(A_16))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.69/1.17  tff(c_51, plain, (v1_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_32, c_43])).
% 1.69/1.17  tff(c_106, plain, (![B_29, A_30]: (r2_hidden(B_29, A_30) | r1_ordinal1(A_30, B_29) | ~v3_ordinal1(B_29) | ~v3_ordinal1(A_30))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.69/1.17  tff(c_12, plain, (![B_7, A_4]: (r1_tarski(B_7, A_4) | ~r2_hidden(B_7, A_4) | ~v1_ordinal1(A_4))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.69/1.17  tff(c_111, plain, (![B_31, A_32]: (r1_tarski(B_31, A_32) | ~v1_ordinal1(A_32) | r1_ordinal1(A_32, B_31) | ~v3_ordinal1(B_31) | ~v3_ordinal1(A_32))), inference(resolution, [status(thm)], [c_106, c_12])).
% 1.69/1.17  tff(c_24, plain, (~r2_xboole_0('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.69/1.17  tff(c_68, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_55, c_24])).
% 1.69/1.17  tff(c_77, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_26, c_68])).
% 1.69/1.17  tff(c_117, plain, (~v1_ordinal1('#skF_2') | r1_ordinal1('#skF_2', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_111, c_77])).
% 1.69/1.17  tff(c_128, plain, (r1_ordinal1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_51, c_117])).
% 1.69/1.17  tff(c_130, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_128])).
% 1.69/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.17  
% 1.69/1.17  Inference rules
% 1.69/1.17  ----------------------
% 1.69/1.17  #Ref     : 0
% 1.69/1.17  #Sup     : 18
% 1.69/1.17  #Fact    : 0
% 1.69/1.17  #Define  : 0
% 1.69/1.17  #Split   : 0
% 1.69/1.17  #Chain   : 0
% 1.69/1.17  #Close   : 0
% 1.69/1.17  
% 1.69/1.17  Ordering : KBO
% 1.69/1.17  
% 1.69/1.17  Simplification rules
% 1.69/1.17  ----------------------
% 1.69/1.17  #Subsume      : 1
% 1.69/1.17  #Demod        : 7
% 1.69/1.17  #Tautology    : 4
% 1.69/1.17  #SimpNegUnit  : 3
% 1.69/1.17  #BackRed      : 0
% 1.69/1.17  
% 1.69/1.17  #Partial instantiations: 0
% 1.69/1.17  #Strategies tried      : 1
% 1.69/1.17  
% 1.69/1.17  Timing (in seconds)
% 1.69/1.17  ----------------------
% 1.69/1.17  Preprocessing        : 0.28
% 1.69/1.17  Parsing              : 0.16
% 1.69/1.17  CNF conversion       : 0.02
% 1.69/1.17  Main loop            : 0.12
% 1.69/1.17  Inferencing          : 0.05
% 1.69/1.17  Reduction            : 0.03
% 1.69/1.17  Demodulation         : 0.02
% 1.69/1.17  BG Simplification    : 0.01
% 1.69/1.17  Subsumption          : 0.02
% 1.69/1.17  Abstraction          : 0.01
% 1.69/1.17  MUC search           : 0.00
% 1.69/1.17  Cooper               : 0.00
% 1.69/1.17  Total                : 0.43
% 1.69/1.17  Index Insertion      : 0.00
% 1.69/1.17  Index Deletion       : 0.00
% 1.69/1.17  Index Matching       : 0.00
% 1.69/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
