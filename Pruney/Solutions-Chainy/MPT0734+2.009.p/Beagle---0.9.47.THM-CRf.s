%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:03 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   37 (  46 expanded)
%              Number of leaves         :   17 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   65 ( 109 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( v1_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ! [C] :
                ( v3_ordinal1(C)
               => ( ( r1_tarski(A,B)
                    & r2_hidden(B,C) )
                 => r2_hidden(A,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

tff(f_38,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( v1_ordinal1(C)
     => ( ( r2_hidden(A,B)
          & r2_hidden(B,C) )
       => r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_ordinal1)).

tff(c_16,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_26,plain,(
    v1_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_24,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_xboole_0(A_1,B_2)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,(
    ! [A_21,B_22] :
      ( r2_hidden(A_21,B_22)
      | ~ r2_xboole_0(A_21,B_22)
      | ~ v3_ordinal1(B_22)
      | ~ v1_ordinal1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_70,plain,(
    ! [A_27,B_28] :
      ( r2_hidden(A_27,B_28)
      | ~ v3_ordinal1(B_28)
      | ~ v1_ordinal1(A_27)
      | B_28 = A_27
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(resolution,[status(thm)],[c_2,c_58])).

tff(c_22,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28,plain,(
    ! [A_15] :
      ( v1_ordinal1(A_15)
      | ~ v3_ordinal1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_35,plain,(
    v1_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_28])).

tff(c_18,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_63,plain,(
    ! [A_23,C_24,B_25] :
      ( r2_hidden(A_23,C_24)
      | ~ r2_hidden(B_25,C_24)
      | ~ r2_hidden(A_23,B_25)
      | ~ v1_ordinal1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_65,plain,(
    ! [A_23] :
      ( r2_hidden(A_23,'#skF_3')
      | ~ r2_hidden(A_23,'#skF_2')
      | ~ v1_ordinal1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_18,c_63])).

tff(c_68,plain,(
    ! [A_23] :
      ( r2_hidden(A_23,'#skF_3')
      | ~ r2_hidden(A_23,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_65])).

tff(c_74,plain,(
    ! [A_27] :
      ( r2_hidden(A_27,'#skF_3')
      | ~ v3_ordinal1('#skF_2')
      | ~ v1_ordinal1(A_27)
      | A_27 = '#skF_2'
      | ~ r1_tarski(A_27,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_70,c_68])).

tff(c_88,plain,(
    ! [A_29] :
      ( r2_hidden(A_29,'#skF_3')
      | ~ v1_ordinal1(A_29)
      | A_29 = '#skF_2'
      | ~ r1_tarski(A_29,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_74])).

tff(c_93,plain,
    ( ~ v1_ordinal1('#skF_1')
    | '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_88,c_16])).

tff(c_99,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_26,c_93])).

tff(c_104,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_18])).

tff(c_109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_104])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 20:58:36 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.17  
% 1.64/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.17  %$ r2_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.64/1.17  
% 1.64/1.17  %Foreground sorts:
% 1.64/1.17  
% 1.64/1.17  
% 1.64/1.17  %Background operators:
% 1.64/1.17  
% 1.64/1.17  
% 1.64/1.17  %Foreground operators:
% 1.64/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.64/1.17  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 1.64/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.64/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.17  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 1.64/1.17  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 1.64/1.17  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.64/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.17  
% 1.87/1.18  tff(f_70, negated_conjecture, ~(![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (![C]: (v3_ordinal1(C) => ((r1_tarski(A, B) & r2_hidden(B, C)) => r2_hidden(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_ordinal1)).
% 1.87/1.18  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.87/1.18  tff(f_55, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_xboole_0(A, B) => r2_hidden(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_ordinal1)).
% 1.87/1.18  tff(f_38, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 1.87/1.18  tff(f_46, axiom, (![A, B, C]: (v1_ordinal1(C) => ((r2_hidden(A, B) & r2_hidden(B, C)) => r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_ordinal1)).
% 1.87/1.18  tff(c_16, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.87/1.18  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.87/1.18  tff(c_26, plain, (v1_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.87/1.18  tff(c_24, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.87/1.18  tff(c_2, plain, (![A_1, B_2]: (r2_xboole_0(A_1, B_2) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.87/1.18  tff(c_58, plain, (![A_21, B_22]: (r2_hidden(A_21, B_22) | ~r2_xboole_0(A_21, B_22) | ~v3_ordinal1(B_22) | ~v1_ordinal1(A_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.87/1.18  tff(c_70, plain, (![A_27, B_28]: (r2_hidden(A_27, B_28) | ~v3_ordinal1(B_28) | ~v1_ordinal1(A_27) | B_28=A_27 | ~r1_tarski(A_27, B_28))), inference(resolution, [status(thm)], [c_2, c_58])).
% 1.87/1.18  tff(c_22, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.87/1.18  tff(c_28, plain, (![A_15]: (v1_ordinal1(A_15) | ~v3_ordinal1(A_15))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.87/1.18  tff(c_35, plain, (v1_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_28])).
% 1.87/1.18  tff(c_18, plain, (r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.87/1.18  tff(c_63, plain, (![A_23, C_24, B_25]: (r2_hidden(A_23, C_24) | ~r2_hidden(B_25, C_24) | ~r2_hidden(A_23, B_25) | ~v1_ordinal1(C_24))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.87/1.18  tff(c_65, plain, (![A_23]: (r2_hidden(A_23, '#skF_3') | ~r2_hidden(A_23, '#skF_2') | ~v1_ordinal1('#skF_3'))), inference(resolution, [status(thm)], [c_18, c_63])).
% 1.87/1.18  tff(c_68, plain, (![A_23]: (r2_hidden(A_23, '#skF_3') | ~r2_hidden(A_23, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_65])).
% 1.87/1.18  tff(c_74, plain, (![A_27]: (r2_hidden(A_27, '#skF_3') | ~v3_ordinal1('#skF_2') | ~v1_ordinal1(A_27) | A_27='#skF_2' | ~r1_tarski(A_27, '#skF_2'))), inference(resolution, [status(thm)], [c_70, c_68])).
% 1.87/1.18  tff(c_88, plain, (![A_29]: (r2_hidden(A_29, '#skF_3') | ~v1_ordinal1(A_29) | A_29='#skF_2' | ~r1_tarski(A_29, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_74])).
% 1.87/1.18  tff(c_93, plain, (~v1_ordinal1('#skF_1') | '#skF_2'='#skF_1' | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_88, c_16])).
% 1.87/1.18  tff(c_99, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_26, c_93])).
% 1.87/1.18  tff(c_104, plain, (r2_hidden('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_18])).
% 1.87/1.18  tff(c_109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_104])).
% 1.87/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.18  
% 1.87/1.18  Inference rules
% 1.87/1.18  ----------------------
% 1.87/1.18  #Ref     : 0
% 1.87/1.18  #Sup     : 13
% 1.87/1.18  #Fact    : 0
% 1.87/1.18  #Define  : 0
% 1.87/1.18  #Split   : 1
% 1.87/1.18  #Chain   : 0
% 1.87/1.18  #Close   : 0
% 1.87/1.18  
% 1.87/1.18  Ordering : KBO
% 1.87/1.18  
% 1.87/1.18  Simplification rules
% 1.87/1.18  ----------------------
% 1.87/1.18  #Subsume      : 0
% 1.87/1.18  #Demod        : 16
% 1.87/1.18  #Tautology    : 3
% 1.87/1.18  #SimpNegUnit  : 1
% 1.87/1.18  #BackRed      : 7
% 1.87/1.18  
% 1.87/1.18  #Partial instantiations: 0
% 1.87/1.18  #Strategies tried      : 1
% 1.87/1.18  
% 1.87/1.18  Timing (in seconds)
% 1.87/1.18  ----------------------
% 1.87/1.19  Preprocessing        : 0.26
% 1.87/1.19  Parsing              : 0.15
% 1.87/1.19  CNF conversion       : 0.02
% 1.87/1.19  Main loop            : 0.14
% 1.87/1.19  Inferencing          : 0.06
% 1.87/1.19  Reduction            : 0.04
% 1.87/1.19  Demodulation         : 0.03
% 1.87/1.19  BG Simplification    : 0.01
% 1.87/1.19  Subsumption          : 0.02
% 1.87/1.19  Abstraction          : 0.01
% 1.87/1.19  MUC search           : 0.00
% 1.87/1.19  Cooper               : 0.00
% 1.87/1.19  Total                : 0.43
% 1.87/1.19  Index Insertion      : 0.00
% 1.87/1.19  Index Deletion       : 0.00
% 1.87/1.19  Index Matching       : 0.00
% 1.87/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
