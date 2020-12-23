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
% DateTime   : Thu Dec  3 10:06:03 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   49 (  72 expanded)
%              Number of leaves         :   22 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   73 ( 164 expanded)
%              Number of equality atoms :    9 (  14 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > #nlpp > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_82,negated_conjecture,(
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

tff(f_67,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_46,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

tff(c_28,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_57,plain,(
    ! [B_27,A_28] :
      ( ~ r1_tarski(B_27,A_28)
      | ~ r2_hidden(A_28,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_61,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_57])).

tff(c_32,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_47,plain,(
    ! [A_24] :
      ( v1_ordinal1(A_24)
      | ~ v3_ordinal1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_54,plain,(
    v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_47])).

tff(c_78,plain,(
    ! [B_34,A_35] :
      ( r1_tarski(B_34,A_35)
      | ~ r2_hidden(B_34,A_35)
      | ~ v1_ordinal1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_84,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_78])).

tff(c_88,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_84])).

tff(c_30,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_69,plain,(
    ! [A_32,B_33] :
      ( k2_xboole_0(A_32,B_33) = B_33
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_73,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_30,c_69])).

tff(c_97,plain,(
    ! [A_36,C_37,B_38] :
      ( r1_tarski(A_36,C_37)
      | ~ r1_tarski(k2_xboole_0(A_36,B_38),C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_103,plain,(
    ! [C_37] :
      ( r1_tarski('#skF_2',C_37)
      | ~ r1_tarski('#skF_3',C_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_97])).

tff(c_36,plain,(
    v1_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_xboole_0(A_1,B_2)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_166,plain,(
    ! [A_47,B_48] :
      ( r2_hidden(A_47,B_48)
      | ~ r2_xboole_0(A_47,B_48)
      | ~ v3_ordinal1(B_48)
      | ~ v1_ordinal1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_171,plain,(
    ! [A_49,B_50] :
      ( r2_hidden(A_49,B_50)
      | ~ v3_ordinal1(B_50)
      | ~ v1_ordinal1(A_49)
      | B_50 = A_49
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(resolution,[status(thm)],[c_2,c_166])).

tff(c_26,plain,(
    ~ r2_hidden('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_180,plain,
    ( ~ v3_ordinal1('#skF_4')
    | ~ v1_ordinal1('#skF_2')
    | '#skF_2' = '#skF_4'
    | ~ r1_tarski('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_171,c_26])).

tff(c_185,plain,
    ( '#skF_2' = '#skF_4'
    | ~ r1_tarski('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_180])).

tff(c_186,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_185])).

tff(c_192,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_103,c_186])).

tff(c_197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_192])).

tff(c_198,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_207,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_30])).

tff(c_210,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_207])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:20:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.30  
% 2.00/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.30  %$ r2_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > #nlpp > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.00/1.30  
% 2.00/1.30  %Foreground sorts:
% 2.00/1.30  
% 2.00/1.30  
% 2.00/1.30  %Background operators:
% 2.00/1.30  
% 2.00/1.30  
% 2.00/1.30  %Foreground operators:
% 2.00/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.00/1.30  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 2.00/1.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.00/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.00/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.00/1.30  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.00/1.30  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 2.00/1.30  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.00/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.00/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.00/1.30  
% 2.00/1.32  tff(f_82, negated_conjecture, ~(![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (![C]: (v3_ordinal1(C) => ((r1_tarski(A, B) & r2_hidden(B, C)) => r2_hidden(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_ordinal1)).
% 2.00/1.32  tff(f_67, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.00/1.32  tff(f_46, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 2.00/1.32  tff(f_53, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 2.00/1.32  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.00/1.32  tff(f_36, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.00/1.32  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.00/1.32  tff(f_62, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_xboole_0(A, B) => r2_hidden(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_ordinal1)).
% 2.00/1.32  tff(c_28, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.00/1.32  tff(c_57, plain, (![B_27, A_28]: (~r1_tarski(B_27, A_28) | ~r2_hidden(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.00/1.32  tff(c_61, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_57])).
% 2.00/1.32  tff(c_32, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.00/1.32  tff(c_47, plain, (![A_24]: (v1_ordinal1(A_24) | ~v3_ordinal1(A_24))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.00/1.32  tff(c_54, plain, (v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_47])).
% 2.00/1.32  tff(c_78, plain, (![B_34, A_35]: (r1_tarski(B_34, A_35) | ~r2_hidden(B_34, A_35) | ~v1_ordinal1(A_35))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.00/1.32  tff(c_84, plain, (r1_tarski('#skF_3', '#skF_4') | ~v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_78])).
% 2.00/1.32  tff(c_88, plain, (r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_84])).
% 2.00/1.32  tff(c_30, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.00/1.32  tff(c_69, plain, (![A_32, B_33]: (k2_xboole_0(A_32, B_33)=B_33 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.00/1.32  tff(c_73, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_30, c_69])).
% 2.00/1.32  tff(c_97, plain, (![A_36, C_37, B_38]: (r1_tarski(A_36, C_37) | ~r1_tarski(k2_xboole_0(A_36, B_38), C_37))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.00/1.32  tff(c_103, plain, (![C_37]: (r1_tarski('#skF_2', C_37) | ~r1_tarski('#skF_3', C_37))), inference(superposition, [status(thm), theory('equality')], [c_73, c_97])).
% 2.00/1.32  tff(c_36, plain, (v1_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.00/1.32  tff(c_2, plain, (![A_1, B_2]: (r2_xboole_0(A_1, B_2) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.00/1.32  tff(c_166, plain, (![A_47, B_48]: (r2_hidden(A_47, B_48) | ~r2_xboole_0(A_47, B_48) | ~v3_ordinal1(B_48) | ~v1_ordinal1(A_47))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.00/1.32  tff(c_171, plain, (![A_49, B_50]: (r2_hidden(A_49, B_50) | ~v3_ordinal1(B_50) | ~v1_ordinal1(A_49) | B_50=A_49 | ~r1_tarski(A_49, B_50))), inference(resolution, [status(thm)], [c_2, c_166])).
% 2.00/1.32  tff(c_26, plain, (~r2_hidden('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.00/1.32  tff(c_180, plain, (~v3_ordinal1('#skF_4') | ~v1_ordinal1('#skF_2') | '#skF_2'='#skF_4' | ~r1_tarski('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_171, c_26])).
% 2.00/1.32  tff(c_185, plain, ('#skF_2'='#skF_4' | ~r1_tarski('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_180])).
% 2.00/1.32  tff(c_186, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_185])).
% 2.00/1.32  tff(c_192, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_103, c_186])).
% 2.00/1.32  tff(c_197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_192])).
% 2.00/1.32  tff(c_198, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_185])).
% 2.00/1.32  tff(c_207, plain, (r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_198, c_30])).
% 2.00/1.32  tff(c_210, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_207])).
% 2.00/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.32  
% 2.00/1.32  Inference rules
% 2.00/1.32  ----------------------
% 2.00/1.32  #Ref     : 0
% 2.00/1.32  #Sup     : 35
% 2.00/1.32  #Fact    : 0
% 2.00/1.32  #Define  : 0
% 2.00/1.32  #Split   : 1
% 2.00/1.32  #Chain   : 0
% 2.00/1.32  #Close   : 0
% 2.00/1.32  
% 2.00/1.32  Ordering : KBO
% 2.00/1.32  
% 2.00/1.32  Simplification rules
% 2.00/1.32  ----------------------
% 2.00/1.32  #Subsume      : 2
% 2.00/1.32  #Demod        : 16
% 2.00/1.32  #Tautology    : 14
% 2.00/1.32  #SimpNegUnit  : 1
% 2.00/1.32  #BackRed      : 8
% 2.00/1.32  
% 2.00/1.32  #Partial instantiations: 0
% 2.00/1.32  #Strategies tried      : 1
% 2.00/1.32  
% 2.00/1.32  Timing (in seconds)
% 2.00/1.32  ----------------------
% 2.00/1.32  Preprocessing        : 0.29
% 2.00/1.32  Parsing              : 0.17
% 2.00/1.32  CNF conversion       : 0.02
% 2.00/1.32  Main loop            : 0.19
% 2.00/1.32  Inferencing          : 0.08
% 2.00/1.32  Reduction            : 0.05
% 2.00/1.32  Demodulation         : 0.03
% 2.00/1.32  BG Simplification    : 0.01
% 2.00/1.32  Subsumption          : 0.04
% 2.00/1.32  Abstraction          : 0.01
% 2.25/1.32  MUC search           : 0.00
% 2.25/1.32  Cooper               : 0.00
% 2.25/1.32  Total                : 0.51
% 2.25/1.32  Index Insertion      : 0.00
% 2.25/1.32  Index Deletion       : 0.00
% 2.25/1.32  Index Matching       : 0.00
% 2.25/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
