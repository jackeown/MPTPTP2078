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
% DateTime   : Thu Dec  3 10:01:28 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   47 (  57 expanded)
%              Number of leaves         :   25 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   58 (  88 expanded)
%              Number of equality atoms :   11 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_79,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_82,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_49,plain,(
    ! [B_41,A_42] :
      ( r1_tarski(k10_relat_1(B_41,A_42),k1_relat_1(B_41))
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_52,plain,(
    ! [A_42] :
      ( r1_tarski(k10_relat_1(k1_xboole_0,A_42),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_49])).

tff(c_53,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_22,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_3'(A_12),A_12)
      | v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_14,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_75,plain,(
    ! [A_51,B_52,C_53] :
      ( ~ r1_xboole_0(A_51,B_52)
      | ~ r2_hidden(C_53,B_52)
      | ~ r2_hidden(C_53,A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_79,plain,(
    ! [C_54] : ~ r2_hidden(C_54,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_75])).

tff(c_95,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_79])).

tff(c_102,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_95])).

tff(c_103,plain,(
    ! [A_42] : r1_tarski(k10_relat_1(k1_xboole_0,A_42),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_140,plain,(
    ! [C_65,B_66,A_67] :
      ( r2_hidden(C_65,B_66)
      | ~ r2_hidden(C_65,A_67)
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_226,plain,(
    ! [A_82,B_83,B_84] :
      ( r2_hidden('#skF_2'(A_82,B_83),B_84)
      | ~ r1_tarski(B_83,B_84)
      | r1_xboole_0(A_82,B_83) ) ),
    inference(resolution,[status(thm)],[c_10,c_140])).

tff(c_114,plain,(
    ! [A_61,B_62,C_63] :
      ( ~ r1_xboole_0(A_61,B_62)
      | ~ r2_hidden(C_63,B_62)
      | ~ r2_hidden(C_63,A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_117,plain,(
    ! [C_63] : ~ r2_hidden(C_63,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_114])).

tff(c_235,plain,(
    ! [B_85,A_86] :
      ( ~ r1_tarski(B_85,k1_xboole_0)
      | r1_xboole_0(A_86,B_85) ) ),
    inference(resolution,[status(thm)],[c_226,c_117])).

tff(c_16,plain,(
    ! [A_11] :
      ( ~ r1_xboole_0(A_11,A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_244,plain,(
    ! [B_87] :
      ( k1_xboole_0 = B_87
      | ~ r1_tarski(B_87,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_235,c_16])).

tff(c_258,plain,(
    ! [A_42] : k10_relat_1(k1_xboole_0,A_42) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_103,c_244])).

tff(c_30,plain,(
    k10_relat_1(k1_xboole_0,'#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_267,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:27:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.39  
% 2.07/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.40  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 2.07/1.40  
% 2.07/1.40  %Foreground sorts:
% 2.07/1.40  
% 2.07/1.40  
% 2.07/1.40  %Background operators:
% 2.07/1.40  
% 2.07/1.40  
% 2.07/1.40  %Foreground operators:
% 2.07/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.07/1.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.07/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.07/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.07/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.07/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.07/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.07/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.40  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.07/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.07/1.40  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.07/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.07/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.07/1.40  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.07/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.07/1.40  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.07/1.40  
% 2.07/1.41  tff(f_79, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.07/1.41  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 2.07/1.41  tff(f_72, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.07/1.41  tff(f_62, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.07/1.41  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.07/1.41  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.07/1.41  tff(f_82, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 2.07/1.41  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.07/1.41  tff(c_49, plain, (![B_41, A_42]: (r1_tarski(k10_relat_1(B_41, A_42), k1_relat_1(B_41)) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.07/1.41  tff(c_52, plain, (![A_42]: (r1_tarski(k10_relat_1(k1_xboole_0, A_42), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_49])).
% 2.07/1.41  tff(c_53, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_52])).
% 2.07/1.41  tff(c_22, plain, (![A_12]: (r2_hidden('#skF_3'(A_12), A_12) | v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.07/1.41  tff(c_14, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.07/1.41  tff(c_75, plain, (![A_51, B_52, C_53]: (~r1_xboole_0(A_51, B_52) | ~r2_hidden(C_53, B_52) | ~r2_hidden(C_53, A_51))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.07/1.41  tff(c_79, plain, (![C_54]: (~r2_hidden(C_54, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_75])).
% 2.07/1.41  tff(c_95, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_79])).
% 2.07/1.41  tff(c_102, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_95])).
% 2.07/1.41  tff(c_103, plain, (![A_42]: (r1_tarski(k10_relat_1(k1_xboole_0, A_42), k1_xboole_0))), inference(splitRight, [status(thm)], [c_52])).
% 2.07/1.41  tff(c_10, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.07/1.41  tff(c_140, plain, (![C_65, B_66, A_67]: (r2_hidden(C_65, B_66) | ~r2_hidden(C_65, A_67) | ~r1_tarski(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.07/1.41  tff(c_226, plain, (![A_82, B_83, B_84]: (r2_hidden('#skF_2'(A_82, B_83), B_84) | ~r1_tarski(B_83, B_84) | r1_xboole_0(A_82, B_83))), inference(resolution, [status(thm)], [c_10, c_140])).
% 2.07/1.41  tff(c_114, plain, (![A_61, B_62, C_63]: (~r1_xboole_0(A_61, B_62) | ~r2_hidden(C_63, B_62) | ~r2_hidden(C_63, A_61))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.07/1.41  tff(c_117, plain, (![C_63]: (~r2_hidden(C_63, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_114])).
% 2.07/1.41  tff(c_235, plain, (![B_85, A_86]: (~r1_tarski(B_85, k1_xboole_0) | r1_xboole_0(A_86, B_85))), inference(resolution, [status(thm)], [c_226, c_117])).
% 2.07/1.41  tff(c_16, plain, (![A_11]: (~r1_xboole_0(A_11, A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.07/1.41  tff(c_244, plain, (![B_87]: (k1_xboole_0=B_87 | ~r1_tarski(B_87, k1_xboole_0))), inference(resolution, [status(thm)], [c_235, c_16])).
% 2.07/1.41  tff(c_258, plain, (![A_42]: (k10_relat_1(k1_xboole_0, A_42)=k1_xboole_0)), inference(resolution, [status(thm)], [c_103, c_244])).
% 2.07/1.41  tff(c_30, plain, (k10_relat_1(k1_xboole_0, '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.07/1.41  tff(c_267, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_258, c_30])).
% 2.07/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.41  
% 2.07/1.41  Inference rules
% 2.07/1.41  ----------------------
% 2.07/1.41  #Ref     : 1
% 2.07/1.41  #Sup     : 47
% 2.07/1.41  #Fact    : 0
% 2.07/1.41  #Define  : 0
% 2.07/1.41  #Split   : 1
% 2.07/1.41  #Chain   : 0
% 2.07/1.41  #Close   : 0
% 2.07/1.41  
% 2.07/1.41  Ordering : KBO
% 2.07/1.41  
% 2.07/1.41  Simplification rules
% 2.07/1.41  ----------------------
% 2.07/1.41  #Subsume      : 2
% 2.07/1.41  #Demod        : 9
% 2.07/1.41  #Tautology    : 18
% 2.07/1.41  #SimpNegUnit  : 1
% 2.07/1.41  #BackRed      : 3
% 2.07/1.41  
% 2.07/1.41  #Partial instantiations: 0
% 2.07/1.41  #Strategies tried      : 1
% 2.07/1.41  
% 2.07/1.41  Timing (in seconds)
% 2.07/1.41  ----------------------
% 2.07/1.41  Preprocessing        : 0.31
% 2.07/1.41  Parsing              : 0.17
% 2.07/1.41  CNF conversion       : 0.02
% 2.07/1.41  Main loop            : 0.19
% 2.07/1.41  Inferencing          : 0.08
% 2.07/1.41  Reduction            : 0.05
% 2.07/1.41  Demodulation         : 0.03
% 2.07/1.41  BG Simplification    : 0.01
% 2.07/1.41  Subsumption          : 0.04
% 2.07/1.41  Abstraction          : 0.01
% 2.07/1.41  MUC search           : 0.00
% 2.07/1.41  Cooper               : 0.00
% 2.07/1.41  Total                : 0.53
% 2.07/1.41  Index Insertion      : 0.00
% 2.07/1.41  Index Deletion       : 0.00
% 2.07/1.41  Index Matching       : 0.00
% 2.07/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
