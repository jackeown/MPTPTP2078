%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:38 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   40 (  54 expanded)
%              Number of leaves         :   18 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   52 (  85 expanded)
%              Number of equality atoms :   23 (  36 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k2_relat_1(B))
        <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_24,plain,
    ( r2_hidden('#skF_1',k2_relat_1('#skF_2'))
    | k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_54,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( k4_xboole_0(A_4,k1_tarski(B_5)) = A_4
      | r2_hidden(B_5,A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_56,plain,(
    ! [B_17,A_18] :
      ( k10_relat_1(B_17,A_18) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_17),A_18)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_71,plain,(
    ! [B_21,B_22] :
      ( k10_relat_1(B_21,B_22) = k1_xboole_0
      | ~ v1_relat_1(B_21)
      | k4_xboole_0(k2_relat_1(B_21),B_22) != k2_relat_1(B_21) ) ),
    inference(resolution,[status(thm)],[c_4,c_56])).

tff(c_77,plain,(
    ! [B_23,B_24] :
      ( k10_relat_1(B_23,k1_tarski(B_24)) = k1_xboole_0
      | ~ v1_relat_1(B_23)
      | r2_hidden(B_24,k2_relat_1(B_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_71])).

tff(c_18,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_55,plain,(
    ~ r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_18])).

tff(c_80,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_77,c_55])).

tff(c_83,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_80])).

tff(c_85,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_83])).

tff(c_87,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_86,plain,(
    r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_94,plain,(
    ! [B_25,A_26] :
      ( r1_xboole_0(k2_relat_1(B_25),A_26)
      | k10_relat_1(B_25,A_26) != k1_xboole_0
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = A_1
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_109,plain,(
    ! [B_29,A_30] :
      ( k4_xboole_0(k2_relat_1(B_29),A_30) = k2_relat_1(B_29)
      | k10_relat_1(B_29,A_30) != k1_xboole_0
      | ~ v1_relat_1(B_29) ) ),
    inference(resolution,[status(thm)],[c_94,c_2])).

tff(c_8,plain,(
    ! [B_5,A_4] :
      ( ~ r2_hidden(B_5,A_4)
      | k4_xboole_0(A_4,k1_tarski(B_5)) != A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_133,plain,(
    ! [B_31,B_32] :
      ( ~ r2_hidden(B_31,k2_relat_1(B_32))
      | k10_relat_1(B_32,k1_tarski(B_31)) != k1_xboole_0
      | ~ v1_relat_1(B_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_8])).

tff(c_136,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_86,c_133])).

tff(c_140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_87,c_136])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:50:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.18  
% 1.76/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.18  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.76/1.18  
% 1.76/1.18  %Foreground sorts:
% 1.76/1.18  
% 1.76/1.18  
% 1.76/1.18  %Background operators:
% 1.76/1.18  
% 1.76/1.18  
% 1.76/1.18  %Foreground operators:
% 1.76/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.76/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.76/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.76/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.76/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.76/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.76/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.76/1.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.76/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.76/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.76/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.76/1.18  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.76/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.76/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.76/1.18  
% 1.76/1.19  tff(f_50, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 1.76/1.19  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.76/1.19  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.76/1.19  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 1.76/1.19  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.76/1.19  tff(c_24, plain, (r2_hidden('#skF_1', k2_relat_1('#skF_2')) | k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.76/1.19  tff(c_54, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_24])).
% 1.76/1.19  tff(c_10, plain, (![A_4, B_5]: (k4_xboole_0(A_4, k1_tarski(B_5))=A_4 | r2_hidden(B_5, A_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.76/1.19  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k4_xboole_0(A_1, B_2)!=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.76/1.19  tff(c_56, plain, (![B_17, A_18]: (k10_relat_1(B_17, A_18)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_17), A_18) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.76/1.19  tff(c_71, plain, (![B_21, B_22]: (k10_relat_1(B_21, B_22)=k1_xboole_0 | ~v1_relat_1(B_21) | k4_xboole_0(k2_relat_1(B_21), B_22)!=k2_relat_1(B_21))), inference(resolution, [status(thm)], [c_4, c_56])).
% 1.76/1.19  tff(c_77, plain, (![B_23, B_24]: (k10_relat_1(B_23, k1_tarski(B_24))=k1_xboole_0 | ~v1_relat_1(B_23) | r2_hidden(B_24, k2_relat_1(B_23)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_71])).
% 1.76/1.19  tff(c_18, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.76/1.19  tff(c_55, plain, (~r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_18])).
% 1.76/1.19  tff(c_80, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_77, c_55])).
% 1.76/1.19  tff(c_83, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_80])).
% 1.76/1.19  tff(c_85, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_83])).
% 1.76/1.19  tff(c_87, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_24])).
% 1.76/1.19  tff(c_86, plain, (r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_24])).
% 1.76/1.19  tff(c_94, plain, (![B_25, A_26]: (r1_xboole_0(k2_relat_1(B_25), A_26) | k10_relat_1(B_25, A_26)!=k1_xboole_0 | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.76/1.19  tff(c_2, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=A_1 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.76/1.19  tff(c_109, plain, (![B_29, A_30]: (k4_xboole_0(k2_relat_1(B_29), A_30)=k2_relat_1(B_29) | k10_relat_1(B_29, A_30)!=k1_xboole_0 | ~v1_relat_1(B_29))), inference(resolution, [status(thm)], [c_94, c_2])).
% 1.76/1.19  tff(c_8, plain, (![B_5, A_4]: (~r2_hidden(B_5, A_4) | k4_xboole_0(A_4, k1_tarski(B_5))!=A_4)), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.76/1.19  tff(c_133, plain, (![B_31, B_32]: (~r2_hidden(B_31, k2_relat_1(B_32)) | k10_relat_1(B_32, k1_tarski(B_31))!=k1_xboole_0 | ~v1_relat_1(B_32))), inference(superposition, [status(thm), theory('equality')], [c_109, c_8])).
% 1.76/1.19  tff(c_136, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_86, c_133])).
% 1.76/1.19  tff(c_140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_87, c_136])).
% 1.76/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.19  
% 1.76/1.19  Inference rules
% 1.76/1.19  ----------------------
% 1.76/1.19  #Ref     : 0
% 1.76/1.19  #Sup     : 22
% 1.76/1.19  #Fact    : 0
% 1.76/1.19  #Define  : 0
% 1.76/1.19  #Split   : 1
% 1.76/1.19  #Chain   : 0
% 1.76/1.19  #Close   : 0
% 1.76/1.19  
% 1.76/1.19  Ordering : KBO
% 1.76/1.19  
% 1.76/1.19  Simplification rules
% 1.76/1.19  ----------------------
% 1.76/1.19  #Subsume      : 0
% 1.76/1.19  #Demod        : 5
% 1.76/1.19  #Tautology    : 17
% 1.76/1.19  #SimpNegUnit  : 2
% 1.76/1.19  #BackRed      : 0
% 1.76/1.19  
% 1.76/1.19  #Partial instantiations: 0
% 1.76/1.19  #Strategies tried      : 1
% 1.76/1.19  
% 1.76/1.19  Timing (in seconds)
% 1.76/1.19  ----------------------
% 1.76/1.20  Preprocessing        : 0.29
% 1.76/1.20  Parsing              : 0.16
% 1.92/1.20  CNF conversion       : 0.02
% 1.92/1.20  Main loop            : 0.12
% 1.92/1.20  Inferencing          : 0.05
% 1.92/1.20  Reduction            : 0.03
% 1.92/1.20  Demodulation         : 0.02
% 1.92/1.20  BG Simplification    : 0.01
% 1.92/1.20  Subsumption          : 0.01
% 1.92/1.20  Abstraction          : 0.01
% 1.92/1.20  MUC search           : 0.00
% 1.92/1.20  Cooper               : 0.00
% 1.92/1.20  Total                : 0.43
% 1.92/1.20  Index Insertion      : 0.00
% 1.92/1.20  Index Deletion       : 0.00
% 1.92/1.20  Index Matching       : 0.00
% 1.92/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
