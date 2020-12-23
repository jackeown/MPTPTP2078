%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:35 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   37 (  39 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   46 (  52 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k1_wellord1 > #nlpp > k3_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k3_relat_1(B))
          | k1_wellord1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_wellord1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k1_wellord1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( D != B
                & r2_hidden(k4_tarski(D,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_32,plain,(
    k1_wellord1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_36,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_202,plain,(
    ! [A_71,B_72,C_73] :
      ( r2_hidden(k4_tarski('#skF_2'(A_71,B_72,C_73),B_72),A_71)
      | r2_hidden('#skF_3'(A_71,B_72,C_73),C_73)
      | k1_wellord1(A_71,B_72) = C_73
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10,plain,(
    ! [B_9,C_10,A_8] :
      ( r2_hidden(B_9,k3_relat_1(C_10))
      | ~ r2_hidden(k4_tarski(A_8,B_9),C_10)
      | ~ v1_relat_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_270,plain,(
    ! [B_74,A_75,C_76] :
      ( r2_hidden(B_74,k3_relat_1(A_75))
      | r2_hidden('#skF_3'(A_75,B_74,C_76),C_76)
      | k1_wellord1(A_75,B_74) = C_76
      | ~ v1_relat_1(A_75) ) ),
    inference(resolution,[status(thm)],[c_202,c_10])).

tff(c_8,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_46,plain,(
    ! [A_27,B_28,C_29] :
      ( ~ r1_xboole_0(A_27,B_28)
      | ~ r2_hidden(C_29,k3_xboole_0(A_27,B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_49,plain,(
    ! [A_6,C_29] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_29,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_46])).

tff(c_51,plain,(
    ! [C_29] : ~ r2_hidden(C_29,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_49])).

tff(c_300,plain,(
    ! [B_77,A_78] :
      ( r2_hidden(B_77,k3_relat_1(A_78))
      | k1_wellord1(A_78,B_77) = k1_xboole_0
      | ~ v1_relat_1(A_78) ) ),
    inference(resolution,[status(thm)],[c_270,c_51])).

tff(c_34,plain,(
    ~ r2_hidden('#skF_4',k3_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_319,plain,
    ( k1_wellord1('#skF_5','#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_300,c_34])).

tff(c_326,plain,(
    k1_wellord1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_319])).

tff(c_328,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_326])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:51:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.39  
% 2.21/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.39  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k1_wellord1 > #nlpp > k3_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.21/1.39  
% 2.21/1.39  %Foreground sorts:
% 2.21/1.39  
% 2.21/1.39  
% 2.21/1.39  %Background operators:
% 2.21/1.39  
% 2.21/1.39  
% 2.21/1.39  %Foreground operators:
% 2.21/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.39  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.21/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.39  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.21/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.21/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.21/1.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.21/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.21/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.21/1.39  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 2.21/1.39  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.21/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.21/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.21/1.39  
% 2.45/1.40  tff(f_71, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k3_relat_1(B)) | (k1_wellord1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_wellord1)).
% 2.45/1.40  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k1_wellord1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (~(D = B) & r2_hidden(k4_tarski(D, B), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord1)).
% 2.45/1.40  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relat_1)).
% 2.45/1.40  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.45/1.40  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.45/1.40  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.45/1.40  tff(c_32, plain, (k1_wellord1('#skF_5', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.45/1.40  tff(c_36, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.45/1.40  tff(c_202, plain, (![A_71, B_72, C_73]: (r2_hidden(k4_tarski('#skF_2'(A_71, B_72, C_73), B_72), A_71) | r2_hidden('#skF_3'(A_71, B_72, C_73), C_73) | k1_wellord1(A_71, B_72)=C_73 | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.45/1.40  tff(c_10, plain, (![B_9, C_10, A_8]: (r2_hidden(B_9, k3_relat_1(C_10)) | ~r2_hidden(k4_tarski(A_8, B_9), C_10) | ~v1_relat_1(C_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.45/1.40  tff(c_270, plain, (![B_74, A_75, C_76]: (r2_hidden(B_74, k3_relat_1(A_75)) | r2_hidden('#skF_3'(A_75, B_74, C_76), C_76) | k1_wellord1(A_75, B_74)=C_76 | ~v1_relat_1(A_75))), inference(resolution, [status(thm)], [c_202, c_10])).
% 2.45/1.40  tff(c_8, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.45/1.40  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.45/1.40  tff(c_46, plain, (![A_27, B_28, C_29]: (~r1_xboole_0(A_27, B_28) | ~r2_hidden(C_29, k3_xboole_0(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.45/1.40  tff(c_49, plain, (![A_6, C_29]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_29, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_46])).
% 2.45/1.40  tff(c_51, plain, (![C_29]: (~r2_hidden(C_29, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_49])).
% 2.45/1.40  tff(c_300, plain, (![B_77, A_78]: (r2_hidden(B_77, k3_relat_1(A_78)) | k1_wellord1(A_78, B_77)=k1_xboole_0 | ~v1_relat_1(A_78))), inference(resolution, [status(thm)], [c_270, c_51])).
% 2.45/1.40  tff(c_34, plain, (~r2_hidden('#skF_4', k3_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.45/1.40  tff(c_319, plain, (k1_wellord1('#skF_5', '#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_300, c_34])).
% 2.45/1.40  tff(c_326, plain, (k1_wellord1('#skF_5', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_319])).
% 2.45/1.40  tff(c_328, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_326])).
% 2.45/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.40  
% 2.45/1.40  Inference rules
% 2.45/1.40  ----------------------
% 2.45/1.40  #Ref     : 0
% 2.45/1.40  #Sup     : 57
% 2.45/1.40  #Fact    : 0
% 2.45/1.40  #Define  : 0
% 2.45/1.40  #Split   : 1
% 2.45/1.40  #Chain   : 0
% 2.45/1.40  #Close   : 0
% 2.45/1.40  
% 2.45/1.40  Ordering : KBO
% 2.45/1.40  
% 2.45/1.40  Simplification rules
% 2.45/1.40  ----------------------
% 2.45/1.40  #Subsume      : 5
% 2.45/1.40  #Demod        : 10
% 2.45/1.40  #Tautology    : 7
% 2.45/1.40  #SimpNegUnit  : 2
% 2.45/1.40  #BackRed      : 0
% 2.45/1.40  
% 2.45/1.40  #Partial instantiations: 0
% 2.45/1.40  #Strategies tried      : 1
% 2.45/1.40  
% 2.45/1.40  Timing (in seconds)
% 2.45/1.40  ----------------------
% 2.45/1.40  Preprocessing        : 0.32
% 2.45/1.40  Parsing              : 0.17
% 2.45/1.40  CNF conversion       : 0.03
% 2.45/1.40  Main loop            : 0.26
% 2.45/1.40  Inferencing          : 0.10
% 2.45/1.40  Reduction            : 0.06
% 2.45/1.40  Demodulation         : 0.04
% 2.45/1.40  BG Simplification    : 0.02
% 2.45/1.40  Subsumption          : 0.06
% 2.45/1.40  Abstraction          : 0.02
% 2.45/1.40  MUC search           : 0.00
% 2.45/1.40  Cooper               : 0.00
% 2.45/1.40  Total                : 0.60
% 2.45/1.40  Index Insertion      : 0.00
% 2.45/1.40  Index Deletion       : 0.00
% 2.45/1.40  Index Matching       : 0.00
% 2.45/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
