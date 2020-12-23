%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:36 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   32 (  45 expanded)
%              Number of leaves         :   16 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :   57 ( 113 expanded)
%              Number of equality atoms :   12 (  22 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_wellord1 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ~ ( v2_wellord1(A)
            & k3_relat_1(A) != k1_xboole_0
            & ! [B] :
                ~ ( r2_hidden(B,k3_relat_1(A))
                  & ! [C] :
                      ( r2_hidden(C,k3_relat_1(A))
                     => r2_hidden(k4_tarski(B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
       => ! [B] :
            ~ ( r1_tarski(B,k3_relat_1(A))
              & B != k1_xboole_0
              & ! [C] :
                  ~ ( r2_hidden(C,B)
                    & ! [D] :
                        ( r2_hidden(D,B)
                       => r2_hidden(k4_tarski(C,D),A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord1)).

tff(c_12,plain,(
    k3_relat_1('#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_14,plain,(
    v2_wellord1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_3,B_11] :
      ( r2_hidden('#skF_1'(A_3,B_11),B_11)
      | k1_xboole_0 = B_11
      | ~ r1_tarski(B_11,k3_relat_1(A_3))
      | ~ v2_wellord1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    ! [B_20] :
      ( r2_hidden('#skF_3'(B_20),k3_relat_1('#skF_2'))
      | ~ r2_hidden(B_20,k3_relat_1('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_33,plain,(
    ! [A_29,B_30,D_31] :
      ( r2_hidden(k4_tarski('#skF_1'(A_29,B_30),D_31),A_29)
      | ~ r2_hidden(D_31,B_30)
      | k1_xboole_0 = B_30
      | ~ r1_tarski(B_30,k3_relat_1(A_29))
      | ~ v2_wellord1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18,plain,(
    ! [B_20] :
      ( ~ r2_hidden(k4_tarski(B_20,'#skF_3'(B_20)),'#skF_2')
      | ~ r2_hidden(B_20,k3_relat_1('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_37,plain,(
    ! [B_30] :
      ( ~ r2_hidden('#skF_1'('#skF_2',B_30),k3_relat_1('#skF_2'))
      | ~ r2_hidden('#skF_3'('#skF_1'('#skF_2',B_30)),B_30)
      | k1_xboole_0 = B_30
      | ~ r1_tarski(B_30,k3_relat_1('#skF_2'))
      | ~ v2_wellord1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_33,c_18])).

tff(c_41,plain,(
    ! [B_32] :
      ( ~ r2_hidden('#skF_1'('#skF_2',B_32),k3_relat_1('#skF_2'))
      | ~ r2_hidden('#skF_3'('#skF_1'('#skF_2',B_32)),B_32)
      | k1_xboole_0 = B_32
      | ~ r1_tarski(B_32,k3_relat_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_37])).

tff(c_45,plain,
    ( k3_relat_1('#skF_2') = k1_xboole_0
    | ~ r1_tarski(k3_relat_1('#skF_2'),k3_relat_1('#skF_2'))
    | ~ r2_hidden('#skF_1'('#skF_2',k3_relat_1('#skF_2')),k3_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_20,c_41])).

tff(c_48,plain,
    ( k3_relat_1('#skF_2') = k1_xboole_0
    | ~ r2_hidden('#skF_1'('#skF_2',k3_relat_1('#skF_2')),k3_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_45])).

tff(c_49,plain,(
    ~ r2_hidden('#skF_1'('#skF_2',k3_relat_1('#skF_2')),k3_relat_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_48])).

tff(c_52,plain,
    ( k3_relat_1('#skF_2') = k1_xboole_0
    | ~ r1_tarski(k3_relat_1('#skF_2'),k3_relat_1('#skF_2'))
    | ~ v2_wellord1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_49])).

tff(c_55,plain,(
    k3_relat_1('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_6,c_52])).

tff(c_57,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_55])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:51:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.20  
% 1.70/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.20  %$ r2_hidden > r1_tarski > v2_wellord1 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.70/1.20  
% 1.70/1.20  %Foreground sorts:
% 1.70/1.20  
% 1.70/1.20  
% 1.70/1.20  %Background operators:
% 1.70/1.20  
% 1.70/1.20  
% 1.70/1.20  %Foreground operators:
% 1.70/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.70/1.20  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.70/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.70/1.20  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.70/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.70/1.20  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 1.70/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.70/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.70/1.20  tff('#skF_3', type, '#skF_3': $i > $i).
% 1.70/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.70/1.20  
% 1.70/1.21  tff(f_69, negated_conjecture, ~(![A]: (v1_relat_1(A) => ~((v2_wellord1(A) & ~(k3_relat_1(A) = k1_xboole_0)) & (![B]: ~(r2_hidden(B, k3_relat_1(A)) & (![C]: (r2_hidden(C, k3_relat_1(A)) => r2_hidden(k4_tarski(B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_wellord1)).
% 1.70/1.21  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.70/1.21  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) => (![B]: ~((r1_tarski(B, k3_relat_1(A)) & ~(B = k1_xboole_0)) & (![C]: ~(r2_hidden(C, B) & (![D]: (r2_hidden(D, B) => r2_hidden(k4_tarski(C, D), A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_wellord1)).
% 1.70/1.21  tff(c_12, plain, (k3_relat_1('#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.70/1.21  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.70/1.21  tff(c_14, plain, (v2_wellord1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.70/1.21  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.70/1.21  tff(c_10, plain, (![A_3, B_11]: (r2_hidden('#skF_1'(A_3, B_11), B_11) | k1_xboole_0=B_11 | ~r1_tarski(B_11, k3_relat_1(A_3)) | ~v2_wellord1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.70/1.21  tff(c_20, plain, (![B_20]: (r2_hidden('#skF_3'(B_20), k3_relat_1('#skF_2')) | ~r2_hidden(B_20, k3_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.70/1.21  tff(c_33, plain, (![A_29, B_30, D_31]: (r2_hidden(k4_tarski('#skF_1'(A_29, B_30), D_31), A_29) | ~r2_hidden(D_31, B_30) | k1_xboole_0=B_30 | ~r1_tarski(B_30, k3_relat_1(A_29)) | ~v2_wellord1(A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.70/1.21  tff(c_18, plain, (![B_20]: (~r2_hidden(k4_tarski(B_20, '#skF_3'(B_20)), '#skF_2') | ~r2_hidden(B_20, k3_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.70/1.21  tff(c_37, plain, (![B_30]: (~r2_hidden('#skF_1'('#skF_2', B_30), k3_relat_1('#skF_2')) | ~r2_hidden('#skF_3'('#skF_1'('#skF_2', B_30)), B_30) | k1_xboole_0=B_30 | ~r1_tarski(B_30, k3_relat_1('#skF_2')) | ~v2_wellord1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_33, c_18])).
% 1.70/1.21  tff(c_41, plain, (![B_32]: (~r2_hidden('#skF_1'('#skF_2', B_32), k3_relat_1('#skF_2')) | ~r2_hidden('#skF_3'('#skF_1'('#skF_2', B_32)), B_32) | k1_xboole_0=B_32 | ~r1_tarski(B_32, k3_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_37])).
% 1.70/1.21  tff(c_45, plain, (k3_relat_1('#skF_2')=k1_xboole_0 | ~r1_tarski(k3_relat_1('#skF_2'), k3_relat_1('#skF_2')) | ~r2_hidden('#skF_1'('#skF_2', k3_relat_1('#skF_2')), k3_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_20, c_41])).
% 1.70/1.21  tff(c_48, plain, (k3_relat_1('#skF_2')=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_2', k3_relat_1('#skF_2')), k3_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_45])).
% 1.70/1.21  tff(c_49, plain, (~r2_hidden('#skF_1'('#skF_2', k3_relat_1('#skF_2')), k3_relat_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_12, c_48])).
% 1.70/1.21  tff(c_52, plain, (k3_relat_1('#skF_2')=k1_xboole_0 | ~r1_tarski(k3_relat_1('#skF_2'), k3_relat_1('#skF_2')) | ~v2_wellord1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10, c_49])).
% 1.70/1.21  tff(c_55, plain, (k3_relat_1('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_6, c_52])).
% 1.70/1.21  tff(c_57, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_55])).
% 1.70/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.21  
% 1.70/1.21  Inference rules
% 1.70/1.21  ----------------------
% 1.70/1.21  #Ref     : 0
% 1.70/1.21  #Sup     : 4
% 1.70/1.21  #Fact    : 0
% 1.70/1.21  #Define  : 0
% 1.70/1.21  #Split   : 0
% 1.70/1.21  #Chain   : 0
% 1.70/1.21  #Close   : 0
% 1.70/1.21  
% 1.70/1.21  Ordering : KBO
% 1.70/1.21  
% 1.70/1.21  Simplification rules
% 1.70/1.21  ----------------------
% 1.70/1.21  #Subsume      : 0
% 1.70/1.21  #Demod        : 8
% 1.70/1.21  #Tautology    : 2
% 1.70/1.21  #SimpNegUnit  : 2
% 1.70/1.21  #BackRed      : 0
% 1.70/1.21  
% 1.70/1.21  #Partial instantiations: 0
% 1.70/1.21  #Strategies tried      : 1
% 1.70/1.21  
% 1.70/1.21  Timing (in seconds)
% 1.70/1.21  ----------------------
% 1.70/1.21  Preprocessing        : 0.27
% 1.70/1.21  Parsing              : 0.16
% 1.70/1.21  CNF conversion       : 0.02
% 1.70/1.21  Main loop            : 0.10
% 1.70/1.21  Inferencing          : 0.04
% 1.70/1.21  Reduction            : 0.02
% 1.70/1.21  Demodulation         : 0.02
% 1.70/1.21  BG Simplification    : 0.01
% 1.70/1.21  Subsumption          : 0.02
% 1.70/1.21  Abstraction          : 0.00
% 1.70/1.21  MUC search           : 0.00
% 1.70/1.21  Cooper               : 0.00
% 1.70/1.21  Total                : 0.39
% 1.70/1.21  Index Insertion      : 0.00
% 1.70/1.21  Index Deletion       : 0.00
% 1.70/1.21  Index Matching       : 0.00
% 1.70/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
