%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:12 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   31 (  34 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   38 (  50 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r2_hidden > r1_tarski > v1_relat_1 > k2_xboole_0 > #nlpp > k2_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v5_relat_1(B,A) )
       => ! [C] :
            ( r2_hidden(C,k2_relat_1(B))
           => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_26,plain,(
    ~ r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_30,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_32,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_28,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_37,plain,(
    ! [B_22,A_23] :
      ( r1_tarski(k2_relat_1(B_22),A_23)
      | ~ v5_relat_1(B_22,A_23)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_55,plain,(
    ! [B_27,A_28] :
      ( k2_xboole_0(k2_relat_1(B_27),A_28) = A_28
      | ~ v5_relat_1(B_27,A_28)
      | ~ v1_relat_1(B_27) ) ),
    inference(resolution,[status(thm)],[c_37,c_20])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( ~ r2_hidden(D_6,A_1)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_73,plain,(
    ! [D_29,B_30,A_31] :
      ( ~ r2_hidden(D_29,k2_relat_1(B_30))
      | r2_hidden(D_29,A_31)
      | ~ v5_relat_1(B_30,A_31)
      | ~ v1_relat_1(B_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_6])).

tff(c_75,plain,(
    ! [A_31] :
      ( r2_hidden('#skF_5',A_31)
      | ~ v5_relat_1('#skF_4',A_31)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_73])).

tff(c_79,plain,(
    ! [A_32] :
      ( r2_hidden('#skF_5',A_32)
      | ~ v5_relat_1('#skF_4',A_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_75])).

tff(c_82,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_79])).

tff(c_86,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_82])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:25:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.14  
% 1.65/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.14  %$ v5_relat_1 > r2_hidden > r1_tarski > v1_relat_1 > k2_xboole_0 > #nlpp > k2_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 1.65/1.14  
% 1.65/1.14  %Foreground sorts:
% 1.65/1.14  
% 1.65/1.14  
% 1.65/1.14  %Background operators:
% 1.65/1.14  
% 1.65/1.14  
% 1.65/1.14  %Foreground operators:
% 1.65/1.14  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.65/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.65/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.65/1.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.65/1.14  tff('#skF_5', type, '#skF_5': $i).
% 1.65/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.65/1.14  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.65/1.14  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.65/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.65/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.65/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.65/1.14  
% 1.65/1.16  tff(f_54, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (r2_hidden(C, k2_relat_1(B)) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t202_relat_1)).
% 1.65/1.16  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 1.65/1.16  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.65/1.16  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 1.65/1.16  tff(c_26, plain, (~r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.65/1.16  tff(c_30, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.65/1.16  tff(c_32, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.65/1.16  tff(c_28, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.65/1.16  tff(c_37, plain, (![B_22, A_23]: (r1_tarski(k2_relat_1(B_22), A_23) | ~v5_relat_1(B_22, A_23) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.65/1.16  tff(c_20, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.65/1.16  tff(c_55, plain, (![B_27, A_28]: (k2_xboole_0(k2_relat_1(B_27), A_28)=A_28 | ~v5_relat_1(B_27, A_28) | ~v1_relat_1(B_27))), inference(resolution, [status(thm)], [c_37, c_20])).
% 1.65/1.16  tff(c_6, plain, (![D_6, A_1, B_2]: (~r2_hidden(D_6, A_1) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.65/1.16  tff(c_73, plain, (![D_29, B_30, A_31]: (~r2_hidden(D_29, k2_relat_1(B_30)) | r2_hidden(D_29, A_31) | ~v5_relat_1(B_30, A_31) | ~v1_relat_1(B_30))), inference(superposition, [status(thm), theory('equality')], [c_55, c_6])).
% 1.65/1.16  tff(c_75, plain, (![A_31]: (r2_hidden('#skF_5', A_31) | ~v5_relat_1('#skF_4', A_31) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_73])).
% 1.65/1.16  tff(c_79, plain, (![A_32]: (r2_hidden('#skF_5', A_32) | ~v5_relat_1('#skF_4', A_32))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_75])).
% 1.65/1.16  tff(c_82, plain, (r2_hidden('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_79])).
% 1.65/1.16  tff(c_86, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_82])).
% 1.65/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.16  
% 1.65/1.16  Inference rules
% 1.65/1.16  ----------------------
% 1.65/1.16  #Ref     : 0
% 1.65/1.16  #Sup     : 11
% 1.65/1.16  #Fact    : 0
% 1.65/1.16  #Define  : 0
% 1.65/1.16  #Split   : 0
% 1.65/1.16  #Chain   : 0
% 1.65/1.16  #Close   : 0
% 1.65/1.16  
% 1.65/1.16  Ordering : KBO
% 1.65/1.16  
% 1.65/1.16  Simplification rules
% 1.65/1.16  ----------------------
% 1.65/1.16  #Subsume      : 0
% 1.65/1.16  #Demod        : 1
% 1.65/1.16  #Tautology    : 7
% 1.65/1.16  #SimpNegUnit  : 1
% 1.65/1.16  #BackRed      : 0
% 1.65/1.16  
% 1.65/1.16  #Partial instantiations: 0
% 1.65/1.16  #Strategies tried      : 1
% 1.65/1.16  
% 1.65/1.16  Timing (in seconds)
% 1.65/1.16  ----------------------
% 1.65/1.16  Preprocessing        : 0.26
% 1.65/1.16  Parsing              : 0.14
% 1.65/1.16  CNF conversion       : 0.02
% 1.65/1.16  Main loop            : 0.13
% 1.65/1.16  Inferencing          : 0.06
% 1.65/1.16  Reduction            : 0.04
% 1.65/1.16  Demodulation         : 0.03
% 1.65/1.16  BG Simplification    : 0.02
% 1.65/1.16  Subsumption          : 0.02
% 1.65/1.16  Abstraction          : 0.01
% 1.65/1.16  MUC search           : 0.00
% 1.65/1.16  Cooper               : 0.00
% 1.65/1.16  Total                : 0.43
% 1.65/1.16  Index Insertion      : 0.00
% 1.65/1.16  Index Deletion       : 0.00
% 1.65/1.16  Index Matching       : 0.00
% 1.65/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
