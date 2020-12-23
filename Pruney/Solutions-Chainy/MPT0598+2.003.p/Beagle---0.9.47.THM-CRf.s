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
% DateTime   : Thu Dec  3 10:02:13 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
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
%$ v5_relat_1 > r2_hidden > r1_tarski > v1_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v5_relat_1(B,A) )
       => ! [C] :
            ( r2_hidden(C,k2_relat_1(B))
           => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

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
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_55,plain,(
    ! [B_27,A_28] :
      ( k3_xboole_0(k2_relat_1(B_27),A_28) = k2_relat_1(B_27)
      | ~ v5_relat_1(B_27,A_28)
      | ~ v1_relat_1(B_27) ) ),
    inference(resolution,[status(thm)],[c_37,c_20])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_73,plain,(
    ! [D_29,A_30,B_31] :
      ( r2_hidden(D_29,A_30)
      | ~ r2_hidden(D_29,k2_relat_1(B_31))
      | ~ v5_relat_1(B_31,A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_4])).

tff(c_75,plain,(
    ! [A_30] :
      ( r2_hidden('#skF_5',A_30)
      | ~ v5_relat_1('#skF_4',A_30)
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
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:08:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.46  
% 2.14/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.47  %$ v5_relat_1 > r2_hidden > r1_tarski > v1_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 2.14/1.47  
% 2.14/1.47  %Foreground sorts:
% 2.14/1.47  
% 2.14/1.47  
% 2.14/1.47  %Background operators:
% 2.14/1.47  
% 2.14/1.47  
% 2.14/1.47  %Foreground operators:
% 2.14/1.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.14/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.14/1.47  tff('#skF_5', type, '#skF_5': $i).
% 2.14/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.14/1.47  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.14/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.14/1.47  tff('#skF_4', type, '#skF_4': $i).
% 2.14/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.14/1.47  
% 2.14/1.48  tff(f_54, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (r2_hidden(C, k2_relat_1(B)) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t202_relat_1)).
% 2.14/1.48  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.14/1.48  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.14/1.48  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.14/1.48  tff(c_26, plain, (~r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.14/1.48  tff(c_30, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.14/1.48  tff(c_32, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.14/1.48  tff(c_28, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.14/1.48  tff(c_37, plain, (![B_22, A_23]: (r1_tarski(k2_relat_1(B_22), A_23) | ~v5_relat_1(B_22, A_23) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.14/1.48  tff(c_20, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.14/1.48  tff(c_55, plain, (![B_27, A_28]: (k3_xboole_0(k2_relat_1(B_27), A_28)=k2_relat_1(B_27) | ~v5_relat_1(B_27, A_28) | ~v1_relat_1(B_27))), inference(resolution, [status(thm)], [c_37, c_20])).
% 2.14/1.48  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.14/1.48  tff(c_73, plain, (![D_29, A_30, B_31]: (r2_hidden(D_29, A_30) | ~r2_hidden(D_29, k2_relat_1(B_31)) | ~v5_relat_1(B_31, A_30) | ~v1_relat_1(B_31))), inference(superposition, [status(thm), theory('equality')], [c_55, c_4])).
% 2.14/1.48  tff(c_75, plain, (![A_30]: (r2_hidden('#skF_5', A_30) | ~v5_relat_1('#skF_4', A_30) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_73])).
% 2.14/1.48  tff(c_79, plain, (![A_32]: (r2_hidden('#skF_5', A_32) | ~v5_relat_1('#skF_4', A_32))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_75])).
% 2.14/1.48  tff(c_82, plain, (r2_hidden('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_79])).
% 2.14/1.48  tff(c_86, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_82])).
% 2.14/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.48  
% 2.14/1.48  Inference rules
% 2.14/1.48  ----------------------
% 2.14/1.48  #Ref     : 0
% 2.14/1.48  #Sup     : 11
% 2.14/1.48  #Fact    : 0
% 2.14/1.48  #Define  : 0
% 2.14/1.48  #Split   : 0
% 2.14/1.48  #Chain   : 0
% 2.14/1.48  #Close   : 0
% 2.14/1.48  
% 2.14/1.48  Ordering : KBO
% 2.14/1.48  
% 2.14/1.48  Simplification rules
% 2.14/1.48  ----------------------
% 2.14/1.48  #Subsume      : 0
% 2.14/1.48  #Demod        : 1
% 2.14/1.48  #Tautology    : 7
% 2.14/1.48  #SimpNegUnit  : 1
% 2.14/1.48  #BackRed      : 0
% 2.14/1.48  
% 2.14/1.48  #Partial instantiations: 0
% 2.14/1.48  #Strategies tried      : 1
% 2.14/1.48  
% 2.14/1.48  Timing (in seconds)
% 2.14/1.48  ----------------------
% 2.14/1.48  Preprocessing        : 0.44
% 2.14/1.48  Parsing              : 0.24
% 2.14/1.48  CNF conversion       : 0.03
% 2.14/1.48  Main loop            : 0.19
% 2.14/1.49  Inferencing          : 0.08
% 2.14/1.49  Reduction            : 0.05
% 2.14/1.49  Demodulation         : 0.04
% 2.14/1.49  BG Simplification    : 0.02
% 2.14/1.49  Subsumption          : 0.03
% 2.14/1.49  Abstraction          : 0.01
% 2.14/1.49  MUC search           : 0.00
% 2.14/1.49  Cooper               : 0.00
% 2.14/1.49  Total                : 0.67
% 2.14/1.49  Index Insertion      : 0.00
% 2.14/1.49  Index Deletion       : 0.00
% 2.14/1.49  Index Matching       : 0.00
% 2.14/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
