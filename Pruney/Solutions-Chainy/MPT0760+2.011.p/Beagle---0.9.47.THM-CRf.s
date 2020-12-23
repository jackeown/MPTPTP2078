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
% DateTime   : Thu Dec  3 10:06:35 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   29 (  31 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   35 (  41 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k3_relat_1(B))
          | k1_wellord1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_wellord1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k1_wellord1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( D != B
                & r2_hidden(k4_tarski(D,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

tff(c_26,plain,(
    k1_wellord1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_30,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_35,plain,(
    ! [D_27,B_28,A_29] :
      ( r2_hidden(k4_tarski(D_27,B_28),A_29)
      | ~ r2_hidden(D_27,k1_wellord1(A_29,B_28))
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4,plain,(
    ! [B_4,C_5,A_3] :
      ( r2_hidden(B_4,k3_relat_1(C_5))
      | ~ r2_hidden(k4_tarski(A_3,B_4),C_5)
      | ~ v1_relat_1(C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_65,plain,(
    ! [B_36,A_37,D_38] :
      ( r2_hidden(B_36,k3_relat_1(A_37))
      | ~ r2_hidden(D_38,k1_wellord1(A_37,B_36))
      | ~ v1_relat_1(A_37) ) ),
    inference(resolution,[status(thm)],[c_35,c_4])).

tff(c_74,plain,(
    ! [B_39,A_40] :
      ( r2_hidden(B_39,k3_relat_1(A_40))
      | ~ v1_relat_1(A_40)
      | k1_wellord1(A_40,B_39) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_65])).

tff(c_28,plain,(
    ~ r2_hidden('#skF_4',k3_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_89,plain,
    ( ~ v1_relat_1('#skF_5')
    | k1_wellord1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_74,c_28])).

tff(c_95,plain,(
    k1_wellord1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_89])).

tff(c_97,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_95])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:50:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.16  
% 1.66/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.16  %$ r2_hidden > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 1.66/1.16  
% 1.66/1.16  %Foreground sorts:
% 1.66/1.16  
% 1.66/1.16  
% 1.66/1.16  %Background operators:
% 1.66/1.16  
% 1.66/1.16  
% 1.66/1.16  %Foreground operators:
% 1.66/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.66/1.16  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.66/1.16  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.66/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.66/1.16  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.66/1.16  tff('#skF_5', type, '#skF_5': $i).
% 1.66/1.16  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.66/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.66/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.66/1.16  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 1.66/1.16  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.66/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.16  
% 1.85/1.17  tff(f_61, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k3_relat_1(B)) | (k1_wellord1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_wellord1)).
% 1.85/1.17  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.85/1.17  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k1_wellord1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (~(D = B) & r2_hidden(k4_tarski(D, B), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord1)).
% 1.85/1.17  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relat_1)).
% 1.85/1.17  tff(c_26, plain, (k1_wellord1('#skF_5', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.85/1.17  tff(c_30, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.85/1.17  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.85/1.17  tff(c_35, plain, (![D_27, B_28, A_29]: (r2_hidden(k4_tarski(D_27, B_28), A_29) | ~r2_hidden(D_27, k1_wellord1(A_29, B_28)) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.85/1.17  tff(c_4, plain, (![B_4, C_5, A_3]: (r2_hidden(B_4, k3_relat_1(C_5)) | ~r2_hidden(k4_tarski(A_3, B_4), C_5) | ~v1_relat_1(C_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.85/1.17  tff(c_65, plain, (![B_36, A_37, D_38]: (r2_hidden(B_36, k3_relat_1(A_37)) | ~r2_hidden(D_38, k1_wellord1(A_37, B_36)) | ~v1_relat_1(A_37))), inference(resolution, [status(thm)], [c_35, c_4])).
% 1.85/1.17  tff(c_74, plain, (![B_39, A_40]: (r2_hidden(B_39, k3_relat_1(A_40)) | ~v1_relat_1(A_40) | k1_wellord1(A_40, B_39)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_65])).
% 1.85/1.17  tff(c_28, plain, (~r2_hidden('#skF_4', k3_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.85/1.17  tff(c_89, plain, (~v1_relat_1('#skF_5') | k1_wellord1('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_74, c_28])).
% 1.85/1.17  tff(c_95, plain, (k1_wellord1('#skF_5', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_89])).
% 1.85/1.17  tff(c_97, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_95])).
% 1.85/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.17  
% 1.85/1.17  Inference rules
% 1.85/1.17  ----------------------
% 1.85/1.17  #Ref     : 0
% 1.85/1.17  #Sup     : 12
% 1.85/1.17  #Fact    : 0
% 1.85/1.17  #Define  : 0
% 1.85/1.17  #Split   : 0
% 1.85/1.17  #Chain   : 0
% 1.85/1.17  #Close   : 0
% 1.85/1.17  
% 1.85/1.17  Ordering : KBO
% 1.85/1.17  
% 1.85/1.17  Simplification rules
% 1.85/1.17  ----------------------
% 1.85/1.17  #Subsume      : 0
% 1.85/1.17  #Demod        : 1
% 1.85/1.17  #Tautology    : 1
% 1.85/1.17  #SimpNegUnit  : 1
% 1.85/1.17  #BackRed      : 0
% 1.85/1.17  
% 1.85/1.17  #Partial instantiations: 0
% 1.85/1.17  #Strategies tried      : 1
% 1.85/1.17  
% 1.85/1.17  Timing (in seconds)
% 1.85/1.17  ----------------------
% 1.85/1.17  Preprocessing        : 0.29
% 1.85/1.17  Parsing              : 0.16
% 1.85/1.18  CNF conversion       : 0.02
% 1.85/1.18  Main loop            : 0.12
% 1.85/1.18  Inferencing          : 0.05
% 1.85/1.18  Reduction            : 0.03
% 1.85/1.18  Demodulation         : 0.02
% 1.85/1.18  BG Simplification    : 0.01
% 1.85/1.18  Subsumption          : 0.03
% 1.85/1.18  Abstraction          : 0.01
% 1.85/1.18  MUC search           : 0.00
% 1.85/1.18  Cooper               : 0.00
% 1.85/1.18  Total                : 0.43
% 1.85/1.18  Index Insertion      : 0.00
% 1.85/1.18  Index Deletion       : 0.00
% 1.85/1.18  Index Matching       : 0.00
% 1.85/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
