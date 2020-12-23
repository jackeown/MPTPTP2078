%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:32 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   29 (  35 expanded)
%              Number of leaves         :   16 (  21 expanded)
%              Depth                    :    4
%              Number of atoms          :   31 (  50 expanded)
%              Number of equality atoms :   11 (  12 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_49,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_xboole_0(B,C)
           => r1_xboole_0(k10_relat_1(A,B),k10_relat_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t141_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_funct_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_17,plain,(
    ! [A_9] :
      ( k10_relat_1(A_9,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_21,plain,(
    k10_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_17])).

tff(c_12,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_31,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = k1_xboole_0
      | ~ r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_39,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_31])).

tff(c_44,plain,(
    ! [C_14,A_15,B_16] :
      ( k3_xboole_0(k10_relat_1(C_14,A_15),k10_relat_1(C_14,B_16)) = k10_relat_1(C_14,k3_xboole_0(A_15,B_16))
      | ~ v1_funct_1(C_14)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    ! [A_10,B_11] :
      ( r1_xboole_0(A_10,B_11)
      | k3_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ~ r1_xboole_0(k10_relat_1('#skF_1','#skF_2'),k10_relat_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30,plain,(
    k3_xboole_0(k10_relat_1('#skF_1','#skF_2'),k10_relat_1('#skF_1','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_10])).

tff(c_50,plain,
    ( k10_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')) != k1_xboole_0
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_30])).

tff(c_63,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_21,c_39,c_50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:06:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.16  
% 1.73/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.16  %$ r1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.73/1.16  
% 1.73/1.16  %Foreground sorts:
% 1.73/1.16  
% 1.73/1.16  
% 1.73/1.16  %Background operators:
% 1.73/1.16  
% 1.73/1.16  
% 1.73/1.16  %Foreground operators:
% 1.73/1.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.73/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.73/1.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.73/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.73/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.73/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.73/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.16  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.73/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.73/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.73/1.16  
% 1.73/1.17  tff(f_49, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_xboole_0(B, C) => r1_xboole_0(k10_relat_1(A, B), k10_relat_1(A, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t141_funct_1)).
% 1.73/1.17  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_relat_1)).
% 1.73/1.17  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.73/1.17  tff(f_39, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_funct_1)).
% 1.73/1.17  tff(c_16, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.73/1.17  tff(c_14, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.73/1.17  tff(c_17, plain, (![A_9]: (k10_relat_1(A_9, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.73/1.17  tff(c_21, plain, (k10_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_17])).
% 1.73/1.17  tff(c_12, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.73/1.17  tff(c_31, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=k1_xboole_0 | ~r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.73/1.17  tff(c_39, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_31])).
% 1.73/1.17  tff(c_44, plain, (![C_14, A_15, B_16]: (k3_xboole_0(k10_relat_1(C_14, A_15), k10_relat_1(C_14, B_16))=k10_relat_1(C_14, k3_xboole_0(A_15, B_16)) | ~v1_funct_1(C_14) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.73/1.17  tff(c_26, plain, (![A_10, B_11]: (r1_xboole_0(A_10, B_11) | k3_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.73/1.17  tff(c_10, plain, (~r1_xboole_0(k10_relat_1('#skF_1', '#skF_2'), k10_relat_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.73/1.17  tff(c_30, plain, (k3_xboole_0(k10_relat_1('#skF_1', '#skF_2'), k10_relat_1('#skF_1', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_10])).
% 1.73/1.17  tff(c_50, plain, (k10_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))!=k1_xboole_0 | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_44, c_30])).
% 1.73/1.17  tff(c_63, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_21, c_39, c_50])).
% 1.73/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.17  
% 1.73/1.17  Inference rules
% 1.73/1.17  ----------------------
% 1.73/1.17  #Ref     : 0
% 1.73/1.17  #Sup     : 13
% 1.73/1.17  #Fact    : 0
% 1.73/1.17  #Define  : 0
% 1.73/1.17  #Split   : 0
% 1.73/1.17  #Chain   : 0
% 1.73/1.17  #Close   : 0
% 1.73/1.17  
% 1.73/1.17  Ordering : KBO
% 1.73/1.17  
% 1.73/1.17  Simplification rules
% 1.73/1.17  ----------------------
% 1.73/1.17  #Subsume      : 0
% 1.73/1.17  #Demod        : 4
% 1.73/1.17  #Tautology    : 6
% 1.73/1.17  #SimpNegUnit  : 0
% 1.73/1.17  #BackRed      : 0
% 1.73/1.17  
% 1.73/1.17  #Partial instantiations: 0
% 1.73/1.17  #Strategies tried      : 1
% 1.73/1.17  
% 1.73/1.17  Timing (in seconds)
% 1.73/1.17  ----------------------
% 1.73/1.17  Preprocessing        : 0.26
% 1.73/1.17  Parsing              : 0.16
% 1.73/1.17  CNF conversion       : 0.01
% 1.73/1.17  Main loop            : 0.09
% 1.73/1.17  Inferencing          : 0.04
% 1.73/1.17  Reduction            : 0.02
% 1.73/1.17  Demodulation         : 0.02
% 1.73/1.17  BG Simplification    : 0.01
% 1.73/1.17  Subsumption          : 0.01
% 1.73/1.17  Abstraction          : 0.00
% 1.73/1.17  MUC search           : 0.00
% 1.73/1.17  Cooper               : 0.00
% 1.73/1.17  Total                : 0.38
% 1.73/1.17  Index Insertion      : 0.00
% 1.73/1.17  Index Deletion       : 0.00
% 1.73/1.17  Index Matching       : 0.00
% 1.73/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
