%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:32 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   33 (  39 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :    4
%              Number of atoms          :   37 (  56 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_53,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_xboole_0(B,C)
           => r1_xboole_0(k10_relat_1(A,B),k10_relat_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_funct_1)).

tff(f_31,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_funct_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_51,plain,(
    ! [B_17,A_18] :
      ( k10_relat_1(B_17,A_18) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_17),A_18)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_62,plain,(
    ! [B_19] :
      ( k10_relat_1(B_19,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_19) ) ),
    inference(resolution,[status(thm)],[c_6,c_51])).

tff(c_66,plain,(
    k10_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_62])).

tff(c_16,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_27,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = k1_xboole_0
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_38,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_27])).

tff(c_86,plain,(
    ! [C_24,A_25,B_26] :
      ( k3_xboole_0(k10_relat_1(C_24,A_25),k10_relat_1(C_24,B_26)) = k10_relat_1(C_24,k3_xboole_0(A_25,B_26))
      | ~ v1_funct_1(C_24)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ~ r1_xboole_0(k10_relat_1('#skF_1','#skF_2'),k10_relat_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_26,plain,(
    k3_xboole_0(k10_relat_1('#skF_1','#skF_2'),k10_relat_1('#skF_1','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_14])).

tff(c_92,plain,
    ( k10_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')) != k1_xboole_0
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_26])).

tff(c_105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_66,c_38,c_92])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:24:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.14  
% 1.63/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.14  %$ r1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.63/1.14  
% 1.63/1.14  %Foreground sorts:
% 1.63/1.14  
% 1.63/1.14  
% 1.63/1.14  %Background operators:
% 1.63/1.14  
% 1.63/1.14  
% 1.63/1.14  %Foreground operators:
% 1.63/1.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.63/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.63/1.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.63/1.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.63/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.63/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.14  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.63/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.63/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.63/1.14  
% 1.63/1.15  tff(f_53, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_xboole_0(B, C) => r1_xboole_0(k10_relat_1(A, B), k10_relat_1(A, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t141_funct_1)).
% 1.63/1.15  tff(f_31, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.63/1.15  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 1.63/1.15  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.63/1.15  tff(f_43, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_funct_1)).
% 1.63/1.15  tff(c_20, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.63/1.15  tff(c_18, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.63/1.15  tff(c_6, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.63/1.15  tff(c_51, plain, (![B_17, A_18]: (k10_relat_1(B_17, A_18)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_17), A_18) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.63/1.15  tff(c_62, plain, (![B_19]: (k10_relat_1(B_19, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_19))), inference(resolution, [status(thm)], [c_6, c_51])).
% 1.63/1.15  tff(c_66, plain, (k10_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_62])).
% 1.63/1.15  tff(c_16, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.63/1.15  tff(c_27, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=k1_xboole_0 | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.63/1.15  tff(c_38, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_27])).
% 1.63/1.15  tff(c_86, plain, (![C_24, A_25, B_26]: (k3_xboole_0(k10_relat_1(C_24, A_25), k10_relat_1(C_24, B_26))=k10_relat_1(C_24, k3_xboole_0(A_25, B_26)) | ~v1_funct_1(C_24) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.63/1.15  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.63/1.15  tff(c_14, plain, (~r1_xboole_0(k10_relat_1('#skF_1', '#skF_2'), k10_relat_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.63/1.15  tff(c_26, plain, (k3_xboole_0(k10_relat_1('#skF_1', '#skF_2'), k10_relat_1('#skF_1', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_14])).
% 1.63/1.15  tff(c_92, plain, (k10_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))!=k1_xboole_0 | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_86, c_26])).
% 1.63/1.15  tff(c_105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_66, c_38, c_92])).
% 1.63/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.15  
% 1.63/1.15  Inference rules
% 1.80/1.15  ----------------------
% 1.80/1.15  #Ref     : 0
% 1.80/1.15  #Sup     : 21
% 1.80/1.15  #Fact    : 0
% 1.80/1.15  #Define  : 0
% 1.80/1.15  #Split   : 0
% 1.80/1.15  #Chain   : 0
% 1.80/1.15  #Close   : 0
% 1.80/1.15  
% 1.80/1.15  Ordering : KBO
% 1.80/1.15  
% 1.80/1.15  Simplification rules
% 1.80/1.15  ----------------------
% 1.80/1.15  #Subsume      : 1
% 1.80/1.15  #Demod        : 4
% 1.80/1.15  #Tautology    : 9
% 1.80/1.15  #SimpNegUnit  : 0
% 1.80/1.15  #BackRed      : 0
% 1.80/1.15  
% 1.80/1.15  #Partial instantiations: 0
% 1.80/1.15  #Strategies tried      : 1
% 1.80/1.15  
% 1.80/1.15  Timing (in seconds)
% 1.80/1.15  ----------------------
% 1.80/1.15  Preprocessing        : 0.26
% 1.80/1.15  Parsing              : 0.15
% 1.80/1.15  CNF conversion       : 0.02
% 1.80/1.15  Main loop            : 0.12
% 1.80/1.15  Inferencing          : 0.06
% 1.80/1.15  Reduction            : 0.03
% 1.80/1.15  Demodulation         : 0.02
% 1.80/1.15  BG Simplification    : 0.01
% 1.80/1.15  Subsumption          : 0.02
% 1.80/1.15  Abstraction          : 0.01
% 1.80/1.15  MUC search           : 0.00
% 1.80/1.15  Cooper               : 0.00
% 1.80/1.15  Total                : 0.41
% 1.80/1.15  Index Insertion      : 0.00
% 1.80/1.15  Index Deletion       : 0.00
% 1.80/1.15  Index Matching       : 0.00
% 1.80/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
