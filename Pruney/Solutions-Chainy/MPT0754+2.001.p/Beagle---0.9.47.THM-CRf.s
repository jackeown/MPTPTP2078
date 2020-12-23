%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:30 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   37 (  45 expanded)
%              Number of leaves         :   18 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   52 ( 110 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r1_tarski > v5_ordinal1 > v1_relat_1 > v1_funct_1 > k2_xboole_0 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => ! [C] :
            ( ( v1_relat_1(C)
              & v5_relat_1(C,A)
              & v1_funct_1(C)
              & v5_ordinal1(C) )
           => ( v1_relat_1(C)
              & v5_relat_1(C,B)
              & v1_funct_1(C)
              & v5_ordinal1(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_ordinal1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k2_relat_1(B_9),A_8)
      | ~ v5_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_58,plain,(
    ! [A_13,B_14] :
      ( k2_xboole_0(A_13,B_14) = B_14
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_62,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_22,c_58])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_67,plain,(
    ! [A_15,C_16,B_17] :
      ( r1_tarski(A_15,k2_xboole_0(C_16,B_17))
      | ~ r1_tarski(A_15,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_81,plain,(
    ! [A_18,B_19,A_20] :
      ( r1_tarski(A_18,k2_xboole_0(B_19,A_20))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_67])).

tff(c_87,plain,(
    ! [A_18] :
      ( r1_tarski(A_18,'#skF_2')
      | ~ r1_tarski(A_18,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_81])).

tff(c_112,plain,(
    ! [B_25,A_26] :
      ( v5_relat_1(B_25,A_26)
      | ~ r1_tarski(k2_relat_1(B_25),A_26)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_132,plain,(
    ! [B_27] :
      ( v5_relat_1(B_27,'#skF_2')
      | ~ v1_relat_1(B_27)
      | ~ r1_tarski(k2_relat_1(B_27),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_87,c_112])).

tff(c_138,plain,(
    ! [B_28] :
      ( v5_relat_1(B_28,'#skF_2')
      | ~ v5_relat_1(B_28,'#skF_1')
      | ~ v1_relat_1(B_28) ) ),
    inference(resolution,[status(thm)],[c_10,c_132])).

tff(c_16,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    v5_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12,plain,
    ( ~ v5_ordinal1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_24,plain,(
    ~ v5_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_14,c_12])).

tff(c_141,plain,
    ( ~ v5_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_138,c_24])).

tff(c_145,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_141])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:36:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.16  
% 1.63/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.16  %$ v5_relat_1 > r1_tarski > v5_ordinal1 > v1_relat_1 > v1_funct_1 > k2_xboole_0 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.63/1.16  
% 1.63/1.16  %Foreground sorts:
% 1.63/1.16  
% 1.63/1.16  
% 1.63/1.16  %Background operators:
% 1.63/1.16  
% 1.63/1.16  
% 1.63/1.16  %Foreground operators:
% 1.63/1.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.63/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.63/1.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.63/1.16  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 1.63/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.63/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.16  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.63/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.63/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.63/1.16  
% 1.85/1.17  tff(f_61, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => (![C]: ((((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) & v5_ordinal1(C)) => (((v1_relat_1(C) & v5_relat_1(C, B)) & v1_funct_1(C)) & v5_ordinal1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_ordinal1)).
% 1.85/1.17  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 1.85/1.17  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.85/1.17  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.85/1.17  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 1.85/1.17  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.85/1.17  tff(c_18, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.85/1.17  tff(c_10, plain, (![B_9, A_8]: (r1_tarski(k2_relat_1(B_9), A_8) | ~v5_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.85/1.17  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.85/1.17  tff(c_58, plain, (![A_13, B_14]: (k2_xboole_0(A_13, B_14)=B_14 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.85/1.17  tff(c_62, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_22, c_58])).
% 1.85/1.17  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.85/1.17  tff(c_67, plain, (![A_15, C_16, B_17]: (r1_tarski(A_15, k2_xboole_0(C_16, B_17)) | ~r1_tarski(A_15, B_17))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.85/1.17  tff(c_81, plain, (![A_18, B_19, A_20]: (r1_tarski(A_18, k2_xboole_0(B_19, A_20)) | ~r1_tarski(A_18, B_19))), inference(superposition, [status(thm), theory('equality')], [c_2, c_67])).
% 1.85/1.17  tff(c_87, plain, (![A_18]: (r1_tarski(A_18, '#skF_2') | ~r1_tarski(A_18, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_81])).
% 1.85/1.17  tff(c_112, plain, (![B_25, A_26]: (v5_relat_1(B_25, A_26) | ~r1_tarski(k2_relat_1(B_25), A_26) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.85/1.17  tff(c_132, plain, (![B_27]: (v5_relat_1(B_27, '#skF_2') | ~v1_relat_1(B_27) | ~r1_tarski(k2_relat_1(B_27), '#skF_1'))), inference(resolution, [status(thm)], [c_87, c_112])).
% 1.85/1.17  tff(c_138, plain, (![B_28]: (v5_relat_1(B_28, '#skF_2') | ~v5_relat_1(B_28, '#skF_1') | ~v1_relat_1(B_28))), inference(resolution, [status(thm)], [c_10, c_132])).
% 1.85/1.17  tff(c_16, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.85/1.17  tff(c_14, plain, (v5_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.85/1.17  tff(c_12, plain, (~v5_ordinal1('#skF_3') | ~v1_funct_1('#skF_3') | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.85/1.17  tff(c_24, plain, (~v5_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_16, c_14, c_12])).
% 1.85/1.17  tff(c_141, plain, (~v5_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_138, c_24])).
% 1.85/1.17  tff(c_145, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_141])).
% 1.85/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.17  
% 1.85/1.17  Inference rules
% 1.85/1.17  ----------------------
% 1.85/1.17  #Ref     : 0
% 1.85/1.17  #Sup     : 28
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
% 1.85/1.17  #Subsume      : 3
% 1.85/1.17  #Demod        : 6
% 1.85/1.17  #Tautology    : 12
% 1.85/1.17  #SimpNegUnit  : 0
% 1.85/1.17  #BackRed      : 0
% 1.85/1.17  
% 1.85/1.17  #Partial instantiations: 0
% 1.85/1.17  #Strategies tried      : 1
% 1.85/1.17  
% 1.85/1.17  Timing (in seconds)
% 1.85/1.17  ----------------------
% 1.85/1.17  Preprocessing        : 0.26
% 1.85/1.17  Parsing              : 0.14
% 1.85/1.17  CNF conversion       : 0.02
% 1.85/1.17  Main loop            : 0.15
% 1.85/1.17  Inferencing          : 0.06
% 1.85/1.17  Reduction            : 0.04
% 1.85/1.17  Demodulation         : 0.03
% 1.85/1.17  BG Simplification    : 0.01
% 1.85/1.17  Subsumption          : 0.03
% 1.85/1.17  Abstraction          : 0.01
% 1.85/1.17  MUC search           : 0.00
% 1.85/1.17  Cooper               : 0.00
% 1.85/1.17  Total                : 0.43
% 1.85/1.17  Index Insertion      : 0.00
% 1.85/1.17  Index Deletion       : 0.00
% 1.85/1.17  Index Matching       : 0.00
% 1.85/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
