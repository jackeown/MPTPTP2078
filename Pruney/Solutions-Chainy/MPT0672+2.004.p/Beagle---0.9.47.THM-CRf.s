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
% DateTime   : Thu Dec  3 10:04:21 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   35 (  43 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   52 (  81 expanded)
%              Number of equality atoms :   13 (  25 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k8_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r1_tarski(A,B)
         => ( k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C)
            & k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(A,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_funct_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_276,plain,(
    ! [A_43,B_44,C_45] :
      ( k8_relat_1(A_43,k8_relat_1(B_44,C_45)) = k8_relat_1(A_43,C_45)
      | ~ r1_tarski(A_43,B_44)
      | ~ v1_relat_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(k8_relat_1(A_4,B_5))
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_6,B_7)),A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_21,plain,(
    ! [A_17,C_18,B_19] :
      ( r1_tarski(A_17,C_18)
      | ~ r1_tarski(B_19,C_18)
      | ~ r1_tarski(A_17,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_27,plain,(
    ! [A_17] :
      ( r1_tarski(A_17,'#skF_2')
      | ~ r1_tarski(A_17,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_14,c_21])).

tff(c_43,plain,(
    ! [A_23,B_24] :
      ( k8_relat_1(A_23,B_24) = B_24
      | ~ r1_tarski(k2_relat_1(B_24),A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_54,plain,(
    ! [B_25] :
      ( k8_relat_1('#skF_2',B_25) = B_25
      | ~ v1_relat_1(B_25)
      | ~ r1_tarski(k2_relat_1(B_25),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_27,c_43])).

tff(c_144,plain,(
    ! [B_39] :
      ( k8_relat_1('#skF_2',k8_relat_1('#skF_1',B_39)) = k8_relat_1('#skF_1',B_39)
      | ~ v1_relat_1(k8_relat_1('#skF_1',B_39))
      | ~ v1_relat_1(B_39) ) ),
    inference(resolution,[status(thm)],[c_6,c_54])).

tff(c_210,plain,(
    ! [B_42] :
      ( k8_relat_1('#skF_2',k8_relat_1('#skF_1',B_42)) = k8_relat_1('#skF_1',B_42)
      | ~ v1_relat_1(B_42) ) ),
    inference(resolution,[status(thm)],[c_4,c_144])).

tff(c_12,plain,
    ( k8_relat_1('#skF_1',k8_relat_1('#skF_2','#skF_3')) != k8_relat_1('#skF_1','#skF_3')
    | k8_relat_1('#skF_2',k8_relat_1('#skF_1','#skF_3')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_53,plain,(
    k8_relat_1('#skF_2',k8_relat_1('#skF_1','#skF_3')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_12])).

tff(c_234,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_53])).

tff(c_262,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_234])).

tff(c_263,plain,(
    k8_relat_1('#skF_1',k8_relat_1('#skF_2','#skF_3')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_288,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_263])).

tff(c_313,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_14,c_288])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:01:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.40  
% 2.20/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.40  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k8_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.20/1.40  
% 2.20/1.40  %Foreground sorts:
% 2.20/1.40  
% 2.20/1.40  
% 2.20/1.40  %Background operators:
% 2.20/1.40  
% 2.20/1.40  
% 2.20/1.40  %Foreground operators:
% 2.20/1.40  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.20/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.20/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.20/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.20/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.20/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.20/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.20/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.20/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.40  
% 2.20/1.41  tff(f_62, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r1_tarski(A, B) => ((k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C)) & (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(A, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_funct_1)).
% 2.20/1.41  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_relat_1)).
% 2.20/1.41  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 2.20/1.41  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_relat_1)).
% 2.20/1.41  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.20/1.41  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 2.20/1.41  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.20/1.41  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.20/1.41  tff(c_276, plain, (![A_43, B_44, C_45]: (k8_relat_1(A_43, k8_relat_1(B_44, C_45))=k8_relat_1(A_43, C_45) | ~r1_tarski(A_43, B_44) | ~v1_relat_1(C_45))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.20/1.41  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k8_relat_1(A_4, B_5)) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.20/1.41  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k2_relat_1(k8_relat_1(A_6, B_7)), A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.20/1.41  tff(c_21, plain, (![A_17, C_18, B_19]: (r1_tarski(A_17, C_18) | ~r1_tarski(B_19, C_18) | ~r1_tarski(A_17, B_19))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.20/1.41  tff(c_27, plain, (![A_17]: (r1_tarski(A_17, '#skF_2') | ~r1_tarski(A_17, '#skF_1'))), inference(resolution, [status(thm)], [c_14, c_21])).
% 2.20/1.41  tff(c_43, plain, (![A_23, B_24]: (k8_relat_1(A_23, B_24)=B_24 | ~r1_tarski(k2_relat_1(B_24), A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.20/1.41  tff(c_54, plain, (![B_25]: (k8_relat_1('#skF_2', B_25)=B_25 | ~v1_relat_1(B_25) | ~r1_tarski(k2_relat_1(B_25), '#skF_1'))), inference(resolution, [status(thm)], [c_27, c_43])).
% 2.20/1.41  tff(c_144, plain, (![B_39]: (k8_relat_1('#skF_2', k8_relat_1('#skF_1', B_39))=k8_relat_1('#skF_1', B_39) | ~v1_relat_1(k8_relat_1('#skF_1', B_39)) | ~v1_relat_1(B_39))), inference(resolution, [status(thm)], [c_6, c_54])).
% 2.20/1.41  tff(c_210, plain, (![B_42]: (k8_relat_1('#skF_2', k8_relat_1('#skF_1', B_42))=k8_relat_1('#skF_1', B_42) | ~v1_relat_1(B_42))), inference(resolution, [status(thm)], [c_4, c_144])).
% 2.20/1.41  tff(c_12, plain, (k8_relat_1('#skF_1', k8_relat_1('#skF_2', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3') | k8_relat_1('#skF_2', k8_relat_1('#skF_1', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.20/1.41  tff(c_53, plain, (k8_relat_1('#skF_2', k8_relat_1('#skF_1', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_12])).
% 2.20/1.41  tff(c_234, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_210, c_53])).
% 2.20/1.41  tff(c_262, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_234])).
% 2.20/1.41  tff(c_263, plain, (k8_relat_1('#skF_1', k8_relat_1('#skF_2', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_12])).
% 2.20/1.41  tff(c_288, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_276, c_263])).
% 2.20/1.41  tff(c_313, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_14, c_288])).
% 2.20/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.41  
% 2.20/1.41  Inference rules
% 2.20/1.41  ----------------------
% 2.20/1.41  #Ref     : 0
% 2.20/1.41  #Sup     : 76
% 2.20/1.41  #Fact    : 0
% 2.20/1.41  #Define  : 0
% 2.20/1.41  #Split   : 3
% 2.20/1.41  #Chain   : 0
% 2.20/1.41  #Close   : 0
% 2.20/1.41  
% 2.20/1.41  Ordering : KBO
% 2.20/1.41  
% 2.20/1.41  Simplification rules
% 2.20/1.41  ----------------------
% 2.20/1.41  #Subsume      : 18
% 2.20/1.41  #Demod        : 6
% 2.20/1.41  #Tautology    : 17
% 2.20/1.41  #SimpNegUnit  : 0
% 2.20/1.41  #BackRed      : 0
% 2.20/1.41  
% 2.20/1.41  #Partial instantiations: 0
% 2.20/1.41  #Strategies tried      : 1
% 2.20/1.41  
% 2.20/1.41  Timing (in seconds)
% 2.20/1.41  ----------------------
% 2.20/1.42  Preprocessing        : 0.40
% 2.20/1.42  Parsing              : 0.25
% 2.20/1.42  CNF conversion       : 0.02
% 2.20/1.42  Main loop            : 0.21
% 2.20/1.42  Inferencing          : 0.09
% 2.20/1.42  Reduction            : 0.05
% 2.20/1.42  Demodulation         : 0.04
% 2.20/1.42  BG Simplification    : 0.01
% 2.20/1.42  Subsumption          : 0.04
% 2.20/1.42  Abstraction          : 0.01
% 2.20/1.42  MUC search           : 0.00
% 2.20/1.42  Cooper               : 0.00
% 2.20/1.42  Total                : 0.64
% 2.20/1.42  Index Insertion      : 0.00
% 2.20/1.42  Index Deletion       : 0.00
% 2.20/1.42  Index Matching       : 0.00
% 2.20/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
