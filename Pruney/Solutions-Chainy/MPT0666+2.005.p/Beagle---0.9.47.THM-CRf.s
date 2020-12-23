%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:17 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
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
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r1_tarski(A,B)
         => ( k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A)
            & k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_funct_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_276,plain,(
    ! [C_43,B_44,A_45] :
      ( k7_relat_1(k7_relat_1(C_43,B_44),A_45) = k7_relat_1(C_43,A_45)
      | ~ r1_tarski(A_45,B_44)
      | ~ v1_relat_1(C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(k7_relat_1(A_4,B_5))
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_10,A_9)),A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

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
    ! [B_23,A_24] :
      ( k7_relat_1(B_23,A_24) = B_23
      | ~ r1_tarski(k1_relat_1(B_23),A_24)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_54,plain,(
    ! [B_25] :
      ( k7_relat_1(B_25,'#skF_2') = B_25
      | ~ v1_relat_1(B_25)
      | ~ r1_tarski(k1_relat_1(B_25),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_27,c_43])).

tff(c_144,plain,(
    ! [B_39] :
      ( k7_relat_1(k7_relat_1(B_39,'#skF_1'),'#skF_2') = k7_relat_1(B_39,'#skF_1')
      | ~ v1_relat_1(k7_relat_1(B_39,'#skF_1'))
      | ~ v1_relat_1(B_39) ) ),
    inference(resolution,[status(thm)],[c_8,c_54])).

tff(c_210,plain,(
    ! [A_42] :
      ( k7_relat_1(k7_relat_1(A_42,'#skF_1'),'#skF_2') = k7_relat_1(A_42,'#skF_1')
      | ~ v1_relat_1(A_42) ) ),
    inference(resolution,[status(thm)],[c_4,c_144])).

tff(c_12,plain,
    ( k7_relat_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') != k7_relat_1('#skF_3','#skF_1')
    | k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') != k7_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_53,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') != k7_relat_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_12])).

tff(c_234,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_53])).

tff(c_262,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_234])).

tff(c_263,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') != k7_relat_1('#skF_3','#skF_1') ),
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
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:35:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.28  
% 2.04/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.29  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.04/1.29  
% 2.04/1.29  %Foreground sorts:
% 2.04/1.29  
% 2.04/1.29  
% 2.04/1.29  %Background operators:
% 2.04/1.29  
% 2.04/1.29  
% 2.04/1.29  %Foreground operators:
% 2.04/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.04/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.29  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.04/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.04/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.04/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.04/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.04/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.04/1.29  
% 2.04/1.30  tff(f_62, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r1_tarski(A, B) => ((k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A)) & (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_funct_1)).
% 2.04/1.30  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_relat_1)).
% 2.04/1.30  tff(f_35, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.04/1.30  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.04/1.30  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.04/1.30  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 2.04/1.30  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.04/1.30  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.04/1.30  tff(c_276, plain, (![C_43, B_44, A_45]: (k7_relat_1(k7_relat_1(C_43, B_44), A_45)=k7_relat_1(C_43, A_45) | ~r1_tarski(A_45, B_44) | ~v1_relat_1(C_43))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.04/1.30  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k7_relat_1(A_4, B_5)) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.04/1.30  tff(c_8, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(k7_relat_1(B_10, A_9)), A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.04/1.30  tff(c_21, plain, (![A_17, C_18, B_19]: (r1_tarski(A_17, C_18) | ~r1_tarski(B_19, C_18) | ~r1_tarski(A_17, B_19))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.04/1.30  tff(c_27, plain, (![A_17]: (r1_tarski(A_17, '#skF_2') | ~r1_tarski(A_17, '#skF_1'))), inference(resolution, [status(thm)], [c_14, c_21])).
% 2.04/1.30  tff(c_43, plain, (![B_23, A_24]: (k7_relat_1(B_23, A_24)=B_23 | ~r1_tarski(k1_relat_1(B_23), A_24) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.04/1.30  tff(c_54, plain, (![B_25]: (k7_relat_1(B_25, '#skF_2')=B_25 | ~v1_relat_1(B_25) | ~r1_tarski(k1_relat_1(B_25), '#skF_1'))), inference(resolution, [status(thm)], [c_27, c_43])).
% 2.04/1.30  tff(c_144, plain, (![B_39]: (k7_relat_1(k7_relat_1(B_39, '#skF_1'), '#skF_2')=k7_relat_1(B_39, '#skF_1') | ~v1_relat_1(k7_relat_1(B_39, '#skF_1')) | ~v1_relat_1(B_39))), inference(resolution, [status(thm)], [c_8, c_54])).
% 2.04/1.30  tff(c_210, plain, (![A_42]: (k7_relat_1(k7_relat_1(A_42, '#skF_1'), '#skF_2')=k7_relat_1(A_42, '#skF_1') | ~v1_relat_1(A_42))), inference(resolution, [status(thm)], [c_4, c_144])).
% 2.04/1.30  tff(c_12, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k7_relat_1('#skF_3', '#skF_1') | k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')!=k7_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.04/1.30  tff(c_53, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')!=k7_relat_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_12])).
% 2.04/1.30  tff(c_234, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_210, c_53])).
% 2.04/1.30  tff(c_262, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_234])).
% 2.04/1.30  tff(c_263, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k7_relat_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_12])).
% 2.04/1.30  tff(c_288, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_276, c_263])).
% 2.04/1.30  tff(c_313, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_14, c_288])).
% 2.04/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.30  
% 2.04/1.30  Inference rules
% 2.04/1.30  ----------------------
% 2.04/1.30  #Ref     : 0
% 2.04/1.30  #Sup     : 76
% 2.04/1.30  #Fact    : 0
% 2.04/1.30  #Define  : 0
% 2.04/1.30  #Split   : 3
% 2.04/1.30  #Chain   : 0
% 2.04/1.30  #Close   : 0
% 2.04/1.30  
% 2.04/1.30  Ordering : KBO
% 2.04/1.30  
% 2.04/1.30  Simplification rules
% 2.04/1.30  ----------------------
% 2.04/1.30  #Subsume      : 18
% 2.04/1.30  #Demod        : 6
% 2.04/1.30  #Tautology    : 17
% 2.04/1.30  #SimpNegUnit  : 0
% 2.04/1.30  #BackRed      : 0
% 2.04/1.30  
% 2.04/1.30  #Partial instantiations: 0
% 2.04/1.30  #Strategies tried      : 1
% 2.04/1.30  
% 2.04/1.30  Timing (in seconds)
% 2.04/1.30  ----------------------
% 2.04/1.30  Preprocessing        : 0.26
% 2.04/1.30  Parsing              : 0.14
% 2.04/1.30  CNF conversion       : 0.02
% 2.04/1.30  Main loop            : 0.22
% 2.04/1.30  Inferencing          : 0.09
% 2.04/1.30  Reduction            : 0.05
% 2.04/1.30  Demodulation         : 0.04
% 2.04/1.30  BG Simplification    : 0.01
% 2.04/1.30  Subsumption          : 0.05
% 2.04/1.30  Abstraction          : 0.01
% 2.04/1.30  MUC search           : 0.00
% 2.04/1.30  Cooper               : 0.00
% 2.04/1.30  Total                : 0.50
% 2.04/1.30  Index Insertion      : 0.00
% 2.04/1.30  Index Deletion       : 0.00
% 2.04/1.30  Index Matching       : 0.00
% 2.04/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
