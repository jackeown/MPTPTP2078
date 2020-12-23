%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:35 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   33 (  65 expanded)
%              Number of leaves         :   15 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   56 ( 146 expanded)
%              Number of equality atoms :    2 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [A_6,B_8] :
      ( r1_tarski(k2_relat_1(A_6),k2_relat_1(B_8))
      | ~ r1_tarski(A_6,B_8)
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8,plain,(
    ! [A_6,B_8] :
      ( r1_tarski(k1_relat_1(A_6),k1_relat_1(B_8))
      | ~ r1_tarski(A_6,B_8)
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_5] :
      ( k2_xboole_0(k1_relat_1(A_5),k2_relat_1(A_5)) = k3_relat_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    ! [A_15,C_16,B_17,D_18] :
      ( r1_tarski(k2_xboole_0(A_15,C_16),k2_xboole_0(B_17,D_18))
      | ~ r1_tarski(C_16,D_18)
      | ~ r1_tarski(A_15,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_35,plain,(
    ! [A_19,B_20,D_21] :
      ( r1_tarski(k3_relat_1(A_19),k2_xboole_0(B_20,D_21))
      | ~ r1_tarski(k2_relat_1(A_19),D_21)
      | ~ r1_tarski(k1_relat_1(A_19),B_20)
      | ~ v1_relat_1(A_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_28])).

tff(c_43,plain,(
    ! [A_25,A_26] :
      ( r1_tarski(k3_relat_1(A_25),k3_relat_1(A_26))
      | ~ r1_tarski(k2_relat_1(A_25),k2_relat_1(A_26))
      | ~ r1_tarski(k1_relat_1(A_25),k1_relat_1(A_26))
      | ~ v1_relat_1(A_25)
      | ~ v1_relat_1(A_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_35])).

tff(c_10,plain,(
    ~ r1_tarski(k3_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_46,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_43,c_10])).

tff(c_49,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16,c_46])).

tff(c_50,plain,(
    ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_49])).

tff(c_53,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_50])).

tff(c_57,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_12,c_53])).

tff(c_58,plain,(
    ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_62,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_58])).

tff(c_66,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_12,c_62])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n008.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 14:11:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.10  
% 1.67/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.11  %$ r1_tarski > v1_relat_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.67/1.11  
% 1.67/1.11  %Foreground sorts:
% 1.67/1.11  
% 1.67/1.11  
% 1.67/1.11  %Background operators:
% 1.67/1.11  
% 1.67/1.11  
% 1.67/1.11  %Foreground operators:
% 1.67/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.11  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.67/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.67/1.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.67/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.67/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.67/1.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.67/1.11  
% 1.67/1.12  tff(f_56, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 1.67/1.12  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 1.67/1.12  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 1.67/1.12  tff(f_31, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_xboole_1)).
% 1.67/1.12  tff(c_16, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.67/1.12  tff(c_14, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.67/1.12  tff(c_12, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.67/1.12  tff(c_6, plain, (![A_6, B_8]: (r1_tarski(k2_relat_1(A_6), k2_relat_1(B_8)) | ~r1_tarski(A_6, B_8) | ~v1_relat_1(B_8) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.67/1.12  tff(c_8, plain, (![A_6, B_8]: (r1_tarski(k1_relat_1(A_6), k1_relat_1(B_8)) | ~r1_tarski(A_6, B_8) | ~v1_relat_1(B_8) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.67/1.12  tff(c_4, plain, (![A_5]: (k2_xboole_0(k1_relat_1(A_5), k2_relat_1(A_5))=k3_relat_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.67/1.12  tff(c_28, plain, (![A_15, C_16, B_17, D_18]: (r1_tarski(k2_xboole_0(A_15, C_16), k2_xboole_0(B_17, D_18)) | ~r1_tarski(C_16, D_18) | ~r1_tarski(A_15, B_17))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.67/1.12  tff(c_35, plain, (![A_19, B_20, D_21]: (r1_tarski(k3_relat_1(A_19), k2_xboole_0(B_20, D_21)) | ~r1_tarski(k2_relat_1(A_19), D_21) | ~r1_tarski(k1_relat_1(A_19), B_20) | ~v1_relat_1(A_19))), inference(superposition, [status(thm), theory('equality')], [c_4, c_28])).
% 1.67/1.12  tff(c_43, plain, (![A_25, A_26]: (r1_tarski(k3_relat_1(A_25), k3_relat_1(A_26)) | ~r1_tarski(k2_relat_1(A_25), k2_relat_1(A_26)) | ~r1_tarski(k1_relat_1(A_25), k1_relat_1(A_26)) | ~v1_relat_1(A_25) | ~v1_relat_1(A_26))), inference(superposition, [status(thm), theory('equality')], [c_4, c_35])).
% 1.67/1.12  tff(c_10, plain, (~r1_tarski(k3_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.67/1.12  tff(c_46, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_43, c_10])).
% 1.67/1.12  tff(c_49, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16, c_46])).
% 1.67/1.12  tff(c_50, plain, (~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_49])).
% 1.67/1.12  tff(c_53, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_8, c_50])).
% 1.67/1.12  tff(c_57, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_12, c_53])).
% 1.67/1.12  tff(c_58, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_49])).
% 1.67/1.12  tff(c_62, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6, c_58])).
% 1.67/1.12  tff(c_66, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_12, c_62])).
% 1.67/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.12  
% 1.67/1.12  Inference rules
% 1.67/1.12  ----------------------
% 1.67/1.12  #Ref     : 0
% 1.67/1.12  #Sup     : 9
% 1.67/1.12  #Fact    : 0
% 1.67/1.12  #Define  : 0
% 1.67/1.12  #Split   : 1
% 1.67/1.12  #Chain   : 0
% 1.67/1.12  #Close   : 0
% 1.67/1.12  
% 1.67/1.12  Ordering : KBO
% 1.67/1.12  
% 1.67/1.12  Simplification rules
% 1.67/1.12  ----------------------
% 1.67/1.12  #Subsume      : 0
% 1.67/1.12  #Demod        : 8
% 1.67/1.12  #Tautology    : 2
% 1.67/1.12  #SimpNegUnit  : 0
% 1.67/1.12  #BackRed      : 0
% 1.67/1.12  
% 1.67/1.12  #Partial instantiations: 0
% 1.67/1.12  #Strategies tried      : 1
% 1.67/1.12  
% 1.67/1.12  Timing (in seconds)
% 1.67/1.12  ----------------------
% 1.67/1.12  Preprocessing        : 0.26
% 1.67/1.12  Parsing              : 0.14
% 1.67/1.12  CNF conversion       : 0.02
% 1.67/1.12  Main loop            : 0.12
% 1.67/1.12  Inferencing          : 0.06
% 1.67/1.12  Reduction            : 0.03
% 1.67/1.12  Demodulation         : 0.02
% 1.67/1.12  BG Simplification    : 0.01
% 1.67/1.12  Subsumption          : 0.02
% 1.67/1.12  Abstraction          : 0.00
% 1.67/1.12  MUC search           : 0.00
% 1.67/1.12  Cooper               : 0.00
% 1.67/1.12  Total                : 0.40
% 1.67/1.12  Index Insertion      : 0.00
% 1.67/1.12  Index Deletion       : 0.00
% 1.67/1.12  Index Matching       : 0.00
% 1.67/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
