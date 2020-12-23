%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:38 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   36 (  54 expanded)
%              Number of leaves         :   17 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   49 (  95 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => r1_tarski(k5_relat_1(B,k7_relat_1(C,A)),k5_relat_1(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k7_relat_1(B_15,A_14),B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_65,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = A_25
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ! [B_15,A_14] :
      ( k3_xboole_0(k7_relat_1(B_15,A_14),B_15) = k7_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(resolution,[status(thm)],[c_10,c_65])).

tff(c_83,plain,(
    ! [B_30,A_31] :
      ( k3_xboole_0(B_30,k7_relat_1(B_30,A_31)) = k7_relat_1(B_30,A_31)
      | ~ v1_relat_1(B_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_68])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( v1_relat_1(k3_xboole_0(A_5,B_6))
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_98,plain,(
    ! [B_32,A_33] :
      ( v1_relat_1(k7_relat_1(B_32,A_33))
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(B_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_6])).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_71,plain,(
    ! [C_27,A_28,B_29] :
      ( r1_tarski(k5_relat_1(C_27,A_28),k5_relat_1(C_27,B_29))
      | ~ r1_tarski(A_28,B_29)
      | ~ v1_relat_1(C_27)
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    ~ r1_tarski(k5_relat_1('#skF_2',k7_relat_1('#skF_3','#skF_1')),k5_relat_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_74,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_3')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_71,c_12])).

tff(c_80,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16,c_74])).

tff(c_82,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_101,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_82])).

tff(c_105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_101])).

tff(c_106,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_110,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_106])).

tff(c_114,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_110])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:16:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.11  
% 1.64/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.12  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.64/1.12  
% 1.64/1.12  %Foreground sorts:
% 1.64/1.12  
% 1.64/1.12  
% 1.64/1.12  %Background operators:
% 1.64/1.12  
% 1.64/1.12  
% 1.64/1.12  %Foreground operators:
% 1.64/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.12  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.64/1.12  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.64/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.64/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.64/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.64/1.12  
% 1.64/1.13  tff(f_59, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(B, k7_relat_1(C, A)), k5_relat_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_relat_1)).
% 1.64/1.13  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 1.64/1.13  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.64/1.13  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.64/1.13  tff(f_35, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 1.64/1.13  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relat_1)).
% 1.64/1.13  tff(c_14, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.64/1.13  tff(c_10, plain, (![B_15, A_14]: (r1_tarski(k7_relat_1(B_15, A_14), B_15) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.64/1.13  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.64/1.13  tff(c_65, plain, (![A_25, B_26]: (k3_xboole_0(A_25, B_26)=A_25 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.64/1.13  tff(c_68, plain, (![B_15, A_14]: (k3_xboole_0(k7_relat_1(B_15, A_14), B_15)=k7_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(resolution, [status(thm)], [c_10, c_65])).
% 1.64/1.13  tff(c_83, plain, (![B_30, A_31]: (k3_xboole_0(B_30, k7_relat_1(B_30, A_31))=k7_relat_1(B_30, A_31) | ~v1_relat_1(B_30))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_68])).
% 1.64/1.13  tff(c_6, plain, (![A_5, B_6]: (v1_relat_1(k3_xboole_0(A_5, B_6)) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.64/1.13  tff(c_98, plain, (![B_32, A_33]: (v1_relat_1(k7_relat_1(B_32, A_33)) | ~v1_relat_1(B_32) | ~v1_relat_1(B_32))), inference(superposition, [status(thm), theory('equality')], [c_83, c_6])).
% 1.64/1.13  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.64/1.13  tff(c_71, plain, (![C_27, A_28, B_29]: (r1_tarski(k5_relat_1(C_27, A_28), k5_relat_1(C_27, B_29)) | ~r1_tarski(A_28, B_29) | ~v1_relat_1(C_27) | ~v1_relat_1(B_29) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.64/1.13  tff(c_12, plain, (~r1_tarski(k5_relat_1('#skF_2', k7_relat_1('#skF_3', '#skF_1')), k5_relat_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.64/1.13  tff(c_74, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_3') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_71, c_12])).
% 1.64/1.13  tff(c_80, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16, c_74])).
% 1.64/1.13  tff(c_82, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_80])).
% 1.64/1.13  tff(c_101, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_98, c_82])).
% 1.64/1.13  tff(c_105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_101])).
% 1.64/1.13  tff(c_106, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_3')), inference(splitRight, [status(thm)], [c_80])).
% 1.64/1.13  tff(c_110, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_106])).
% 1.64/1.13  tff(c_114, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_110])).
% 1.64/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.13  
% 1.64/1.13  Inference rules
% 1.64/1.13  ----------------------
% 1.64/1.13  #Ref     : 0
% 1.64/1.13  #Sup     : 21
% 1.64/1.13  #Fact    : 0
% 1.64/1.13  #Define  : 0
% 1.64/1.13  #Split   : 1
% 1.64/1.13  #Chain   : 0
% 1.64/1.13  #Close   : 0
% 1.64/1.13  
% 1.64/1.13  Ordering : KBO
% 1.64/1.13  
% 1.64/1.13  Simplification rules
% 1.64/1.13  ----------------------
% 1.64/1.13  #Subsume      : 3
% 1.64/1.13  #Demod        : 5
% 1.64/1.13  #Tautology    : 11
% 1.64/1.13  #SimpNegUnit  : 0
% 1.64/1.13  #BackRed      : 0
% 1.64/1.13  
% 1.64/1.13  #Partial instantiations: 0
% 1.64/1.13  #Strategies tried      : 1
% 1.64/1.13  
% 1.64/1.13  Timing (in seconds)
% 1.64/1.13  ----------------------
% 1.64/1.13  Preprocessing        : 0.26
% 1.64/1.13  Parsing              : 0.14
% 1.64/1.13  CNF conversion       : 0.02
% 1.64/1.13  Main loop            : 0.12
% 1.64/1.13  Inferencing          : 0.05
% 1.64/1.13  Reduction            : 0.03
% 1.64/1.13  Demodulation         : 0.03
% 1.64/1.13  BG Simplification    : 0.01
% 1.64/1.13  Subsumption          : 0.02
% 1.64/1.13  Abstraction          : 0.01
% 1.64/1.13  MUC search           : 0.00
% 1.64/1.13  Cooper               : 0.00
% 1.64/1.13  Total                : 0.40
% 1.64/1.13  Index Insertion      : 0.00
% 1.64/1.13  Index Deletion       : 0.00
% 1.64/1.13  Index Matching       : 0.00
% 1.64/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
