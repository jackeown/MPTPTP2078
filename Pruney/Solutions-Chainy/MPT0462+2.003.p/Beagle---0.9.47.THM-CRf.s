%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:43 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   32 (  38 expanded)
%              Number of leaves         :   16 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   67 ( 109 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k5_relat_1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => ! [D] :
                    ( v1_relat_1(D)
                   => ( ( r1_tarski(A,B)
                        & r1_tarski(C,D) )
                     => r1_tarski(k5_relat_1(A,C),k5_relat_1(B,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(A,C),k5_relat_1(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_16,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_12,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6,plain,(
    ! [C_12,A_6,B_10] :
      ( r1_tarski(k5_relat_1(C_12,A_6),k5_relat_1(C_12,B_10))
      | ~ r1_tarski(A_6,B_10)
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_54,plain,(
    ! [A_39,C_40,B_41] :
      ( r1_tarski(k5_relat_1(A_39,C_40),k5_relat_1(B_41,C_40))
      | ~ r1_tarski(A_39,B_41)
      | ~ v1_relat_1(C_40)
      | ~ v1_relat_1(B_41)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_64,plain,(
    ! [A_45,C_46,B_47] :
      ( k2_xboole_0(k5_relat_1(A_45,C_46),k5_relat_1(B_47,C_46)) = k5_relat_1(B_47,C_46)
      | ~ r1_tarski(A_45,B_47)
      | ~ v1_relat_1(C_46)
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(A_45) ) ),
    inference(resolution,[status(thm)],[c_54,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_98,plain,(
    ! [A_51,C_52,C_53,B_54] :
      ( r1_tarski(k5_relat_1(A_51,C_52),C_53)
      | ~ r1_tarski(k5_relat_1(B_54,C_52),C_53)
      | ~ r1_tarski(A_51,B_54)
      | ~ v1_relat_1(C_52)
      | ~ v1_relat_1(B_54)
      | ~ v1_relat_1(A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_2])).

tff(c_112,plain,(
    ! [A_59,A_60,C_61,B_62] :
      ( r1_tarski(k5_relat_1(A_59,A_60),k5_relat_1(C_61,B_62))
      | ~ r1_tarski(A_59,C_61)
      | ~ v1_relat_1(A_59)
      | ~ r1_tarski(A_60,B_62)
      | ~ v1_relat_1(C_61)
      | ~ v1_relat_1(B_62)
      | ~ v1_relat_1(A_60) ) ),
    inference(resolution,[status(thm)],[c_6,c_98])).

tff(c_10,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1','#skF_3'),k5_relat_1('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_122,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_1')
    | ~ r1_tarski('#skF_3','#skF_4')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_112,c_10])).

tff(c_129,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_20,c_12,c_22,c_14,c_122])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:42:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.20  
% 1.93/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.20  %$ r1_tarski > v1_relat_1 > k5_relat_1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.93/1.20  
% 1.93/1.20  %Foreground sorts:
% 1.93/1.20  
% 1.93/1.20  
% 1.93/1.20  %Background operators:
% 1.93/1.20  
% 1.93/1.20  
% 1.93/1.20  %Foreground operators:
% 1.93/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.20  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.93/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.93/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.93/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.93/1.20  
% 1.93/1.21  tff(f_75, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k5_relat_1(A, C), k5_relat_1(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relat_1)).
% 1.93/1.21  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relat_1)).
% 1.93/1.21  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(A, C), k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relat_1)).
% 1.93/1.21  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.93/1.21  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.93/1.21  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.93/1.21  tff(c_16, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.93/1.21  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.93/1.21  tff(c_12, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.93/1.21  tff(c_22, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.93/1.21  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.93/1.21  tff(c_6, plain, (![C_12, A_6, B_10]: (r1_tarski(k5_relat_1(C_12, A_6), k5_relat_1(C_12, B_10)) | ~r1_tarski(A_6, B_10) | ~v1_relat_1(C_12) | ~v1_relat_1(B_10) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.93/1.21  tff(c_54, plain, (![A_39, C_40, B_41]: (r1_tarski(k5_relat_1(A_39, C_40), k5_relat_1(B_41, C_40)) | ~r1_tarski(A_39, B_41) | ~v1_relat_1(C_40) | ~v1_relat_1(B_41) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.93/1.21  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.93/1.21  tff(c_64, plain, (![A_45, C_46, B_47]: (k2_xboole_0(k5_relat_1(A_45, C_46), k5_relat_1(B_47, C_46))=k5_relat_1(B_47, C_46) | ~r1_tarski(A_45, B_47) | ~v1_relat_1(C_46) | ~v1_relat_1(B_47) | ~v1_relat_1(A_45))), inference(resolution, [status(thm)], [c_54, c_4])).
% 1.93/1.21  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.21  tff(c_98, plain, (![A_51, C_52, C_53, B_54]: (r1_tarski(k5_relat_1(A_51, C_52), C_53) | ~r1_tarski(k5_relat_1(B_54, C_52), C_53) | ~r1_tarski(A_51, B_54) | ~v1_relat_1(C_52) | ~v1_relat_1(B_54) | ~v1_relat_1(A_51))), inference(superposition, [status(thm), theory('equality')], [c_64, c_2])).
% 1.93/1.21  tff(c_112, plain, (![A_59, A_60, C_61, B_62]: (r1_tarski(k5_relat_1(A_59, A_60), k5_relat_1(C_61, B_62)) | ~r1_tarski(A_59, C_61) | ~v1_relat_1(A_59) | ~r1_tarski(A_60, B_62) | ~v1_relat_1(C_61) | ~v1_relat_1(B_62) | ~v1_relat_1(A_60))), inference(resolution, [status(thm)], [c_6, c_98])).
% 1.93/1.21  tff(c_10, plain, (~r1_tarski(k5_relat_1('#skF_1', '#skF_3'), k5_relat_1('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.93/1.21  tff(c_122, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_1') | ~r1_tarski('#skF_3', '#skF_4') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_112, c_10])).
% 1.93/1.21  tff(c_129, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_20, c_12, c_22, c_14, c_122])).
% 1.93/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.21  
% 1.93/1.21  Inference rules
% 1.93/1.21  ----------------------
% 1.93/1.21  #Ref     : 0
% 1.93/1.21  #Sup     : 27
% 1.93/1.21  #Fact    : 0
% 1.93/1.21  #Define  : 0
% 1.93/1.21  #Split   : 0
% 1.93/1.21  #Chain   : 0
% 1.93/1.21  #Close   : 0
% 1.93/1.21  
% 1.93/1.21  Ordering : KBO
% 1.93/1.21  
% 1.93/1.21  Simplification rules
% 1.93/1.21  ----------------------
% 1.93/1.21  #Subsume      : 0
% 1.93/1.21  #Demod        : 6
% 1.93/1.21  #Tautology    : 10
% 1.93/1.21  #SimpNegUnit  : 0
% 1.93/1.21  #BackRed      : 0
% 1.93/1.21  
% 1.93/1.21  #Partial instantiations: 0
% 1.93/1.21  #Strategies tried      : 1
% 1.93/1.21  
% 1.93/1.21  Timing (in seconds)
% 1.93/1.21  ----------------------
% 2.03/1.21  Preprocessing        : 0.28
% 2.03/1.21  Parsing              : 0.15
% 2.03/1.21  CNF conversion       : 0.02
% 2.03/1.21  Main loop            : 0.18
% 2.03/1.21  Inferencing          : 0.08
% 2.03/1.21  Reduction            : 0.04
% 2.03/1.21  Demodulation         : 0.03
% 2.03/1.21  BG Simplification    : 0.01
% 2.03/1.21  Subsumption          : 0.03
% 2.03/1.22  Abstraction          : 0.01
% 2.03/1.22  MUC search           : 0.00
% 2.03/1.22  Cooper               : 0.00
% 2.03/1.22  Total                : 0.49
% 2.03/1.22  Index Insertion      : 0.00
% 2.03/1.22  Index Deletion       : 0.00
% 2.03/1.22  Index Matching       : 0.00
% 2.03/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
