%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:56 EST 2020

% Result     : Theorem 6.20s
% Output     : CNFRefutation 6.54s
% Verified   : 
% Statistics : Number of formulae       :   33 (  39 expanded)
%              Number of leaves         :   16 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   61 (  87 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k7_relat_1(C,A),k7_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k7_relat_1(B,A),k7_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(k7_relat_1(A_4,B_5))
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_73,plain,(
    ! [C_30,B_31,A_32] :
      ( k7_relat_1(k7_relat_1(C_30,B_31),A_32) = k7_relat_1(C_30,A_32)
      | ~ r1_tarski(A_32,B_31)
      | ~ v1_relat_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k7_relat_1(B_14,A_13),B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_82,plain,(
    ! [C_30,A_32,B_31] :
      ( r1_tarski(k7_relat_1(C_30,A_32),k7_relat_1(C_30,B_31))
      | ~ v1_relat_1(k7_relat_1(C_30,B_31))
      | ~ r1_tarski(A_32,B_31)
      | ~ v1_relat_1(C_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_10])).

tff(c_170,plain,(
    ! [B_46,A_47,C_48] :
      ( r1_tarski(k7_relat_1(B_46,A_47),k7_relat_1(C_48,A_47))
      | ~ r1_tarski(B_46,C_48)
      | ~ v1_relat_1(C_48)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_377,plain,(
    ! [A_70,C_71,A_72,B_73] :
      ( r1_tarski(A_70,k7_relat_1(C_71,A_72))
      | ~ r1_tarski(A_70,k7_relat_1(B_73,A_72))
      | ~ r1_tarski(B_73,C_71)
      | ~ v1_relat_1(C_71)
      | ~ v1_relat_1(B_73) ) ),
    inference(resolution,[status(thm)],[c_170,c_2])).

tff(c_5840,plain,(
    ! [C_206,A_207,C_208,B_209] :
      ( r1_tarski(k7_relat_1(C_206,A_207),k7_relat_1(C_208,B_209))
      | ~ r1_tarski(C_206,C_208)
      | ~ v1_relat_1(C_208)
      | ~ v1_relat_1(k7_relat_1(C_206,B_209))
      | ~ r1_tarski(A_207,B_209)
      | ~ v1_relat_1(C_206) ) ),
    inference(resolution,[status(thm)],[c_82,c_377])).

tff(c_12,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_5925,plain,
    ( ~ r1_tarski('#skF_3','#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5840,c_12])).

tff(c_6019,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_14,c_18,c_16,c_5925])).

tff(c_6034,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_6019])).

tff(c_6038,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_6034])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:10:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.20/2.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.20/2.25  
% 6.20/2.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.20/2.25  %$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.20/2.25  
% 6.20/2.25  %Foreground sorts:
% 6.20/2.25  
% 6.20/2.25  
% 6.20/2.25  %Background operators:
% 6.20/2.25  
% 6.20/2.25  
% 6.20/2.25  %Foreground operators:
% 6.20/2.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.20/2.25  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.20/2.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.20/2.25  tff('#skF_2', type, '#skF_2': $i).
% 6.20/2.25  tff('#skF_3', type, '#skF_3': $i).
% 6.20/2.25  tff('#skF_1', type, '#skF_1': $i).
% 6.20/2.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.20/2.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.20/2.25  tff('#skF_4', type, '#skF_4': $i).
% 6.20/2.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.20/2.25  
% 6.54/2.26  tff(f_66, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k7_relat_1(C, A), k7_relat_1(D, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_relat_1)).
% 6.54/2.26  tff(f_35, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 6.54/2.26  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_relat_1)).
% 6.54/2.26  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 6.54/2.26  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k7_relat_1(B, A), k7_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_relat_1)).
% 6.54/2.26  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 6.54/2.26  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.54/2.26  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k7_relat_1(A_4, B_5)) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.54/2.26  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.54/2.26  tff(c_18, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.54/2.26  tff(c_16, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.54/2.26  tff(c_73, plain, (![C_30, B_31, A_32]: (k7_relat_1(k7_relat_1(C_30, B_31), A_32)=k7_relat_1(C_30, A_32) | ~r1_tarski(A_32, B_31) | ~v1_relat_1(C_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.54/2.26  tff(c_10, plain, (![B_14, A_13]: (r1_tarski(k7_relat_1(B_14, A_13), B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.54/2.26  tff(c_82, plain, (![C_30, A_32, B_31]: (r1_tarski(k7_relat_1(C_30, A_32), k7_relat_1(C_30, B_31)) | ~v1_relat_1(k7_relat_1(C_30, B_31)) | ~r1_tarski(A_32, B_31) | ~v1_relat_1(C_30))), inference(superposition, [status(thm), theory('equality')], [c_73, c_10])).
% 6.54/2.26  tff(c_170, plain, (![B_46, A_47, C_48]: (r1_tarski(k7_relat_1(B_46, A_47), k7_relat_1(C_48, A_47)) | ~r1_tarski(B_46, C_48) | ~v1_relat_1(C_48) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.54/2.26  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.54/2.26  tff(c_377, plain, (![A_70, C_71, A_72, B_73]: (r1_tarski(A_70, k7_relat_1(C_71, A_72)) | ~r1_tarski(A_70, k7_relat_1(B_73, A_72)) | ~r1_tarski(B_73, C_71) | ~v1_relat_1(C_71) | ~v1_relat_1(B_73))), inference(resolution, [status(thm)], [c_170, c_2])).
% 6.54/2.26  tff(c_5840, plain, (![C_206, A_207, C_208, B_209]: (r1_tarski(k7_relat_1(C_206, A_207), k7_relat_1(C_208, B_209)) | ~r1_tarski(C_206, C_208) | ~v1_relat_1(C_208) | ~v1_relat_1(k7_relat_1(C_206, B_209)) | ~r1_tarski(A_207, B_209) | ~v1_relat_1(C_206))), inference(resolution, [status(thm)], [c_82, c_377])).
% 6.54/2.26  tff(c_12, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.54/2.26  tff(c_5925, plain, (~r1_tarski('#skF_3', '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_5840, c_12])).
% 6.54/2.26  tff(c_6019, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_14, c_18, c_16, c_5925])).
% 6.54/2.26  tff(c_6034, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4, c_6019])).
% 6.54/2.26  tff(c_6038, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_6034])).
% 6.54/2.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.54/2.26  
% 6.54/2.26  Inference rules
% 6.54/2.26  ----------------------
% 6.54/2.26  #Ref     : 0
% 6.54/2.26  #Sup     : 1440
% 6.54/2.26  #Fact    : 0
% 6.54/2.26  #Define  : 0
% 6.54/2.26  #Split   : 10
% 6.54/2.26  #Chain   : 0
% 6.54/2.26  #Close   : 0
% 6.54/2.26  
% 6.54/2.26  Ordering : KBO
% 6.54/2.26  
% 6.54/2.26  Simplification rules
% 6.54/2.26  ----------------------
% 6.54/2.26  #Subsume      : 389
% 6.54/2.26  #Demod        : 536
% 6.54/2.26  #Tautology    : 122
% 6.54/2.26  #SimpNegUnit  : 3
% 6.54/2.26  #BackRed      : 0
% 6.54/2.26  
% 6.54/2.26  #Partial instantiations: 0
% 6.54/2.26  #Strategies tried      : 1
% 6.54/2.26  
% 6.54/2.26  Timing (in seconds)
% 6.54/2.26  ----------------------
% 6.54/2.26  Preprocessing        : 0.26
% 6.54/2.26  Parsing              : 0.14
% 6.54/2.26  CNF conversion       : 0.02
% 6.54/2.26  Main loop            : 1.25
% 6.54/2.26  Inferencing          : 0.37
% 6.54/2.26  Reduction            : 0.33
% 6.54/2.26  Demodulation         : 0.22
% 6.54/2.26  BG Simplification    : 0.04
% 6.54/2.26  Subsumption          : 0.43
% 6.54/2.26  Abstraction          : 0.05
% 6.54/2.26  MUC search           : 0.00
% 6.54/2.26  Cooper               : 0.00
% 6.54/2.26  Total                : 1.53
% 6.54/2.26  Index Insertion      : 0.00
% 6.54/2.26  Index Deletion       : 0.00
% 6.54/2.26  Index Matching       : 0.00
% 6.54/2.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
