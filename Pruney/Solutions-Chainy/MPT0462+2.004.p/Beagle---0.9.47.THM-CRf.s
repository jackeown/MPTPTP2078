%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:43 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   28 (  34 expanded)
%              Number of leaves         :   14 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   60 ( 102 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k5_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_73,negated_conjecture,(
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

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(A,C),k5_relat_1(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_14,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_20,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_10,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_12,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4,plain,(
    ! [C_10,A_4,B_8] :
      ( r1_tarski(k5_relat_1(C_10,A_4),k5_relat_1(C_10,B_8))
      | ~ r1_tarski(A_4,B_8)
      | ~ v1_relat_1(C_10)
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_45,plain,(
    ! [A_36,C_37,B_38] :
      ( r1_tarski(k5_relat_1(A_36,C_37),k5_relat_1(B_38,C_37))
      | ~ r1_tarski(A_36,B_38)
      | ~ v1_relat_1(C_37)
      | ~ v1_relat_1(B_38)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ! [A_42,B_43,C_44,A_45] :
      ( r1_tarski(A_42,k5_relat_1(B_43,C_44))
      | ~ r1_tarski(A_42,k5_relat_1(A_45,C_44))
      | ~ r1_tarski(A_45,B_43)
      | ~ v1_relat_1(C_44)
      | ~ v1_relat_1(B_43)
      | ~ v1_relat_1(A_45) ) ),
    inference(resolution,[status(thm)],[c_45,c_2])).

tff(c_172,plain,(
    ! [C_72,A_73,B_74,B_75] :
      ( r1_tarski(k5_relat_1(C_72,A_73),k5_relat_1(B_74,B_75))
      | ~ r1_tarski(C_72,B_74)
      | ~ v1_relat_1(B_74)
      | ~ r1_tarski(A_73,B_75)
      | ~ v1_relat_1(C_72)
      | ~ v1_relat_1(B_75)
      | ~ v1_relat_1(A_73) ) ),
    inference(resolution,[status(thm)],[c_4,c_59])).

tff(c_8,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1','#skF_3'),k5_relat_1('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_189,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ r1_tarski('#skF_3','#skF_4')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_172,c_8])).

tff(c_200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_20,c_10,c_18,c_12,c_189])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:11:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.24  
% 2.11/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.24  %$ r1_tarski > v1_relat_1 > k5_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.11/1.24  
% 2.11/1.24  %Foreground sorts:
% 2.11/1.24  
% 2.11/1.24  
% 2.11/1.24  %Background operators:
% 2.11/1.24  
% 2.11/1.24  
% 2.11/1.24  %Foreground operators:
% 2.11/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.24  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.11/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.11/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.11/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.11/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.11/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.11/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.24  
% 2.28/1.25  tff(f_73, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k5_relat_1(A, C), k5_relat_1(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relat_1)).
% 2.28/1.25  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relat_1)).
% 2.28/1.25  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(A, C), k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relat_1)).
% 2.28/1.25  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.28/1.25  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.28/1.25  tff(c_14, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.28/1.25  tff(c_20, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.28/1.25  tff(c_10, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.28/1.25  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.28/1.25  tff(c_12, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.28/1.25  tff(c_4, plain, (![C_10, A_4, B_8]: (r1_tarski(k5_relat_1(C_10, A_4), k5_relat_1(C_10, B_8)) | ~r1_tarski(A_4, B_8) | ~v1_relat_1(C_10) | ~v1_relat_1(B_8) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.28/1.25  tff(c_45, plain, (![A_36, C_37, B_38]: (r1_tarski(k5_relat_1(A_36, C_37), k5_relat_1(B_38, C_37)) | ~r1_tarski(A_36, B_38) | ~v1_relat_1(C_37) | ~v1_relat_1(B_38) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.28/1.25  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.28/1.25  tff(c_59, plain, (![A_42, B_43, C_44, A_45]: (r1_tarski(A_42, k5_relat_1(B_43, C_44)) | ~r1_tarski(A_42, k5_relat_1(A_45, C_44)) | ~r1_tarski(A_45, B_43) | ~v1_relat_1(C_44) | ~v1_relat_1(B_43) | ~v1_relat_1(A_45))), inference(resolution, [status(thm)], [c_45, c_2])).
% 2.28/1.25  tff(c_172, plain, (![C_72, A_73, B_74, B_75]: (r1_tarski(k5_relat_1(C_72, A_73), k5_relat_1(B_74, B_75)) | ~r1_tarski(C_72, B_74) | ~v1_relat_1(B_74) | ~r1_tarski(A_73, B_75) | ~v1_relat_1(C_72) | ~v1_relat_1(B_75) | ~v1_relat_1(A_73))), inference(resolution, [status(thm)], [c_4, c_59])).
% 2.28/1.25  tff(c_8, plain, (~r1_tarski(k5_relat_1('#skF_1', '#skF_3'), k5_relat_1('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.28/1.25  tff(c_189, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2') | ~r1_tarski('#skF_3', '#skF_4') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_172, c_8])).
% 2.28/1.25  tff(c_200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_20, c_10, c_18, c_12, c_189])).
% 2.28/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.25  
% 2.28/1.25  Inference rules
% 2.28/1.25  ----------------------
% 2.28/1.25  #Ref     : 0
% 2.28/1.25  #Sup     : 45
% 2.28/1.25  #Fact    : 0
% 2.28/1.25  #Define  : 0
% 2.28/1.25  #Split   : 1
% 2.28/1.25  #Chain   : 0
% 2.28/1.25  #Close   : 0
% 2.28/1.25  
% 2.28/1.25  Ordering : KBO
% 2.28/1.25  
% 2.28/1.25  Simplification rules
% 2.28/1.25  ----------------------
% 2.28/1.25  #Subsume      : 4
% 2.28/1.25  #Demod        : 20
% 2.28/1.25  #Tautology    : 1
% 2.28/1.25  #SimpNegUnit  : 0
% 2.28/1.25  #BackRed      : 0
% 2.28/1.25  
% 2.28/1.25  #Partial instantiations: 0
% 2.28/1.25  #Strategies tried      : 1
% 2.28/1.25  
% 2.28/1.25  Timing (in seconds)
% 2.28/1.25  ----------------------
% 2.28/1.25  Preprocessing        : 0.25
% 2.28/1.25  Parsing              : 0.13
% 2.28/1.25  CNF conversion       : 0.02
% 2.28/1.25  Main loop            : 0.22
% 2.28/1.25  Inferencing          : 0.08
% 2.28/1.25  Reduction            : 0.05
% 2.28/1.25  Demodulation         : 0.04
% 2.28/1.25  BG Simplification    : 0.01
% 2.28/1.25  Subsumption          : 0.06
% 2.28/1.25  Abstraction          : 0.01
% 2.28/1.25  MUC search           : 0.00
% 2.28/1.25  Cooper               : 0.00
% 2.28/1.25  Total                : 0.50
% 2.28/1.25  Index Insertion      : 0.00
% 2.28/1.25  Index Deletion       : 0.00
% 2.28/1.25  Index Matching       : 0.00
% 2.28/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
