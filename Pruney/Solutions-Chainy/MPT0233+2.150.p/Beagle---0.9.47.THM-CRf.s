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
% DateTime   : Thu Dec  3 09:49:40 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   25 (  27 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   32 (  38 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
        & A != B
        & A != C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(c_18,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_16,plain,(
    '#skF_1' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10,plain,(
    ! [B_5,C_6] : r1_tarski(k1_tarski(B_5),k2_tarski(B_5,C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_20,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_25,plain,(
    ! [A_18,C_19,B_20] :
      ( r1_tarski(A_18,C_19)
      | ~ r1_tarski(B_20,C_19)
      | ~ r1_tarski(A_18,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    ! [A_18] :
      ( r1_tarski(A_18,k2_tarski('#skF_3','#skF_4'))
      | ~ r1_tarski(A_18,k2_tarski('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_20,c_25])).

tff(c_57,plain,(
    ! [C_31,A_32,B_33] :
      ( C_31 = A_32
      | B_33 = A_32
      | ~ r1_tarski(k1_tarski(A_32),k2_tarski(B_33,C_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_132,plain,(
    ! [A_46] :
      ( A_46 = '#skF_4'
      | A_46 = '#skF_3'
      | ~ r1_tarski(k1_tarski(A_46),k2_tarski('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_36,c_57])).

tff(c_149,plain,
    ( '#skF_1' = '#skF_4'
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_10,c_132])).

tff(c_157,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_16,c_149])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:34:15 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.15  
% 1.66/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.15  %$ r1_tarski > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.66/1.15  
% 1.66/1.15  %Foreground sorts:
% 1.66/1.15  
% 1.66/1.15  
% 1.66/1.15  %Background operators:
% 1.66/1.15  
% 1.66/1.15  
% 1.66/1.15  %Foreground operators:
% 1.66/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.66/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.66/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.66/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.66/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.66/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.15  tff('#skF_4', type, '#skF_4': $i).
% 1.66/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.15  
% 1.66/1.16  tff(f_65, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 1.66/1.16  tff(f_46, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 1.66/1.16  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.66/1.16  tff(f_55, axiom, (![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 1.66/1.16  tff(c_18, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.66/1.16  tff(c_16, plain, ('#skF_1'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.66/1.16  tff(c_10, plain, (![B_5, C_6]: (r1_tarski(k1_tarski(B_5), k2_tarski(B_5, C_6)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.66/1.16  tff(c_20, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.66/1.16  tff(c_25, plain, (![A_18, C_19, B_20]: (r1_tarski(A_18, C_19) | ~r1_tarski(B_20, C_19) | ~r1_tarski(A_18, B_20))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.66/1.16  tff(c_36, plain, (![A_18]: (r1_tarski(A_18, k2_tarski('#skF_3', '#skF_4')) | ~r1_tarski(A_18, k2_tarski('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_20, c_25])).
% 1.66/1.16  tff(c_57, plain, (![C_31, A_32, B_33]: (C_31=A_32 | B_33=A_32 | ~r1_tarski(k1_tarski(A_32), k2_tarski(B_33, C_31)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.66/1.16  tff(c_132, plain, (![A_46]: (A_46='#skF_4' | A_46='#skF_3' | ~r1_tarski(k1_tarski(A_46), k2_tarski('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_36, c_57])).
% 1.66/1.16  tff(c_149, plain, ('#skF_1'='#skF_4' | '#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_10, c_132])).
% 1.66/1.16  tff(c_157, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_16, c_149])).
% 1.66/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.16  
% 1.66/1.16  Inference rules
% 1.66/1.16  ----------------------
% 1.66/1.16  #Ref     : 0
% 1.66/1.16  #Sup     : 29
% 1.66/1.16  #Fact    : 0
% 1.66/1.16  #Define  : 0
% 1.66/1.16  #Split   : 0
% 1.66/1.16  #Chain   : 0
% 1.66/1.16  #Close   : 0
% 1.66/1.16  
% 1.66/1.16  Ordering : KBO
% 1.66/1.16  
% 1.66/1.16  Simplification rules
% 1.66/1.16  ----------------------
% 1.66/1.16  #Subsume      : 1
% 1.66/1.16  #Demod        : 0
% 1.66/1.16  #Tautology    : 7
% 1.66/1.16  #SimpNegUnit  : 1
% 1.66/1.16  #BackRed      : 0
% 1.66/1.16  
% 1.66/1.16  #Partial instantiations: 0
% 1.66/1.16  #Strategies tried      : 1
% 1.66/1.16  
% 1.66/1.16  Timing (in seconds)
% 1.66/1.16  ----------------------
% 1.66/1.16  Preprocessing        : 0.26
% 1.66/1.16  Parsing              : 0.14
% 1.66/1.16  CNF conversion       : 0.02
% 1.66/1.16  Main loop            : 0.16
% 1.66/1.16  Inferencing          : 0.06
% 1.66/1.16  Reduction            : 0.04
% 1.66/1.16  Demodulation         : 0.03
% 1.66/1.16  BG Simplification    : 0.01
% 1.66/1.16  Subsumption          : 0.04
% 1.66/1.16  Abstraction          : 0.01
% 1.66/1.16  MUC search           : 0.00
% 1.66/1.16  Cooper               : 0.00
% 1.66/1.16  Total                : 0.44
% 1.66/1.16  Index Insertion      : 0.00
% 1.66/1.16  Index Deletion       : 0.00
% 1.66/1.16  Index Matching       : 0.00
% 1.66/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
