%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:12 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   26 (  34 expanded)
%              Number of leaves         :   13 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   25 (  44 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( A != B
       => ( r1_xboole_0(k2_zfmisc_1(k1_tarski(A),C),k2_zfmisc_1(k1_tarski(B),D))
          & r1_xboole_0(k2_zfmisc_1(C,k1_tarski(A)),k2_zfmisc_1(D,k1_tarski(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(c_10,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r1_xboole_0(k1_tarski(A_5),k1_tarski(B_6))
      | B_6 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2,plain,(
    ! [C_3,D_4,A_1,B_2] :
      ( ~ r1_xboole_0(C_3,D_4)
      | r1_xboole_0(k2_zfmisc_1(A_1,C_3),k2_zfmisc_1(B_2,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( ~ r1_xboole_0(A_1,B_2)
      | r1_xboole_0(k2_zfmisc_1(A_1,C_3),k2_zfmisc_1(B_2,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1('#skF_3',k1_tarski('#skF_1')),k2_zfmisc_1('#skF_4',k1_tarski('#skF_2')))
    | ~ r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_3'),k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_14,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_3'),k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_8])).

tff(c_22,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_4,c_14])).

tff(c_25,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_22])).

tff(c_29,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_25])).

tff(c_30,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_3',k1_tarski('#skF_1')),k2_zfmisc_1('#skF_4',k1_tarski('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_8])).

tff(c_38,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2,c_30])).

tff(c_42,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_38])).

tff(c_46,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:04:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.10  
% 1.59/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.10  %$ r1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.59/1.10  
% 1.59/1.10  %Foreground sorts:
% 1.59/1.10  
% 1.59/1.10  
% 1.59/1.10  %Background operators:
% 1.59/1.10  
% 1.59/1.10  
% 1.59/1.10  %Foreground operators:
% 1.59/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.59/1.10  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.59/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.59/1.10  tff('#skF_3', type, '#skF_3': $i).
% 1.59/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.59/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.10  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.59/1.10  tff('#skF_4', type, '#skF_4': $i).
% 1.59/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.10  
% 1.59/1.11  tff(f_44, negated_conjecture, ~(![A, B, C, D]: (~(A = B) => (r1_xboole_0(k2_zfmisc_1(k1_tarski(A), C), k2_zfmisc_1(k1_tarski(B), D)) & r1_xboole_0(k2_zfmisc_1(C, k1_tarski(A)), k2_zfmisc_1(D, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t131_zfmisc_1)).
% 1.59/1.11  tff(f_36, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 1.59/1.11  tff(f_31, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 1.59/1.11  tff(c_10, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.59/1.11  tff(c_6, plain, (![A_5, B_6]: (r1_xboole_0(k1_tarski(A_5), k1_tarski(B_6)) | B_6=A_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.59/1.11  tff(c_2, plain, (![C_3, D_4, A_1, B_2]: (~r1_xboole_0(C_3, D_4) | r1_xboole_0(k2_zfmisc_1(A_1, C_3), k2_zfmisc_1(B_2, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.59/1.11  tff(c_4, plain, (![A_1, B_2, C_3, D_4]: (~r1_xboole_0(A_1, B_2) | r1_xboole_0(k2_zfmisc_1(A_1, C_3), k2_zfmisc_1(B_2, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.59/1.11  tff(c_8, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_3', k1_tarski('#skF_1')), k2_zfmisc_1('#skF_4', k1_tarski('#skF_2'))) | ~r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_3'), k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.59/1.11  tff(c_14, plain, (~r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_3'), k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_4'))), inference(splitLeft, [status(thm)], [c_8])).
% 1.59/1.11  tff(c_22, plain, (~r1_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_4, c_14])).
% 1.59/1.11  tff(c_25, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_6, c_22])).
% 1.59/1.11  tff(c_29, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_25])).
% 1.59/1.11  tff(c_30, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_3', k1_tarski('#skF_1')), k2_zfmisc_1('#skF_4', k1_tarski('#skF_2')))), inference(splitRight, [status(thm)], [c_8])).
% 1.59/1.11  tff(c_38, plain, (~r1_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_2, c_30])).
% 1.59/1.11  tff(c_42, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_6, c_38])).
% 1.59/1.11  tff(c_46, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_42])).
% 1.59/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.11  
% 1.59/1.11  Inference rules
% 1.59/1.11  ----------------------
% 1.59/1.11  #Ref     : 0
% 1.59/1.11  #Sup     : 6
% 1.59/1.11  #Fact    : 0
% 1.59/1.11  #Define  : 0
% 1.59/1.11  #Split   : 1
% 1.59/1.11  #Chain   : 0
% 1.59/1.11  #Close   : 0
% 1.59/1.11  
% 1.59/1.11  Ordering : KBO
% 1.59/1.11  
% 1.59/1.11  Simplification rules
% 1.59/1.11  ----------------------
% 1.59/1.11  #Subsume      : 0
% 1.59/1.11  #Demod        : 0
% 1.59/1.11  #Tautology    : 0
% 1.59/1.11  #SimpNegUnit  : 2
% 1.59/1.11  #BackRed      : 0
% 1.59/1.11  
% 1.59/1.11  #Partial instantiations: 0
% 1.59/1.11  #Strategies tried      : 1
% 1.59/1.11  
% 1.59/1.11  Timing (in seconds)
% 1.59/1.11  ----------------------
% 1.59/1.11  Preprocessing        : 0.26
% 1.59/1.11  Parsing              : 0.14
% 1.59/1.11  CNF conversion       : 0.02
% 1.59/1.11  Main loop            : 0.08
% 1.59/1.11  Inferencing          : 0.04
% 1.59/1.11  Reduction            : 0.01
% 1.59/1.11  Demodulation         : 0.00
% 1.59/1.11  BG Simplification    : 0.01
% 1.59/1.11  Subsumption          : 0.02
% 1.59/1.11  Abstraction          : 0.00
% 1.59/1.11  MUC search           : 0.00
% 1.59/1.11  Cooper               : 0.00
% 1.59/1.11  Total                : 0.36
% 1.59/1.11  Index Insertion      : 0.00
% 1.59/1.11  Index Deletion       : 0.00
% 1.59/1.11  Index Matching       : 0.00
% 1.59/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
