%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:53 EST 2020

% Result     : Theorem 1.45s
% Output     : CNFRefutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   19 (  22 expanded)
%              Number of leaves         :   12 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  16 expanded)
%              Number of equality atoms :   10 (  15 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_zfmisc_1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_zfmisc_1(k2_xboole_0(A,B),k2_xboole_0(C,D)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(A,D)),k2_zfmisc_1(B,C)),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_zfmisc_1)).

tff(c_4,plain,(
    ! [A_4,C_6,B_5] : k2_xboole_0(k2_zfmisc_1(A_4,C_6),k2_zfmisc_1(B_5,C_6)) = k2_zfmisc_1(k2_xboole_0(A_4,B_5),C_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [C_6,A_4,B_5] : k2_xboole_0(k2_zfmisc_1(C_6,A_4),k2_zfmisc_1(C_6,B_5)) = k2_zfmisc_1(C_6,k2_xboole_0(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1('#skF_1','#skF_3'),k2_zfmisc_1('#skF_1','#skF_4')),k2_zfmisc_1('#skF_2','#skF_3')),k2_zfmisc_1('#skF_2','#skF_4')) != k2_zfmisc_1(k2_xboole_0('#skF_1','#skF_2'),k2_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_9,plain,(
    k2_xboole_0(k2_xboole_0(k2_zfmisc_1('#skF_1',k2_xboole_0('#skF_3','#skF_4')),k2_zfmisc_1('#skF_2','#skF_3')),k2_zfmisc_1('#skF_2','#skF_4')) != k2_zfmisc_1(k2_xboole_0('#skF_1','#skF_2'),k2_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_10,plain,(
    k2_xboole_0(k2_zfmisc_1('#skF_1',k2_xboole_0('#skF_3','#skF_4')),k2_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'),k2_zfmisc_1('#skF_2','#skF_4'))) != k2_zfmisc_1(k2_xboole_0('#skF_1','#skF_2'),k2_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_9])).

tff(c_12,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n007.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 14:53:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.45/1.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.45/1.05  
% 1.45/1.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.05  %$ k2_zfmisc_1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.58/1.05  
% 1.58/1.05  %Foreground sorts:
% 1.58/1.05  
% 1.58/1.05  
% 1.58/1.05  %Background operators:
% 1.58/1.05  
% 1.58/1.05  
% 1.58/1.05  %Foreground operators:
% 1.58/1.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.58/1.05  tff('#skF_2', type, '#skF_2': $i).
% 1.58/1.05  tff('#skF_3', type, '#skF_3': $i).
% 1.58/1.05  tff('#skF_1', type, '#skF_1': $i).
% 1.58/1.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.58/1.05  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.58/1.05  tff('#skF_4', type, '#skF_4': $i).
% 1.58/1.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.58/1.05  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.58/1.06  
% 1.58/1.06  tff(f_31, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 1.58/1.06  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 1.58/1.06  tff(f_34, negated_conjecture, ~(![A, B, C, D]: (k2_zfmisc_1(k2_xboole_0(A, B), k2_xboole_0(C, D)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(A, D)), k2_zfmisc_1(B, C)), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_zfmisc_1)).
% 1.58/1.06  tff(c_4, plain, (![A_4, C_6, B_5]: (k2_xboole_0(k2_zfmisc_1(A_4, C_6), k2_zfmisc_1(B_5, C_6))=k2_zfmisc_1(k2_xboole_0(A_4, B_5), C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.58/1.06  tff(c_6, plain, (![C_6, A_4, B_5]: (k2_xboole_0(k2_zfmisc_1(C_6, A_4), k2_zfmisc_1(C_6, B_5))=k2_zfmisc_1(C_6, k2_xboole_0(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.58/1.06  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.58/1.06  tff(c_8, plain, (k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1('#skF_1', '#skF_3'), k2_zfmisc_1('#skF_1', '#skF_4')), k2_zfmisc_1('#skF_2', '#skF_3')), k2_zfmisc_1('#skF_2', '#skF_4'))!=k2_zfmisc_1(k2_xboole_0('#skF_1', '#skF_2'), k2_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.58/1.06  tff(c_9, plain, (k2_xboole_0(k2_xboole_0(k2_zfmisc_1('#skF_1', k2_xboole_0('#skF_3', '#skF_4')), k2_zfmisc_1('#skF_2', '#skF_3')), k2_zfmisc_1('#skF_2', '#skF_4'))!=k2_zfmisc_1(k2_xboole_0('#skF_1', '#skF_2'), k2_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 1.58/1.06  tff(c_10, plain, (k2_xboole_0(k2_zfmisc_1('#skF_1', k2_xboole_0('#skF_3', '#skF_4')), k2_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'), k2_zfmisc_1('#skF_2', '#skF_4')))!=k2_zfmisc_1(k2_xboole_0('#skF_1', '#skF_2'), k2_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_9])).
% 1.58/1.06  tff(c_12, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_6, c_10])).
% 1.58/1.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.06  
% 1.58/1.06  Inference rules
% 1.58/1.06  ----------------------
% 1.58/1.06  #Ref     : 0
% 1.58/1.06  #Sup     : 0
% 1.58/1.06  #Fact    : 0
% 1.58/1.06  #Define  : 0
% 1.58/1.06  #Split   : 0
% 1.58/1.06  #Chain   : 0
% 1.58/1.06  #Close   : 0
% 1.58/1.06  
% 1.58/1.06  Ordering : KBO
% 1.58/1.06  
% 1.58/1.06  Simplification rules
% 1.58/1.06  ----------------------
% 1.58/1.06  #Subsume      : 3
% 1.58/1.06  #Demod        : 4
% 1.58/1.06  #Tautology    : 0
% 1.58/1.06  #SimpNegUnit  : 0
% 1.58/1.06  #BackRed      : 0
% 1.58/1.06  
% 1.58/1.06  #Partial instantiations: 0
% 1.58/1.06  #Strategies tried      : 1
% 1.58/1.06  
% 1.58/1.06  Timing (in seconds)
% 1.58/1.06  ----------------------
% 1.58/1.07  Preprocessing        : 0.25
% 1.58/1.07  Parsing              : 0.14
% 1.58/1.07  CNF conversion       : 0.01
% 1.58/1.07  Main loop            : 0.03
% 1.58/1.07  Inferencing          : 0.00
% 1.58/1.07  Reduction            : 0.02
% 1.58/1.07  Demodulation         : 0.02
% 1.58/1.07  BG Simplification    : 0.01
% 1.58/1.07  Subsumption          : 0.01
% 1.58/1.07  Abstraction          : 0.00
% 1.58/1.07  MUC search           : 0.00
% 1.58/1.07  Cooper               : 0.00
% 1.58/1.07  Total                : 0.31
% 1.58/1.07  Index Insertion      : 0.00
% 1.58/1.07  Index Deletion       : 0.00
% 1.58/1.07  Index Matching       : 0.00
% 1.58/1.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
