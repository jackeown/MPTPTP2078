%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:44 EST 2020

% Result     : Theorem 4.10s
% Output     : CNFRefutation 4.10s
% Verified   : 
% Statistics : Number of formulae       :   40 (  53 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   44 (  73 expanded)
%              Number of equality atoms :    4 (  12 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( ( r1_tarski(A,k2_zfmisc_1(C,D))
          & r1_tarski(B,k2_zfmisc_1(E,F)) )
       => r1_tarski(k2_xboole_0(A,B),k2_zfmisc_1(k2_xboole_0(C,E),k2_xboole_0(D,F))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).

tff(c_18,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_312,plain,(
    ! [C_69,A_70,B_71] : k2_xboole_0(k2_zfmisc_1(C_69,A_70),k2_zfmisc_1(C_69,B_71)) = k2_zfmisc_1(C_69,k2_xboole_0(A_70,B_71)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,k2_xboole_0(C_3,B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_349,plain,(
    ! [A_1,C_69,A_70,B_71] :
      ( r1_tarski(A_1,k2_zfmisc_1(C_69,k2_xboole_0(A_70,B_71)))
      | ~ r1_tarski(A_1,k2_zfmisc_1(C_69,B_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_2])).

tff(c_20,plain,(
    r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_362,plain,(
    ! [C_72,A_73,B_74] : r1_tarski(k2_zfmisc_1(C_72,A_73),k2_zfmisc_1(C_72,k2_xboole_0(A_73,B_74))) ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_8])).

tff(c_6,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(A_8,C_10)
      | ~ r1_tarski(B_9,C_10)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_385,plain,(
    ! [A_8,C_72,A_73,B_74] :
      ( r1_tarski(A_8,k2_zfmisc_1(C_72,k2_xboole_0(A_73,B_74)))
      | ~ r1_tarski(A_8,k2_zfmisc_1(C_72,A_73)) ) ),
    inference(resolution,[status(thm)],[c_362,c_6])).

tff(c_12,plain,(
    ! [A_15,C_17,B_16] : k2_xboole_0(k2_zfmisc_1(A_15,C_17),k2_zfmisc_1(B_16,C_17)) = k2_zfmisc_1(k2_xboole_0(A_15,B_16),C_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_448,plain,(
    ! [A_83,C_84,B_85,D_86] :
      ( r1_tarski(k2_xboole_0(A_83,C_84),k2_xboole_0(B_85,D_86))
      | ~ r1_tarski(C_84,D_86)
      | ~ r1_tarski(A_83,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1740,plain,(
    ! [A_190,C_188,A_189,C_186,B_187] :
      ( r1_tarski(k2_xboole_0(A_190,C_188),k2_zfmisc_1(k2_xboole_0(A_189,B_187),C_186))
      | ~ r1_tarski(C_188,k2_zfmisc_1(B_187,C_186))
      | ~ r1_tarski(A_190,k2_zfmisc_1(A_189,C_186)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_448])).

tff(c_16,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_2'),k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1795,plain,
    ( ~ r1_tarski('#skF_2',k2_zfmisc_1('#skF_5',k2_xboole_0('#skF_4','#skF_6')))
    | ~ r1_tarski('#skF_1',k2_zfmisc_1('#skF_3',k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_1740,c_16])).

tff(c_1823,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1('#skF_3',k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_1795])).

tff(c_1826,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_385,c_1823])).

tff(c_1833,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1826])).

tff(c_1834,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1('#skF_5',k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_1795])).

tff(c_1841,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_349,c_1834])).

tff(c_1846,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1841])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:00:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.10/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.10/1.71  
% 4.10/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.10/1.72  %$ r1_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.10/1.72  
% 4.10/1.72  %Foreground sorts:
% 4.10/1.72  
% 4.10/1.72  
% 4.10/1.72  %Background operators:
% 4.10/1.72  
% 4.10/1.72  
% 4.10/1.72  %Foreground operators:
% 4.10/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.10/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.10/1.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.10/1.72  tff('#skF_5', type, '#skF_5': $i).
% 4.10/1.72  tff('#skF_6', type, '#skF_6': $i).
% 4.10/1.72  tff('#skF_2', type, '#skF_2': $i).
% 4.10/1.72  tff('#skF_3', type, '#skF_3': $i).
% 4.10/1.72  tff('#skF_1', type, '#skF_1': $i).
% 4.10/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.10/1.72  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.10/1.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.10/1.72  tff('#skF_4', type, '#skF_4': $i).
% 4.10/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.10/1.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.10/1.72  
% 4.10/1.73  tff(f_56, negated_conjecture, ~(![A, B, C, D, E, F]: ((r1_tarski(A, k2_zfmisc_1(C, D)) & r1_tarski(B, k2_zfmisc_1(E, F))) => r1_tarski(k2_xboole_0(A, B), k2_zfmisc_1(k2_xboole_0(C, E), k2_xboole_0(D, F))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 4.10/1.73  tff(f_49, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 4.10/1.73  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 4.10/1.73  tff(f_43, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.10/1.73  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.10/1.73  tff(f_35, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_xboole_1)).
% 4.10/1.73  tff(c_18, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.10/1.73  tff(c_312, plain, (![C_69, A_70, B_71]: (k2_xboole_0(k2_zfmisc_1(C_69, A_70), k2_zfmisc_1(C_69, B_71))=k2_zfmisc_1(C_69, k2_xboole_0(A_70, B_71)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.10/1.73  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, k2_xboole_0(C_3, B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.10/1.73  tff(c_349, plain, (![A_1, C_69, A_70, B_71]: (r1_tarski(A_1, k2_zfmisc_1(C_69, k2_xboole_0(A_70, B_71))) | ~r1_tarski(A_1, k2_zfmisc_1(C_69, B_71)))), inference(superposition, [status(thm), theory('equality')], [c_312, c_2])).
% 4.10/1.73  tff(c_20, plain, (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.10/1.73  tff(c_8, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.10/1.73  tff(c_362, plain, (![C_72, A_73, B_74]: (r1_tarski(k2_zfmisc_1(C_72, A_73), k2_zfmisc_1(C_72, k2_xboole_0(A_73, B_74))))), inference(superposition, [status(thm), theory('equality')], [c_312, c_8])).
% 4.10/1.73  tff(c_6, plain, (![A_8, C_10, B_9]: (r1_tarski(A_8, C_10) | ~r1_tarski(B_9, C_10) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.10/1.73  tff(c_385, plain, (![A_8, C_72, A_73, B_74]: (r1_tarski(A_8, k2_zfmisc_1(C_72, k2_xboole_0(A_73, B_74))) | ~r1_tarski(A_8, k2_zfmisc_1(C_72, A_73)))), inference(resolution, [status(thm)], [c_362, c_6])).
% 4.10/1.73  tff(c_12, plain, (![A_15, C_17, B_16]: (k2_xboole_0(k2_zfmisc_1(A_15, C_17), k2_zfmisc_1(B_16, C_17))=k2_zfmisc_1(k2_xboole_0(A_15, B_16), C_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.10/1.73  tff(c_448, plain, (![A_83, C_84, B_85, D_86]: (r1_tarski(k2_xboole_0(A_83, C_84), k2_xboole_0(B_85, D_86)) | ~r1_tarski(C_84, D_86) | ~r1_tarski(A_83, B_85))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.10/1.73  tff(c_1740, plain, (![A_190, C_188, A_189, C_186, B_187]: (r1_tarski(k2_xboole_0(A_190, C_188), k2_zfmisc_1(k2_xboole_0(A_189, B_187), C_186)) | ~r1_tarski(C_188, k2_zfmisc_1(B_187, C_186)) | ~r1_tarski(A_190, k2_zfmisc_1(A_189, C_186)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_448])).
% 4.10/1.73  tff(c_16, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_2'), k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.10/1.73  tff(c_1795, plain, (~r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', k2_xboole_0('#skF_4', '#skF_6'))) | ~r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', k2_xboole_0('#skF_4', '#skF_6')))), inference(resolution, [status(thm)], [c_1740, c_16])).
% 4.10/1.73  tff(c_1823, plain, (~r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', k2_xboole_0('#skF_4', '#skF_6')))), inference(splitLeft, [status(thm)], [c_1795])).
% 4.10/1.73  tff(c_1826, plain, (~r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_385, c_1823])).
% 4.10/1.73  tff(c_1833, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_1826])).
% 4.10/1.73  tff(c_1834, plain, (~r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', k2_xboole_0('#skF_4', '#skF_6')))), inference(splitRight, [status(thm)], [c_1795])).
% 4.10/1.73  tff(c_1841, plain, (~r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_349, c_1834])).
% 4.10/1.73  tff(c_1846, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_1841])).
% 4.10/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.10/1.73  
% 4.10/1.73  Inference rules
% 4.10/1.73  ----------------------
% 4.10/1.73  #Ref     : 0
% 4.10/1.73  #Sup     : 512
% 4.10/1.73  #Fact    : 0
% 4.10/1.73  #Define  : 0
% 4.10/1.73  #Split   : 5
% 4.10/1.73  #Chain   : 0
% 4.10/1.73  #Close   : 0
% 4.10/1.73  
% 4.10/1.73  Ordering : KBO
% 4.10/1.73  
% 4.10/1.73  Simplification rules
% 4.10/1.73  ----------------------
% 4.10/1.73  #Subsume      : 21
% 4.10/1.73  #Demod        : 60
% 4.10/1.73  #Tautology    : 66
% 4.10/1.73  #SimpNegUnit  : 0
% 4.10/1.73  #BackRed      : 0
% 4.10/1.73  
% 4.10/1.73  #Partial instantiations: 0
% 4.10/1.73  #Strategies tried      : 1
% 4.10/1.73  
% 4.10/1.73  Timing (in seconds)
% 4.10/1.73  ----------------------
% 4.10/1.73  Preprocessing        : 0.27
% 4.10/1.73  Parsing              : 0.15
% 4.10/1.73  CNF conversion       : 0.02
% 4.10/1.73  Main loop            : 0.69
% 4.10/1.73  Inferencing          : 0.22
% 4.10/1.73  Reduction            : 0.23
% 4.10/1.73  Demodulation         : 0.18
% 4.10/1.73  BG Simplification    : 0.02
% 4.10/1.73  Subsumption          : 0.17
% 4.10/1.73  Abstraction          : 0.03
% 4.10/1.73  MUC search           : 0.00
% 4.10/1.73  Cooper               : 0.00
% 4.10/1.73  Total                : 0.99
% 4.10/1.73  Index Insertion      : 0.00
% 4.10/1.73  Index Deletion       : 0.00
% 4.10/1.73  Index Matching       : 0.00
% 4.10/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
