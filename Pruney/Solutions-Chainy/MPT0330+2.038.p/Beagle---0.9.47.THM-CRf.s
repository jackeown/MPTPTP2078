%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:44 EST 2020

% Result     : Theorem 5.36s
% Output     : CNFRefutation 5.36s
% Verified   : 
% Statistics : Number of formulae       :   39 (  44 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   44 (  55 expanded)
%              Number of equality atoms :    7 (  12 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).

tff(c_18,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_193,plain,(
    ! [C_37,A_38,B_39] : k2_xboole_0(k2_zfmisc_1(C_37,A_38),k2_zfmisc_1(C_37,B_39)) = k2_zfmisc_1(C_37,k2_xboole_0(A_38,B_39)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,k2_xboole_0(C_3,B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_213,plain,(
    ! [A_1,C_37,A_38,B_39] :
      ( r1_tarski(A_1,k2_zfmisc_1(C_37,k2_xboole_0(A_38,B_39)))
      | ~ r1_tarski(A_1,k2_zfmisc_1(C_37,B_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_2])).

tff(c_20,plain,(
    r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_22,plain,(
    ! [A_20,B_21] :
      ( k2_xboole_0(A_20,B_21) = B_21
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_34,plain,(
    k2_xboole_0('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_22])).

tff(c_10,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_35,plain,(
    ! [A_22,C_23,B_24] :
      ( r1_tarski(A_22,C_23)
      | ~ r1_tarski(k2_xboole_0(A_22,B_24),C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_40,plain,(
    ! [A_22,B_24,B_14] : r1_tarski(A_22,k2_xboole_0(k2_xboole_0(A_22,B_24),B_14)) ),
    inference(resolution,[status(thm)],[c_10,c_35])).

tff(c_103,plain,(
    ! [B_14] : r1_tarski('#skF_1',k2_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),B_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_40])).

tff(c_204,plain,(
    ! [B_39] : r1_tarski('#skF_1',k2_zfmisc_1('#skF_3',k2_xboole_0('#skF_4',B_39))) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_103])).

tff(c_12,plain,(
    ! [A_15,C_17,B_16] : k2_xboole_0(k2_zfmisc_1(A_15,C_17),k2_zfmisc_1(B_16,C_17)) = k2_zfmisc_1(k2_xboole_0(A_15,B_16),C_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_556,plain,(
    ! [A_71,C_72,B_73,D_74] :
      ( r1_tarski(k2_xboole_0(A_71,C_72),k2_xboole_0(B_73,D_74))
      | ~ r1_tarski(C_72,D_74)
      | ~ r1_tarski(A_71,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3966,plain,(
    ! [B_240,C_241,A_243,C_239,A_242] :
      ( r1_tarski(k2_xboole_0(A_242,C_241),k2_zfmisc_1(k2_xboole_0(A_243,B_240),C_239))
      | ~ r1_tarski(C_241,k2_zfmisc_1(B_240,C_239))
      | ~ r1_tarski(A_242,k2_zfmisc_1(A_243,C_239)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_556])).

tff(c_16,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_2'),k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3978,plain,
    ( ~ r1_tarski('#skF_2',k2_zfmisc_1('#skF_5',k2_xboole_0('#skF_4','#skF_6')))
    | ~ r1_tarski('#skF_1',k2_zfmisc_1('#skF_3',k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_3966,c_16])).

tff(c_4042,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1('#skF_5',k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_3978])).

tff(c_4050,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_213,c_4042])).

tff(c_4055,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_4050])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n013.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:23:54 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.36/2.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.36/2.00  
% 5.36/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.36/2.01  %$ r1_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.36/2.01  
% 5.36/2.01  %Foreground sorts:
% 5.36/2.01  
% 5.36/2.01  
% 5.36/2.01  %Background operators:
% 5.36/2.01  
% 5.36/2.01  
% 5.36/2.01  %Foreground operators:
% 5.36/2.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.36/2.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.36/2.01  tff('#skF_5', type, '#skF_5': $i).
% 5.36/2.01  tff('#skF_6', type, '#skF_6': $i).
% 5.36/2.01  tff('#skF_2', type, '#skF_2': $i).
% 5.36/2.01  tff('#skF_3', type, '#skF_3': $i).
% 5.36/2.01  tff('#skF_1', type, '#skF_1': $i).
% 5.36/2.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.36/2.01  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.36/2.01  tff('#skF_4', type, '#skF_4': $i).
% 5.36/2.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.36/2.01  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.36/2.01  
% 5.36/2.02  tff(f_56, negated_conjecture, ~(![A, B, C, D, E, F]: ((r1_tarski(A, k2_zfmisc_1(C, D)) & r1_tarski(B, k2_zfmisc_1(E, F))) => r1_tarski(k2_xboole_0(A, B), k2_zfmisc_1(k2_xboole_0(C, E), k2_xboole_0(D, F))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 5.36/2.02  tff(f_49, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 5.36/2.02  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 5.36/2.02  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.36/2.02  tff(f_45, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.36/2.02  tff(f_33, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 5.36/2.02  tff(f_43, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_xboole_1)).
% 5.36/2.02  tff(c_18, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.36/2.02  tff(c_193, plain, (![C_37, A_38, B_39]: (k2_xboole_0(k2_zfmisc_1(C_37, A_38), k2_zfmisc_1(C_37, B_39))=k2_zfmisc_1(C_37, k2_xboole_0(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.36/2.02  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, k2_xboole_0(C_3, B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.36/2.02  tff(c_213, plain, (![A_1, C_37, A_38, B_39]: (r1_tarski(A_1, k2_zfmisc_1(C_37, k2_xboole_0(A_38, B_39))) | ~r1_tarski(A_1, k2_zfmisc_1(C_37, B_39)))), inference(superposition, [status(thm), theory('equality')], [c_193, c_2])).
% 5.36/2.02  tff(c_20, plain, (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.36/2.02  tff(c_22, plain, (![A_20, B_21]: (k2_xboole_0(A_20, B_21)=B_21 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.36/2.02  tff(c_34, plain, (k2_xboole_0('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_20, c_22])).
% 5.36/2.02  tff(c_10, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.36/2.02  tff(c_35, plain, (![A_22, C_23, B_24]: (r1_tarski(A_22, C_23) | ~r1_tarski(k2_xboole_0(A_22, B_24), C_23))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.36/2.02  tff(c_40, plain, (![A_22, B_24, B_14]: (r1_tarski(A_22, k2_xboole_0(k2_xboole_0(A_22, B_24), B_14)))), inference(resolution, [status(thm)], [c_10, c_35])).
% 5.36/2.02  tff(c_103, plain, (![B_14]: (r1_tarski('#skF_1', k2_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), B_14)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_40])).
% 5.36/2.02  tff(c_204, plain, (![B_39]: (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', k2_xboole_0('#skF_4', B_39))))), inference(superposition, [status(thm), theory('equality')], [c_193, c_103])).
% 5.36/2.02  tff(c_12, plain, (![A_15, C_17, B_16]: (k2_xboole_0(k2_zfmisc_1(A_15, C_17), k2_zfmisc_1(B_16, C_17))=k2_zfmisc_1(k2_xboole_0(A_15, B_16), C_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.36/2.02  tff(c_556, plain, (![A_71, C_72, B_73, D_74]: (r1_tarski(k2_xboole_0(A_71, C_72), k2_xboole_0(B_73, D_74)) | ~r1_tarski(C_72, D_74) | ~r1_tarski(A_71, B_73))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.36/2.02  tff(c_3966, plain, (![B_240, C_241, A_243, C_239, A_242]: (r1_tarski(k2_xboole_0(A_242, C_241), k2_zfmisc_1(k2_xboole_0(A_243, B_240), C_239)) | ~r1_tarski(C_241, k2_zfmisc_1(B_240, C_239)) | ~r1_tarski(A_242, k2_zfmisc_1(A_243, C_239)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_556])).
% 5.36/2.02  tff(c_16, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_2'), k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.36/2.02  tff(c_3978, plain, (~r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', k2_xboole_0('#skF_4', '#skF_6'))) | ~r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', k2_xboole_0('#skF_4', '#skF_6')))), inference(resolution, [status(thm)], [c_3966, c_16])).
% 5.36/2.02  tff(c_4042, plain, (~r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', k2_xboole_0('#skF_4', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_3978])).
% 5.36/2.02  tff(c_4050, plain, (~r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_213, c_4042])).
% 5.36/2.02  tff(c_4055, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_4050])).
% 5.36/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.36/2.02  
% 5.36/2.02  Inference rules
% 5.36/2.02  ----------------------
% 5.36/2.02  #Ref     : 0
% 5.36/2.02  #Sup     : 1011
% 5.36/2.02  #Fact    : 0
% 5.36/2.02  #Define  : 0
% 5.36/2.02  #Split   : 2
% 5.36/2.02  #Chain   : 0
% 5.36/2.02  #Close   : 0
% 5.36/2.02  
% 5.36/2.02  Ordering : KBO
% 5.36/2.02  
% 5.36/2.02  Simplification rules
% 5.36/2.02  ----------------------
% 5.36/2.02  #Subsume      : 67
% 5.36/2.02  #Demod        : 196
% 5.36/2.02  #Tautology    : 212
% 5.36/2.02  #SimpNegUnit  : 0
% 5.36/2.02  #BackRed      : 0
% 5.36/2.02  
% 5.36/2.02  #Partial instantiations: 0
% 5.36/2.02  #Strategies tried      : 1
% 5.36/2.02  
% 5.36/2.02  Timing (in seconds)
% 5.36/2.02  ----------------------
% 5.36/2.02  Preprocessing        : 0.28
% 5.36/2.02  Parsing              : 0.17
% 5.36/2.02  CNF conversion       : 0.02
% 5.36/2.02  Main loop            : 0.96
% 5.36/2.02  Inferencing          : 0.30
% 5.36/2.02  Reduction            : 0.36
% 5.36/2.02  Demodulation         : 0.29
% 5.36/2.02  BG Simplification    : 0.03
% 5.36/2.02  Subsumption          : 0.20
% 5.36/2.02  Abstraction          : 0.04
% 5.36/2.02  MUC search           : 0.00
% 5.36/2.02  Cooper               : 0.00
% 5.36/2.02  Total                : 1.26
% 5.36/2.02  Index Insertion      : 0.00
% 5.36/2.02  Index Deletion       : 0.00
% 5.36/2.02  Index Matching       : 0.00
% 5.36/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
