%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:42 EST 2020

% Result     : Theorem 7.49s
% Output     : CNFRefutation 7.49s
% Verified   : 
% Statistics : Number of formulae       :   42 (  54 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   42 (  64 expanded)
%              Number of equality atoms :   10 (  17 expanded)
%              Maximal formula depth    :   10 (   3 average)
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

tff(f_49,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( ( r1_tarski(A,k2_zfmisc_1(C,D))
          & r1_tarski(B,k2_zfmisc_1(E,F)) )
       => r1_tarski(k2_xboole_0(A,B),k2_zfmisc_1(k2_xboole_0(C,E),k2_xboole_0(D,F))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).

tff(c_14,plain,(
    ! [A_16,C_18,B_17] : k2_xboole_0(k2_zfmisc_1(A_16,C_18),k2_zfmisc_1(B_17,C_18)) = k2_zfmisc_1(k2_xboole_0(A_16,B_17),C_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_72,plain,(
    ! [A_25,B_26] :
      ( k2_xboole_0(A_25,B_26) = B_26
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_88,plain,(
    k2_xboole_0('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_72])).

tff(c_10,plain,(
    ! [A_12,B_13] : r1_tarski(A_12,k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_99,plain,(
    ! [A_29,C_30,B_31] :
      ( r1_tarski(A_29,C_30)
      | ~ r1_tarski(k2_xboole_0(A_29,B_31),C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_115,plain,(
    ! [A_29,B_31,B_13] : r1_tarski(A_29,k2_xboole_0(k2_xboole_0(A_29,B_31),B_13)) ),
    inference(resolution,[status(thm)],[c_10,c_99])).

tff(c_440,plain,(
    ! [B_53] : r1_tarski('#skF_1',k2_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),B_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_115])).

tff(c_451,plain,(
    ! [B_17] : r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3',B_17),'#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_440])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_87,plain,(
    k2_xboole_0('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) = k2_zfmisc_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_72])).

tff(c_294,plain,(
    ! [B_47] : r1_tarski('#skF_2',k2_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'),B_47)) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_115])).

tff(c_328,plain,(
    ! [B_49] : r1_tarski('#skF_2',k2_xboole_0(B_49,k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_294])).

tff(c_337,plain,(
    ! [A_16] : r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0(A_16,'#skF_5'),'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_328])).

tff(c_16,plain,(
    ! [C_18,A_16,B_17] : k2_xboole_0(k2_zfmisc_1(C_18,A_16),k2_zfmisc_1(C_18,B_17)) = k2_zfmisc_1(C_18,k2_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_505,plain,(
    ! [A_56,C_57,B_58,D_59] :
      ( r1_tarski(k2_xboole_0(A_56,C_57),k2_xboole_0(B_58,D_59))
      | ~ r1_tarski(C_57,D_59)
      | ~ r1_tarski(A_56,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_9165,plain,(
    ! [A_274,C_275,A_273,B_272,C_276] :
      ( r1_tarski(k2_xboole_0(A_274,C_275),k2_zfmisc_1(C_276,k2_xboole_0(A_273,B_272)))
      | ~ r1_tarski(C_275,k2_zfmisc_1(C_276,B_272))
      | ~ r1_tarski(A_274,k2_zfmisc_1(C_276,A_273)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_505])).

tff(c_18,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_2'),k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_9173,plain,
    ( ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),'#skF_6'))
    | ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_9165,c_18])).

tff(c_9282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_451,c_337,c_9173])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:47:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.49/2.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.49/2.76  
% 7.49/2.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.49/2.77  %$ r1_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.49/2.77  
% 7.49/2.77  %Foreground sorts:
% 7.49/2.77  
% 7.49/2.77  
% 7.49/2.77  %Background operators:
% 7.49/2.77  
% 7.49/2.77  
% 7.49/2.77  %Foreground operators:
% 7.49/2.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.49/2.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.49/2.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.49/2.77  tff('#skF_5', type, '#skF_5': $i).
% 7.49/2.77  tff('#skF_6', type, '#skF_6': $i).
% 7.49/2.77  tff('#skF_2', type, '#skF_2': $i).
% 7.49/2.77  tff('#skF_3', type, '#skF_3': $i).
% 7.49/2.77  tff('#skF_1', type, '#skF_1': $i).
% 7.49/2.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.49/2.77  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.49/2.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.49/2.77  tff('#skF_4', type, '#skF_4': $i).
% 7.49/2.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.49/2.77  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.49/2.77  
% 7.49/2.78  tff(f_49, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 7.49/2.78  tff(f_56, negated_conjecture, ~(![A, B, C, D, E, F]: ((r1_tarski(A, k2_zfmisc_1(C, D)) & r1_tarski(B, k2_zfmisc_1(E, F))) => r1_tarski(k2_xboole_0(A, B), k2_zfmisc_1(k2_xboole_0(C, E), k2_xboole_0(D, F))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 7.49/2.78  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.49/2.78  tff(f_43, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.49/2.78  tff(f_31, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 7.49/2.78  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 7.49/2.78  tff(f_41, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_xboole_1)).
% 7.49/2.78  tff(c_14, plain, (![A_16, C_18, B_17]: (k2_xboole_0(k2_zfmisc_1(A_16, C_18), k2_zfmisc_1(B_17, C_18))=k2_zfmisc_1(k2_xboole_0(A_16, B_17), C_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.49/2.78  tff(c_22, plain, (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.49/2.78  tff(c_72, plain, (![A_25, B_26]: (k2_xboole_0(A_25, B_26)=B_26 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.49/2.78  tff(c_88, plain, (k2_xboole_0('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_22, c_72])).
% 7.49/2.78  tff(c_10, plain, (![A_12, B_13]: (r1_tarski(A_12, k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.49/2.78  tff(c_99, plain, (![A_29, C_30, B_31]: (r1_tarski(A_29, C_30) | ~r1_tarski(k2_xboole_0(A_29, B_31), C_30))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.49/2.78  tff(c_115, plain, (![A_29, B_31, B_13]: (r1_tarski(A_29, k2_xboole_0(k2_xboole_0(A_29, B_31), B_13)))), inference(resolution, [status(thm)], [c_10, c_99])).
% 7.49/2.78  tff(c_440, plain, (![B_53]: (r1_tarski('#skF_1', k2_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), B_53)))), inference(superposition, [status(thm), theory('equality')], [c_88, c_115])).
% 7.49/2.78  tff(c_451, plain, (![B_17]: (r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', B_17), '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_14, c_440])).
% 7.49/2.78  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.49/2.78  tff(c_20, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.49/2.78  tff(c_87, plain, (k2_xboole_0('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))=k2_zfmisc_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_20, c_72])).
% 7.49/2.78  tff(c_294, plain, (![B_47]: (r1_tarski('#skF_2', k2_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'), B_47)))), inference(superposition, [status(thm), theory('equality')], [c_87, c_115])).
% 7.49/2.78  tff(c_328, plain, (![B_49]: (r1_tarski('#skF_2', k2_xboole_0(B_49, k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_294])).
% 7.49/2.78  tff(c_337, plain, (![A_16]: (r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0(A_16, '#skF_5'), '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_14, c_328])).
% 7.49/2.78  tff(c_16, plain, (![C_18, A_16, B_17]: (k2_xboole_0(k2_zfmisc_1(C_18, A_16), k2_zfmisc_1(C_18, B_17))=k2_zfmisc_1(C_18, k2_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.49/2.78  tff(c_505, plain, (![A_56, C_57, B_58, D_59]: (r1_tarski(k2_xboole_0(A_56, C_57), k2_xboole_0(B_58, D_59)) | ~r1_tarski(C_57, D_59) | ~r1_tarski(A_56, B_58))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.49/2.78  tff(c_9165, plain, (![A_274, C_275, A_273, B_272, C_276]: (r1_tarski(k2_xboole_0(A_274, C_275), k2_zfmisc_1(C_276, k2_xboole_0(A_273, B_272))) | ~r1_tarski(C_275, k2_zfmisc_1(C_276, B_272)) | ~r1_tarski(A_274, k2_zfmisc_1(C_276, A_273)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_505])).
% 7.49/2.78  tff(c_18, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_2'), k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.49/2.78  tff(c_9173, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), '#skF_6')) | ~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_9165, c_18])).
% 7.49/2.78  tff(c_9282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_451, c_337, c_9173])).
% 7.49/2.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.49/2.78  
% 7.49/2.78  Inference rules
% 7.49/2.78  ----------------------
% 7.49/2.78  #Ref     : 0
% 7.49/2.78  #Sup     : 2203
% 7.49/2.78  #Fact    : 0
% 7.49/2.78  #Define  : 0
% 7.49/2.78  #Split   : 0
% 7.49/2.78  #Chain   : 0
% 7.49/2.78  #Close   : 0
% 7.49/2.78  
% 7.49/2.78  Ordering : KBO
% 7.49/2.78  
% 7.49/2.78  Simplification rules
% 7.49/2.78  ----------------------
% 7.49/2.78  #Subsume      : 67
% 7.49/2.78  #Demod        : 1178
% 7.49/2.78  #Tautology    : 985
% 7.49/2.78  #SimpNegUnit  : 0
% 7.49/2.78  #BackRed      : 0
% 7.49/2.78  
% 7.49/2.78  #Partial instantiations: 0
% 7.49/2.78  #Strategies tried      : 1
% 7.49/2.78  
% 7.49/2.78  Timing (in seconds)
% 7.49/2.78  ----------------------
% 7.49/2.78  Preprocessing        : 0.27
% 7.49/2.78  Parsing              : 0.15
% 7.49/2.78  CNF conversion       : 0.02
% 7.49/2.78  Main loop            : 1.68
% 7.49/2.78  Inferencing          : 0.39
% 7.49/2.78  Reduction            : 0.83
% 7.49/2.78  Demodulation         : 0.73
% 7.49/2.78  BG Simplification    : 0.05
% 7.49/2.78  Subsumption          : 0.32
% 7.49/2.78  Abstraction          : 0.06
% 7.49/2.78  MUC search           : 0.00
% 7.49/2.78  Cooper               : 0.00
% 7.49/2.78  Total                : 1.98
% 7.49/2.78  Index Insertion      : 0.00
% 7.49/2.78  Index Deletion       : 0.00
% 7.49/2.78  Index Matching       : 0.00
% 7.49/2.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
