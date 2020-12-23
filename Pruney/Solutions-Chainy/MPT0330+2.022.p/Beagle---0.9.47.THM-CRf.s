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

% Result     : Theorem 8.27s
% Output     : CNFRefutation 8.27s
% Verified   : 
% Statistics : Number of formulae       :   41 (  52 expanded)
%              Number of leaves         :   19 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   43 (  64 expanded)
%              Number of equality atoms :   10 (  17 expanded)
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

tff(f_51,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_58,negated_conjecture,(
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

tff(c_486,plain,(
    ! [C_56,A_57,B_58] : k2_xboole_0(k2_zfmisc_1(C_56,A_57),k2_zfmisc_1(C_56,B_58)) = k2_zfmisc_1(C_56,k2_xboole_0(A_57,B_58)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_72,plain,(
    ! [A_26,B_27] :
      ( k2_xboole_0(A_26,B_27) = B_27
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_88,plain,(
    k2_xboole_0('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_72])).

tff(c_10,plain,(
    ! [A_12,B_13] : r1_tarski(A_12,k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_90,plain,(
    ! [A_28,C_29,B_30] :
      ( r1_tarski(A_28,C_29)
      | ~ r1_tarski(k2_xboole_0(A_28,B_30),C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_106,plain,(
    ! [A_28,B_30,B_13] : r1_tarski(A_28,k2_xboole_0(k2_xboole_0(A_28,B_30),B_13)) ),
    inference(resolution,[status(thm)],[c_10,c_90])).

tff(c_412,plain,(
    ! [B_13] : r1_tarski('#skF_1',k2_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),B_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_106])).

tff(c_497,plain,(
    ! [B_58] : r1_tarski('#skF_1',k2_zfmisc_1('#skF_3',k2_xboole_0('#skF_4',B_58))) ),
    inference(superposition,[status(thm),theory(equality)],[c_486,c_412])).

tff(c_20,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_87,plain,(
    k2_xboole_0('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) = k2_zfmisc_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_72])).

tff(c_24,plain,(
    ! [B_22,A_23] : k2_xboole_0(B_22,A_23) = k2_xboole_0(A_23,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_39,plain,(
    ! [A_23,B_22] : r1_tarski(A_23,k2_xboole_0(B_22,A_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_10])).

tff(c_105,plain,(
    ! [A_28,B_22,B_30] : r1_tarski(A_28,k2_xboole_0(B_22,k2_xboole_0(A_28,B_30))) ),
    inference(resolution,[status(thm)],[c_39,c_90])).

tff(c_252,plain,(
    ! [B_22] : r1_tarski('#skF_2',k2_xboole_0(B_22,k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_105])).

tff(c_505,plain,(
    ! [A_57] : r1_tarski('#skF_2',k2_zfmisc_1('#skF_5',k2_xboole_0(A_57,'#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_486,c_252])).

tff(c_14,plain,(
    ! [A_17,C_19,B_18] : k2_xboole_0(k2_zfmisc_1(A_17,C_19),k2_zfmisc_1(B_18,C_19)) = k2_zfmisc_1(k2_xboole_0(A_17,B_18),C_19) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_656,plain,(
    ! [A_64,C_65,B_66,D_67] :
      ( r1_tarski(k2_xboole_0(A_64,C_65),k2_xboole_0(B_66,D_67))
      | ~ r1_tarski(C_65,D_67)
      | ~ r1_tarski(A_64,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_11273,plain,(
    ! [A_325,C_322,C_321,B_324,A_323] :
      ( r1_tarski(k2_xboole_0(A_325,C_322),k2_zfmisc_1(k2_xboole_0(A_323,B_324),C_321))
      | ~ r1_tarski(C_322,k2_zfmisc_1(B_324,C_321))
      | ~ r1_tarski(A_325,k2_zfmisc_1(A_323,C_321)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_656])).

tff(c_18,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_2'),k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_11279,plain,
    ( ~ r1_tarski('#skF_2',k2_zfmisc_1('#skF_5',k2_xboole_0('#skF_4','#skF_6')))
    | ~ r1_tarski('#skF_1',k2_zfmisc_1('#skF_3',k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_11273,c_18])).

tff(c_11393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_497,c_505,c_11279])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:07:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.27/3.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.27/3.07  
% 8.27/3.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.27/3.07  %$ r1_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.27/3.07  
% 8.27/3.07  %Foreground sorts:
% 8.27/3.07  
% 8.27/3.07  
% 8.27/3.07  %Background operators:
% 8.27/3.07  
% 8.27/3.07  
% 8.27/3.07  %Foreground operators:
% 8.27/3.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.27/3.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.27/3.07  tff('#skF_5', type, '#skF_5': $i).
% 8.27/3.07  tff('#skF_6', type, '#skF_6': $i).
% 8.27/3.07  tff('#skF_2', type, '#skF_2': $i).
% 8.27/3.07  tff('#skF_3', type, '#skF_3': $i).
% 8.27/3.07  tff('#skF_1', type, '#skF_1': $i).
% 8.27/3.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.27/3.07  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.27/3.07  tff('#skF_4', type, '#skF_4': $i).
% 8.27/3.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.27/3.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.27/3.07  
% 8.27/3.08  tff(f_51, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 8.27/3.08  tff(f_58, negated_conjecture, ~(![A, B, C, D, E, F]: ((r1_tarski(A, k2_zfmisc_1(C, D)) & r1_tarski(B, k2_zfmisc_1(E, F))) => r1_tarski(k2_xboole_0(A, B), k2_zfmisc_1(k2_xboole_0(C, E), k2_xboole_0(D, F))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 8.27/3.08  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 8.27/3.08  tff(f_43, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 8.27/3.08  tff(f_31, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 8.27/3.08  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.27/3.08  tff(f_41, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_xboole_1)).
% 8.27/3.08  tff(c_486, plain, (![C_56, A_57, B_58]: (k2_xboole_0(k2_zfmisc_1(C_56, A_57), k2_zfmisc_1(C_56, B_58))=k2_zfmisc_1(C_56, k2_xboole_0(A_57, B_58)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.27/3.08  tff(c_22, plain, (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.27/3.08  tff(c_72, plain, (![A_26, B_27]: (k2_xboole_0(A_26, B_27)=B_27 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.27/3.08  tff(c_88, plain, (k2_xboole_0('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_22, c_72])).
% 8.27/3.08  tff(c_10, plain, (![A_12, B_13]: (r1_tarski(A_12, k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.27/3.08  tff(c_90, plain, (![A_28, C_29, B_30]: (r1_tarski(A_28, C_29) | ~r1_tarski(k2_xboole_0(A_28, B_30), C_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.27/3.08  tff(c_106, plain, (![A_28, B_30, B_13]: (r1_tarski(A_28, k2_xboole_0(k2_xboole_0(A_28, B_30), B_13)))), inference(resolution, [status(thm)], [c_10, c_90])).
% 8.27/3.08  tff(c_412, plain, (![B_13]: (r1_tarski('#skF_1', k2_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), B_13)))), inference(superposition, [status(thm), theory('equality')], [c_88, c_106])).
% 8.27/3.08  tff(c_497, plain, (![B_58]: (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', k2_xboole_0('#skF_4', B_58))))), inference(superposition, [status(thm), theory('equality')], [c_486, c_412])).
% 8.27/3.08  tff(c_20, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.27/3.08  tff(c_87, plain, (k2_xboole_0('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))=k2_zfmisc_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_20, c_72])).
% 8.27/3.08  tff(c_24, plain, (![B_22, A_23]: (k2_xboole_0(B_22, A_23)=k2_xboole_0(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.27/3.08  tff(c_39, plain, (![A_23, B_22]: (r1_tarski(A_23, k2_xboole_0(B_22, A_23)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_10])).
% 8.27/3.08  tff(c_105, plain, (![A_28, B_22, B_30]: (r1_tarski(A_28, k2_xboole_0(B_22, k2_xboole_0(A_28, B_30))))), inference(resolution, [status(thm)], [c_39, c_90])).
% 8.27/3.08  tff(c_252, plain, (![B_22]: (r1_tarski('#skF_2', k2_xboole_0(B_22, k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_87, c_105])).
% 8.27/3.08  tff(c_505, plain, (![A_57]: (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', k2_xboole_0(A_57, '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_486, c_252])).
% 8.27/3.08  tff(c_14, plain, (![A_17, C_19, B_18]: (k2_xboole_0(k2_zfmisc_1(A_17, C_19), k2_zfmisc_1(B_18, C_19))=k2_zfmisc_1(k2_xboole_0(A_17, B_18), C_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.27/3.08  tff(c_656, plain, (![A_64, C_65, B_66, D_67]: (r1_tarski(k2_xboole_0(A_64, C_65), k2_xboole_0(B_66, D_67)) | ~r1_tarski(C_65, D_67) | ~r1_tarski(A_64, B_66))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.27/3.08  tff(c_11273, plain, (![A_325, C_322, C_321, B_324, A_323]: (r1_tarski(k2_xboole_0(A_325, C_322), k2_zfmisc_1(k2_xboole_0(A_323, B_324), C_321)) | ~r1_tarski(C_322, k2_zfmisc_1(B_324, C_321)) | ~r1_tarski(A_325, k2_zfmisc_1(A_323, C_321)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_656])).
% 8.27/3.08  tff(c_18, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_2'), k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.27/3.08  tff(c_11279, plain, (~r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', k2_xboole_0('#skF_4', '#skF_6'))) | ~r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', k2_xboole_0('#skF_4', '#skF_6')))), inference(resolution, [status(thm)], [c_11273, c_18])).
% 8.27/3.08  tff(c_11393, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_497, c_505, c_11279])).
% 8.27/3.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.27/3.08  
% 8.27/3.08  Inference rules
% 8.27/3.08  ----------------------
% 8.27/3.08  #Ref     : 0
% 8.27/3.08  #Sup     : 2707
% 8.27/3.08  #Fact    : 0
% 8.27/3.08  #Define  : 0
% 8.27/3.08  #Split   : 0
% 8.27/3.08  #Chain   : 0
% 8.27/3.08  #Close   : 0
% 8.27/3.09  
% 8.27/3.09  Ordering : KBO
% 8.27/3.09  
% 8.27/3.09  Simplification rules
% 8.27/3.09  ----------------------
% 8.27/3.09  #Subsume      : 145
% 8.27/3.09  #Demod        : 1498
% 8.27/3.09  #Tautology    : 1247
% 8.27/3.09  #SimpNegUnit  : 0
% 8.27/3.09  #BackRed      : 0
% 8.27/3.09  
% 8.27/3.09  #Partial instantiations: 0
% 8.27/3.09  #Strategies tried      : 1
% 8.27/3.09  
% 8.27/3.09  Timing (in seconds)
% 8.27/3.09  ----------------------
% 8.27/3.09  Preprocessing        : 0.30
% 8.27/3.09  Parsing              : 0.17
% 8.27/3.09  CNF conversion       : 0.02
% 8.27/3.09  Main loop            : 2.00
% 8.27/3.09  Inferencing          : 0.46
% 8.27/3.09  Reduction            : 1.01
% 8.27/3.09  Demodulation         : 0.90
% 8.27/3.09  BG Simplification    : 0.05
% 8.27/3.09  Subsumption          : 0.37
% 8.27/3.09  Abstraction          : 0.06
% 8.27/3.09  MUC search           : 0.00
% 8.27/3.09  Cooper               : 0.00
% 8.27/3.09  Total                : 2.33
% 8.27/3.09  Index Insertion      : 0.00
% 8.27/3.09  Index Deletion       : 0.00
% 8.27/3.09  Index Matching       : 0.00
% 8.27/3.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
