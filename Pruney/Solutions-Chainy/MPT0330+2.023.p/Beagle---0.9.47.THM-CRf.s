%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:43 EST 2020

% Result     : Theorem 11.03s
% Output     : CNFRefutation 11.03s
% Verified   : 
% Statistics : Number of formulae       :   51 (  72 expanded)
%              Number of leaves         :   19 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   53 (  95 expanded)
%              Number of equality atoms :   13 (  23 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_47,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( ( r1_tarski(A,k2_zfmisc_1(C,D))
          & r1_tarski(B,k2_zfmisc_1(E,F)) )
       => r1_tarski(k2_xboole_0(A,B),k2_zfmisc_1(k2_xboole_0(C,E),k2_xboole_0(D,F))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_12,plain,(
    ! [A_13,C_15,B_14] : k2_xboole_0(k2_zfmisc_1(A_13,C_15),k2_zfmisc_1(B_14,C_15)) = k2_zfmisc_1(k2_xboole_0(A_13,B_14),C_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_471,plain,(
    ! [C_52,A_53,B_54] : k2_xboole_0(k2_zfmisc_1(C_52,A_53),k2_zfmisc_1(C_52,B_54)) = k2_zfmisc_1(C_52,k2_xboole_0(A_53,B_54)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_13838,plain,(
    ! [C_324,B_325,A_326] : k2_xboole_0(k2_zfmisc_1(C_324,B_325),k2_zfmisc_1(C_324,A_326)) = k2_zfmisc_1(C_324,k2_xboole_0(A_326,B_325)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_471])).

tff(c_22,plain,(
    ! [B_18,A_19] : k2_xboole_0(B_18,A_19) = k2_xboole_0(A_19,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_37,plain,(
    ! [A_19,B_18] : r1_tarski(A_19,k2_xboole_0(B_18,A_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_8])).

tff(c_88,plain,(
    ! [A_24,C_25,B_26] :
      ( r1_tarski(A_24,C_25)
      | ~ r1_tarski(k2_xboole_0(A_24,B_26),C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_103,plain,(
    ! [A_24,B_18,B_26] : r1_tarski(A_24,k2_xboole_0(B_18,k2_xboole_0(A_24,B_26))) ),
    inference(resolution,[status(thm)],[c_37,c_88])).

tff(c_18,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_70,plain,(
    ! [A_22,B_23] :
      ( k2_xboole_0(A_22,B_23) = B_23
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_85,plain,(
    k2_xboole_0('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) = k2_zfmisc_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_18,c_70])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10872,plain,(
    ! [C_258] :
      ( r1_tarski('#skF_2',C_258)
      | ~ r1_tarski(k2_zfmisc_1('#skF_5','#skF_6'),C_258) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_4])).

tff(c_10904,plain,(
    ! [B_18,B_26] : r1_tarski('#skF_2',k2_xboole_0(B_18,k2_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'),B_26))) ),
    inference(resolution,[status(thm)],[c_103,c_10872])).

tff(c_18070,plain,(
    ! [B_413,A_414] : r1_tarski('#skF_2',k2_xboole_0(B_413,k2_zfmisc_1('#skF_5',k2_xboole_0(A_414,'#skF_6')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_13838,c_10904])).

tff(c_18115,plain,(
    ! [A_13,A_414] : r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0(A_13,'#skF_5'),k2_xboole_0(A_414,'#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_18070])).

tff(c_14,plain,(
    ! [C_15,A_13,B_14] : k2_xboole_0(k2_zfmisc_1(C_15,A_13),k2_zfmisc_1(C_15,B_14)) = k2_zfmisc_1(C_15,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_86,plain,(
    k2_xboole_0('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_70])).

tff(c_105,plain,(
    ! [A_27,B_28,B_29] : r1_tarski(A_27,k2_xboole_0(k2_xboole_0(A_27,B_28),B_29)) ),
    inference(resolution,[status(thm)],[c_8,c_88])).

tff(c_2977,plain,(
    ! [A_107,B_108,B_109,B_110] : r1_tarski(A_107,k2_xboole_0(k2_xboole_0(k2_xboole_0(A_107,B_108),B_109),B_110)) ),
    inference(resolution,[status(thm)],[c_105,c_4])).

tff(c_4088,plain,(
    ! [B_132,B_133] : r1_tarski('#skF_1',k2_xboole_0(k2_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),B_132),B_133)) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_2977])).

tff(c_7948,plain,(
    ! [B_206,B_207] : r1_tarski('#skF_1',k2_xboole_0(k2_zfmisc_1(k2_xboole_0('#skF_3',B_206),'#skF_4'),B_207)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_4088])).

tff(c_8001,plain,(
    ! [B_206,B_14] : r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3',B_206),k2_xboole_0('#skF_4',B_14))) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_7948])).

tff(c_184,plain,(
    ! [A_36,C_37,B_38] :
      ( r1_tarski(k2_xboole_0(A_36,C_37),B_38)
      | ~ r1_tarski(C_37,B_38)
      | ~ r1_tarski(A_36,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_2'),k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_200,plain,
    ( ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6')))
    | ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_184,c_16])).

tff(c_567,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_200])).

tff(c_10578,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8001,c_567])).

tff(c_10579,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_200])).

tff(c_22373,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18115,c_10579])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:04:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.03/4.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.03/4.19  
% 11.03/4.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.03/4.19  %$ r1_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.03/4.19  
% 11.03/4.19  %Foreground sorts:
% 11.03/4.19  
% 11.03/4.19  
% 11.03/4.19  %Background operators:
% 11.03/4.19  
% 11.03/4.19  
% 11.03/4.19  %Foreground operators:
% 11.03/4.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.03/4.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.03/4.19  tff('#skF_5', type, '#skF_5': $i).
% 11.03/4.19  tff('#skF_6', type, '#skF_6': $i).
% 11.03/4.19  tff('#skF_2', type, '#skF_2': $i).
% 11.03/4.19  tff('#skF_3', type, '#skF_3': $i).
% 11.03/4.19  tff('#skF_1', type, '#skF_1': $i).
% 11.03/4.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.03/4.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.03/4.19  tff('#skF_4', type, '#skF_4': $i).
% 11.03/4.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.03/4.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.03/4.19  
% 11.03/4.21  tff(f_47, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 11.03/4.21  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 11.03/4.21  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 11.03/4.21  tff(f_31, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 11.03/4.21  tff(f_54, negated_conjecture, ~(![A, B, C, D, E, F]: ((r1_tarski(A, k2_zfmisc_1(C, D)) & r1_tarski(B, k2_zfmisc_1(E, F))) => r1_tarski(k2_xboole_0(A, B), k2_zfmisc_1(k2_xboole_0(C, E), k2_xboole_0(D, F))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 11.03/4.21  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 11.03/4.21  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 11.03/4.21  tff(c_12, plain, (![A_13, C_15, B_14]: (k2_xboole_0(k2_zfmisc_1(A_13, C_15), k2_zfmisc_1(B_14, C_15))=k2_zfmisc_1(k2_xboole_0(A_13, B_14), C_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.03/4.21  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.03/4.21  tff(c_471, plain, (![C_52, A_53, B_54]: (k2_xboole_0(k2_zfmisc_1(C_52, A_53), k2_zfmisc_1(C_52, B_54))=k2_zfmisc_1(C_52, k2_xboole_0(A_53, B_54)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.03/4.21  tff(c_13838, plain, (![C_324, B_325, A_326]: (k2_xboole_0(k2_zfmisc_1(C_324, B_325), k2_zfmisc_1(C_324, A_326))=k2_zfmisc_1(C_324, k2_xboole_0(A_326, B_325)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_471])).
% 11.03/4.21  tff(c_22, plain, (![B_18, A_19]: (k2_xboole_0(B_18, A_19)=k2_xboole_0(A_19, B_18))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.03/4.21  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.03/4.21  tff(c_37, plain, (![A_19, B_18]: (r1_tarski(A_19, k2_xboole_0(B_18, A_19)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_8])).
% 11.03/4.21  tff(c_88, plain, (![A_24, C_25, B_26]: (r1_tarski(A_24, C_25) | ~r1_tarski(k2_xboole_0(A_24, B_26), C_25))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.03/4.21  tff(c_103, plain, (![A_24, B_18, B_26]: (r1_tarski(A_24, k2_xboole_0(B_18, k2_xboole_0(A_24, B_26))))), inference(resolution, [status(thm)], [c_37, c_88])).
% 11.03/4.21  tff(c_18, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.03/4.21  tff(c_70, plain, (![A_22, B_23]: (k2_xboole_0(A_22, B_23)=B_23 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.03/4.21  tff(c_85, plain, (k2_xboole_0('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))=k2_zfmisc_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_18, c_70])).
% 11.03/4.21  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.03/4.21  tff(c_10872, plain, (![C_258]: (r1_tarski('#skF_2', C_258) | ~r1_tarski(k2_zfmisc_1('#skF_5', '#skF_6'), C_258))), inference(superposition, [status(thm), theory('equality')], [c_85, c_4])).
% 11.03/4.21  tff(c_10904, plain, (![B_18, B_26]: (r1_tarski('#skF_2', k2_xboole_0(B_18, k2_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'), B_26))))), inference(resolution, [status(thm)], [c_103, c_10872])).
% 11.03/4.21  tff(c_18070, plain, (![B_413, A_414]: (r1_tarski('#skF_2', k2_xboole_0(B_413, k2_zfmisc_1('#skF_5', k2_xboole_0(A_414, '#skF_6')))))), inference(superposition, [status(thm), theory('equality')], [c_13838, c_10904])).
% 11.03/4.21  tff(c_18115, plain, (![A_13, A_414]: (r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0(A_13, '#skF_5'), k2_xboole_0(A_414, '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_12, c_18070])).
% 11.03/4.21  tff(c_14, plain, (![C_15, A_13, B_14]: (k2_xboole_0(k2_zfmisc_1(C_15, A_13), k2_zfmisc_1(C_15, B_14))=k2_zfmisc_1(C_15, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.03/4.21  tff(c_20, plain, (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.03/4.21  tff(c_86, plain, (k2_xboole_0('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_20, c_70])).
% 11.03/4.21  tff(c_105, plain, (![A_27, B_28, B_29]: (r1_tarski(A_27, k2_xboole_0(k2_xboole_0(A_27, B_28), B_29)))), inference(resolution, [status(thm)], [c_8, c_88])).
% 11.03/4.21  tff(c_2977, plain, (![A_107, B_108, B_109, B_110]: (r1_tarski(A_107, k2_xboole_0(k2_xboole_0(k2_xboole_0(A_107, B_108), B_109), B_110)))), inference(resolution, [status(thm)], [c_105, c_4])).
% 11.03/4.21  tff(c_4088, plain, (![B_132, B_133]: (r1_tarski('#skF_1', k2_xboole_0(k2_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), B_132), B_133)))), inference(superposition, [status(thm), theory('equality')], [c_86, c_2977])).
% 11.03/4.21  tff(c_7948, plain, (![B_206, B_207]: (r1_tarski('#skF_1', k2_xboole_0(k2_zfmisc_1(k2_xboole_0('#skF_3', B_206), '#skF_4'), B_207)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_4088])).
% 11.03/4.21  tff(c_8001, plain, (![B_206, B_14]: (r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', B_206), k2_xboole_0('#skF_4', B_14))))), inference(superposition, [status(thm), theory('equality')], [c_14, c_7948])).
% 11.03/4.21  tff(c_184, plain, (![A_36, C_37, B_38]: (r1_tarski(k2_xboole_0(A_36, C_37), B_38) | ~r1_tarski(C_37, B_38) | ~r1_tarski(A_36, B_38))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.03/4.21  tff(c_16, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_2'), k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.03/4.21  tff(c_200, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6'))) | ~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(resolution, [status(thm)], [c_184, c_16])).
% 11.03/4.21  tff(c_567, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(splitLeft, [status(thm)], [c_200])).
% 11.03/4.21  tff(c_10578, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8001, c_567])).
% 11.03/4.21  tff(c_10579, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(splitRight, [status(thm)], [c_200])).
% 11.03/4.21  tff(c_22373, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18115, c_10579])).
% 11.03/4.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.03/4.21  
% 11.03/4.21  Inference rules
% 11.03/4.21  ----------------------
% 11.03/4.21  #Ref     : 0
% 11.03/4.21  #Sup     : 5333
% 11.03/4.21  #Fact    : 0
% 11.03/4.21  #Define  : 0
% 11.03/4.21  #Split   : 1
% 11.03/4.21  #Chain   : 0
% 11.03/4.21  #Close   : 0
% 11.03/4.21  
% 11.03/4.21  Ordering : KBO
% 11.03/4.21  
% 11.03/4.21  Simplification rules
% 11.03/4.21  ----------------------
% 11.03/4.21  #Subsume      : 187
% 11.03/4.21  #Demod        : 3225
% 11.03/4.21  #Tautology    : 2775
% 11.03/4.21  #SimpNegUnit  : 0
% 11.03/4.21  #BackRed      : 2
% 11.03/4.21  
% 11.03/4.21  #Partial instantiations: 0
% 11.03/4.21  #Strategies tried      : 1
% 11.03/4.21  
% 11.03/4.21  Timing (in seconds)
% 11.03/4.21  ----------------------
% 11.03/4.21  Preprocessing        : 0.30
% 11.03/4.21  Parsing              : 0.17
% 11.03/4.21  CNF conversion       : 0.02
% 11.03/4.21  Main loop            : 3.08
% 11.03/4.21  Inferencing          : 0.63
% 11.03/4.21  Reduction            : 1.63
% 11.03/4.21  Demodulation         : 1.45
% 11.03/4.21  BG Simplification    : 0.08
% 11.03/4.21  Subsumption          : 0.58
% 11.03/4.21  Abstraction          : 0.10
% 11.03/4.21  MUC search           : 0.00
% 11.03/4.21  Cooper               : 0.00
% 11.03/4.21  Total                : 3.41
% 11.03/4.21  Index Insertion      : 0.00
% 11.03/4.21  Index Deletion       : 0.00
% 11.03/4.21  Index Matching       : 0.00
% 11.03/4.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
