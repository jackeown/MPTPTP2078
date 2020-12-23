%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:44 EST 2020

% Result     : Theorem 4.86s
% Output     : CNFRefutation 5.20s
% Verified   : 
% Statistics : Number of formulae       :   46 (  62 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   54 (  88 expanded)
%              Number of equality atoms :    5 (  12 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( ( r1_tarski(A,k2_zfmisc_1(C,D))
          & r1_tarski(B,k2_zfmisc_1(E,F)) )
       => r1_tarski(k2_xboole_0(A,B),k2_zfmisc_1(k2_xboole_0(C,E),k2_xboole_0(D,F))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_22,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_132,plain,(
    ! [C_52,A_53,B_54] : k2_xboole_0(k2_zfmisc_1(C_52,A_53),k2_zfmisc_1(C_52,B_54)) = k2_zfmisc_1(C_52,k2_xboole_0(A_53,B_54)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,k2_xboole_0(C_3,B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2933,plain,(
    ! [A_265,C_266,A_267,B_268] :
      ( r1_tarski(A_265,k2_zfmisc_1(C_266,k2_xboole_0(A_267,B_268)))
      | ~ r1_tarski(A_265,k2_zfmisc_1(C_266,B_268)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_2])).

tff(c_306,plain,(
    ! [A_76,C_77,B_78] : k2_xboole_0(k2_zfmisc_1(A_76,C_77),k2_zfmisc_1(B_78,C_77)) = k2_zfmisc_1(k2_xboole_0(A_76,B_78),C_77) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2773,plain,(
    ! [A_249,A_250,B_251,C_252] :
      ( r1_tarski(A_249,k2_zfmisc_1(k2_xboole_0(A_250,B_251),C_252))
      | ~ r1_tarski(A_249,k2_zfmisc_1(B_251,C_252)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_2])).

tff(c_16,plain,(
    ! [A_17,C_19,B_18] : k2_xboole_0(k2_zfmisc_1(A_17,C_19),k2_zfmisc_1(B_18,C_19)) = k2_zfmisc_1(k2_xboole_0(A_17,B_18),C_19) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [A_7,B_8] : r1_tarski(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_149,plain,(
    ! [C_52,A_53,B_54] : r1_tarski(k2_zfmisc_1(C_52,A_53),k2_zfmisc_1(C_52,k2_xboole_0(A_53,B_54))) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_6])).

tff(c_24,plain,(
    r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_36,plain,(
    ! [A_27,C_28,B_29] :
      ( r1_tarski(A_27,C_28)
      | ~ r1_tarski(B_29,C_28)
      | ~ r1_tarski(A_27,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_49,plain,(
    ! [A_30,A_31,B_32] :
      ( r1_tarski(A_30,k2_xboole_0(A_31,B_32))
      | ~ r1_tarski(A_30,A_31) ) ),
    inference(resolution,[status(thm)],[c_6,c_36])).

tff(c_4,plain,(
    ! [A_4,C_6,B_5] :
      ( r1_tarski(A_4,C_6)
      | ~ r1_tarski(B_5,C_6)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2013,plain,(
    ! [A_201,A_202,B_203,A_204] :
      ( r1_tarski(A_201,k2_xboole_0(A_202,B_203))
      | ~ r1_tarski(A_201,A_204)
      | ~ r1_tarski(A_204,A_202) ) ),
    inference(resolution,[status(thm)],[c_49,c_4])).

tff(c_2297,plain,(
    ! [A_215,B_216] :
      ( r1_tarski('#skF_1',k2_xboole_0(A_215,B_216))
      | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),A_215) ) ),
    inference(resolution,[status(thm)],[c_24,c_2013])).

tff(c_2460,plain,(
    ! [B_225,B_226] : r1_tarski('#skF_1',k2_xboole_0(k2_zfmisc_1('#skF_3',k2_xboole_0('#skF_4',B_225)),B_226)) ),
    inference(resolution,[status(thm)],[c_149,c_2297])).

tff(c_2474,plain,(
    ! [B_18,B_225] : r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3',B_18),k2_xboole_0('#skF_4',B_225))) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2460])).

tff(c_69,plain,(
    ! [A_41,C_42,B_43] :
      ( r1_tarski(k2_xboole_0(A_41,C_42),B_43)
      | ~ r1_tarski(C_42,B_43)
      | ~ r1_tarski(A_41,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_2'),k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_75,plain,
    ( ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6')))
    | ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_69,c_20])).

tff(c_410,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_2539,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2474,c_410])).

tff(c_2540,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_2806,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1('#skF_5',k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_2773,c_2540])).

tff(c_2939,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_2933,c_2806])).

tff(c_2976,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2939])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:20:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.86/1.97  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.86/1.98  
% 4.86/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.86/1.98  %$ r1_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.86/1.98  
% 4.86/1.98  %Foreground sorts:
% 4.86/1.98  
% 4.86/1.98  
% 4.86/1.98  %Background operators:
% 4.86/1.98  
% 4.86/1.98  
% 4.86/1.98  %Foreground operators:
% 4.86/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.86/1.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.86/1.98  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.86/1.98  tff('#skF_5', type, '#skF_5': $i).
% 4.86/1.98  tff('#skF_6', type, '#skF_6': $i).
% 4.86/1.98  tff('#skF_2', type, '#skF_2': $i).
% 4.86/1.98  tff('#skF_3', type, '#skF_3': $i).
% 4.86/1.98  tff('#skF_1', type, '#skF_1': $i).
% 4.86/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.86/1.98  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.86/1.98  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.86/1.98  tff('#skF_4', type, '#skF_4': $i).
% 4.86/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.86/1.98  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.86/1.98  
% 5.20/1.99  tff(f_62, negated_conjecture, ~(![A, B, C, D, E, F]: ((r1_tarski(A, k2_zfmisc_1(C, D)) & r1_tarski(B, k2_zfmisc_1(E, F))) => r1_tarski(k2_xboole_0(A, B), k2_zfmisc_1(k2_xboole_0(C, E), k2_xboole_0(D, F))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 5.20/1.99  tff(f_55, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 5.20/1.99  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 5.20/1.99  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.20/1.99  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.20/1.99  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 5.20/1.99  tff(c_22, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.20/1.99  tff(c_132, plain, (![C_52, A_53, B_54]: (k2_xboole_0(k2_zfmisc_1(C_52, A_53), k2_zfmisc_1(C_52, B_54))=k2_zfmisc_1(C_52, k2_xboole_0(A_53, B_54)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.20/1.99  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, k2_xboole_0(C_3, B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.20/1.99  tff(c_2933, plain, (![A_265, C_266, A_267, B_268]: (r1_tarski(A_265, k2_zfmisc_1(C_266, k2_xboole_0(A_267, B_268))) | ~r1_tarski(A_265, k2_zfmisc_1(C_266, B_268)))), inference(superposition, [status(thm), theory('equality')], [c_132, c_2])).
% 5.20/1.99  tff(c_306, plain, (![A_76, C_77, B_78]: (k2_xboole_0(k2_zfmisc_1(A_76, C_77), k2_zfmisc_1(B_78, C_77))=k2_zfmisc_1(k2_xboole_0(A_76, B_78), C_77))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.20/1.99  tff(c_2773, plain, (![A_249, A_250, B_251, C_252]: (r1_tarski(A_249, k2_zfmisc_1(k2_xboole_0(A_250, B_251), C_252)) | ~r1_tarski(A_249, k2_zfmisc_1(B_251, C_252)))), inference(superposition, [status(thm), theory('equality')], [c_306, c_2])).
% 5.20/1.99  tff(c_16, plain, (![A_17, C_19, B_18]: (k2_xboole_0(k2_zfmisc_1(A_17, C_19), k2_zfmisc_1(B_18, C_19))=k2_zfmisc_1(k2_xboole_0(A_17, B_18), C_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.20/1.99  tff(c_6, plain, (![A_7, B_8]: (r1_tarski(A_7, k2_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.20/1.99  tff(c_149, plain, (![C_52, A_53, B_54]: (r1_tarski(k2_zfmisc_1(C_52, A_53), k2_zfmisc_1(C_52, k2_xboole_0(A_53, B_54))))), inference(superposition, [status(thm), theory('equality')], [c_132, c_6])).
% 5.20/1.99  tff(c_24, plain, (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.20/1.99  tff(c_36, plain, (![A_27, C_28, B_29]: (r1_tarski(A_27, C_28) | ~r1_tarski(B_29, C_28) | ~r1_tarski(A_27, B_29))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.20/1.99  tff(c_49, plain, (![A_30, A_31, B_32]: (r1_tarski(A_30, k2_xboole_0(A_31, B_32)) | ~r1_tarski(A_30, A_31))), inference(resolution, [status(thm)], [c_6, c_36])).
% 5.20/1.99  tff(c_4, plain, (![A_4, C_6, B_5]: (r1_tarski(A_4, C_6) | ~r1_tarski(B_5, C_6) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.20/1.99  tff(c_2013, plain, (![A_201, A_202, B_203, A_204]: (r1_tarski(A_201, k2_xboole_0(A_202, B_203)) | ~r1_tarski(A_201, A_204) | ~r1_tarski(A_204, A_202))), inference(resolution, [status(thm)], [c_49, c_4])).
% 5.20/1.99  tff(c_2297, plain, (![A_215, B_216]: (r1_tarski('#skF_1', k2_xboole_0(A_215, B_216)) | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), A_215))), inference(resolution, [status(thm)], [c_24, c_2013])).
% 5.20/1.99  tff(c_2460, plain, (![B_225, B_226]: (r1_tarski('#skF_1', k2_xboole_0(k2_zfmisc_1('#skF_3', k2_xboole_0('#skF_4', B_225)), B_226)))), inference(resolution, [status(thm)], [c_149, c_2297])).
% 5.20/1.99  tff(c_2474, plain, (![B_18, B_225]: (r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', B_18), k2_xboole_0('#skF_4', B_225))))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2460])).
% 5.20/1.99  tff(c_69, plain, (![A_41, C_42, B_43]: (r1_tarski(k2_xboole_0(A_41, C_42), B_43) | ~r1_tarski(C_42, B_43) | ~r1_tarski(A_41, B_43))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.20/1.99  tff(c_20, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_2'), k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.20/1.99  tff(c_75, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6'))) | ~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(resolution, [status(thm)], [c_69, c_20])).
% 5.20/1.99  tff(c_410, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(splitLeft, [status(thm)], [c_75])).
% 5.20/1.99  tff(c_2539, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2474, c_410])).
% 5.20/1.99  tff(c_2540, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(splitRight, [status(thm)], [c_75])).
% 5.20/1.99  tff(c_2806, plain, (~r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', k2_xboole_0('#skF_4', '#skF_6')))), inference(resolution, [status(thm)], [c_2773, c_2540])).
% 5.20/1.99  tff(c_2939, plain, (~r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_2933, c_2806])).
% 5.20/1.99  tff(c_2976, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_2939])).
% 5.20/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.20/1.99  
% 5.20/1.99  Inference rules
% 5.20/1.99  ----------------------
% 5.20/1.99  #Ref     : 0
% 5.20/1.99  #Sup     : 810
% 5.20/1.99  #Fact    : 0
% 5.20/1.99  #Define  : 0
% 5.20/1.99  #Split   : 3
% 5.20/1.99  #Chain   : 0
% 5.20/1.99  #Close   : 0
% 5.20/1.99  
% 5.20/1.99  Ordering : KBO
% 5.20/1.99  
% 5.20/1.99  Simplification rules
% 5.20/1.99  ----------------------
% 5.20/1.99  #Subsume      : 90
% 5.20/1.99  #Demod        : 65
% 5.20/1.99  #Tautology    : 77
% 5.20/1.99  #SimpNegUnit  : 16
% 5.20/1.99  #BackRed      : 1
% 5.20/1.99  
% 5.20/1.99  #Partial instantiations: 0
% 5.20/1.99  #Strategies tried      : 1
% 5.20/1.99  
% 5.20/1.99  Timing (in seconds)
% 5.20/2.00  ----------------------
% 5.20/2.00  Preprocessing        : 0.29
% 5.20/2.00  Parsing              : 0.17
% 5.20/2.00  CNF conversion       : 0.02
% 5.20/2.00  Main loop            : 0.88
% 5.20/2.00  Inferencing          : 0.29
% 5.20/2.00  Reduction            : 0.28
% 5.20/2.00  Demodulation         : 0.21
% 5.20/2.00  BG Simplification    : 0.03
% 5.20/2.00  Subsumption          : 0.21
% 5.20/2.00  Abstraction          : 0.03
% 5.20/2.00  MUC search           : 0.00
% 5.20/2.00  Cooper               : 0.00
% 5.20/2.00  Total                : 1.21
% 5.20/2.00  Index Insertion      : 0.00
% 5.20/2.00  Index Deletion       : 0.00
% 5.20/2.00  Index Matching       : 0.00
% 5.20/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
