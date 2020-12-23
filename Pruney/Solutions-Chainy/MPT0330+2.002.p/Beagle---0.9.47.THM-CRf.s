%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:40 EST 2020

% Result     : Theorem 5.64s
% Output     : CNFRefutation 5.64s
% Verified   : 
% Statistics : Number of formulae       :   62 (  76 expanded)
%              Number of leaves         :   26 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   68 (  99 expanded)
%              Number of equality atoms :   18 (  25 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k1_enumset1 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( ( r1_tarski(A,k2_zfmisc_1(C,D))
          & r1_tarski(B,k2_zfmisc_1(E,F)) )
       => r1_tarski(k2_xboole_0(A,B),k2_zfmisc_1(k2_xboole_0(C,E),k2_xboole_0(D,F))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_53,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_30,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3569,plain,(
    ! [A_253,C_254,B_255] : k2_xboole_0(k2_zfmisc_1(A_253,C_254),k2_zfmisc_1(B_255,C_254)) = k2_zfmisc_1(k2_xboole_0(A_253,B_255),C_254) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4720,plain,(
    ! [A_316,A_317,B_318,C_319] :
      ( r1_tarski(A_316,k2_zfmisc_1(k2_xboole_0(A_317,B_318),C_319))
      | ~ r1_tarski(A_316,k2_zfmisc_1(B_318,C_319)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3569,c_4])).

tff(c_3430,plain,(
    ! [C_240,A_241,B_242] : k2_xboole_0(k2_zfmisc_1(C_240,A_241),k2_zfmisc_1(C_240,B_242)) = k2_zfmisc_1(C_240,k2_xboole_0(A_241,B_242)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4508,plain,(
    ! [A_302,C_303,A_304,B_305] :
      ( r1_tarski(A_302,k2_zfmisc_1(C_303,k2_xboole_0(A_304,B_305)))
      | ~ r1_tarski(A_302,k2_zfmisc_1(C_303,B_305)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3430,c_4])).

tff(c_14,plain,(
    ! [B_17,A_16] : k2_tarski(B_17,A_16) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_100,plain,(
    ! [A_34,B_35] : k3_tarski(k2_tarski(A_34,B_35)) = k2_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_154,plain,(
    ! [B_42,A_43] : k3_tarski(k2_tarski(B_42,A_43)) = k2_xboole_0(A_43,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_100])).

tff(c_18,plain,(
    ! [A_20,B_21] : k3_tarski(k2_tarski(A_20,B_21)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_160,plain,(
    ! [B_42,A_43] : k2_xboole_0(B_42,A_43) = k2_xboole_0(A_43,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_18])).

tff(c_24,plain,(
    ! [A_25,C_27,B_26] : k2_xboole_0(k2_zfmisc_1(A_25,C_27),k2_zfmisc_1(B_26,C_27)) = k2_zfmisc_1(k2_xboole_0(A_25,B_26),C_27) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_892,plain,(
    ! [C_89,A_90,B_91] : k2_xboole_0(k2_zfmisc_1(C_89,A_90),k2_zfmisc_1(C_89,B_91)) = k2_zfmisc_1(C_89,k2_xboole_0(A_90,B_91)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_934,plain,(
    ! [C_89,A_90,B_91] : r1_tarski(k2_zfmisc_1(C_89,A_90),k2_zfmisc_1(C_89,k2_xboole_0(A_90,B_91))) ),
    inference(superposition,[status(thm),theory(equality)],[c_892,c_10])).

tff(c_32,plain,(
    r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_235,plain,(
    ! [A_48,C_49,B_50] :
      ( r1_tarski(A_48,k2_xboole_0(C_49,B_50))
      | ~ r1_tarski(A_48,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_378,plain,(
    ! [A_68,C_69,B_70] :
      ( k3_xboole_0(A_68,k2_xboole_0(C_69,B_70)) = A_68
      | ~ r1_tarski(A_68,B_70) ) ),
    inference(resolution,[status(thm)],[c_235,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_274,plain,(
    ! [A_53,B_54,C_55] :
      ( r1_tarski(A_53,B_54)
      | ~ r1_tarski(A_53,k3_xboole_0(B_54,C_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_289,plain,(
    ! [A_53,A_1,B_2] :
      ( r1_tarski(A_53,A_1)
      | ~ r1_tarski(A_53,k3_xboole_0(B_2,A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_274])).

tff(c_978,plain,(
    ! [A_98,C_99,B_100,A_101] :
      ( r1_tarski(A_98,k2_xboole_0(C_99,B_100))
      | ~ r1_tarski(A_98,A_101)
      | ~ r1_tarski(A_101,B_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_289])).

tff(c_1129,plain,(
    ! [C_111,B_112] :
      ( r1_tarski('#skF_1',k2_xboole_0(C_111,B_112))
      | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),B_112) ) ),
    inference(resolution,[status(thm)],[c_32,c_978])).

tff(c_1277,plain,(
    ! [C_119,B_120] : r1_tarski('#skF_1',k2_xboole_0(C_119,k2_zfmisc_1('#skF_3',k2_xboole_0('#skF_4',B_120)))) ),
    inference(resolution,[status(thm)],[c_934,c_1129])).

tff(c_3290,plain,(
    ! [A_230,B_231] : r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0(A_230,'#skF_3'),k2_xboole_0('#skF_4',B_231))) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1277])).

tff(c_3307,plain,(
    ! [B_42,B_231] : r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3',B_42),k2_xboole_0('#skF_4',B_231))) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_3290])).

tff(c_787,plain,(
    ! [A_85,C_86,B_87] :
      ( r1_tarski(k2_xboole_0(A_85,C_86),B_87)
      | ~ r1_tarski(C_86,B_87)
      | ~ r1_tarski(A_85,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_28,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_2'),k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_810,plain,
    ( ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6')))
    | ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_787,c_28])).

tff(c_891,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_810])).

tff(c_3423,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3307,c_891])).

tff(c_3424,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_810])).

tff(c_4548,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_4508,c_3424])).

tff(c_4726,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_4720,c_4548])).

tff(c_4767,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_4726])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:40:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.64/2.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.64/2.12  
% 5.64/2.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.64/2.12  %$ r1_tarski > k1_enumset1 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.64/2.12  
% 5.64/2.12  %Foreground sorts:
% 5.64/2.12  
% 5.64/2.12  
% 5.64/2.12  %Background operators:
% 5.64/2.12  
% 5.64/2.12  
% 5.64/2.12  %Foreground operators:
% 5.64/2.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.64/2.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.64/2.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.64/2.12  tff('#skF_5', type, '#skF_5': $i).
% 5.64/2.12  tff('#skF_6', type, '#skF_6': $i).
% 5.64/2.12  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.64/2.12  tff('#skF_2', type, '#skF_2': $i).
% 5.64/2.12  tff('#skF_3', type, '#skF_3': $i).
% 5.64/2.12  tff('#skF_1', type, '#skF_1': $i).
% 5.64/2.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.64/2.12  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.64/2.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.64/2.12  tff('#skF_4', type, '#skF_4': $i).
% 5.64/2.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.64/2.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.64/2.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.64/2.12  
% 5.64/2.14  tff(f_70, negated_conjecture, ~(![A, B, C, D, E, F]: ((r1_tarski(A, k2_zfmisc_1(C, D)) & r1_tarski(B, k2_zfmisc_1(E, F))) => r1_tarski(k2_xboole_0(A, B), k2_zfmisc_1(k2_xboole_0(C, E), k2_xboole_0(D, F))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 5.64/2.14  tff(f_63, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 5.64/2.14  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 5.64/2.14  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.64/2.14  tff(f_53, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.64/2.14  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.64/2.14  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.64/2.14  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.64/2.14  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 5.64/2.14  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 5.64/2.14  tff(c_30, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.64/2.14  tff(c_3569, plain, (![A_253, C_254, B_255]: (k2_xboole_0(k2_zfmisc_1(A_253, C_254), k2_zfmisc_1(B_255, C_254))=k2_zfmisc_1(k2_xboole_0(A_253, B_255), C_254))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.64/2.14  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.64/2.14  tff(c_4720, plain, (![A_316, A_317, B_318, C_319]: (r1_tarski(A_316, k2_zfmisc_1(k2_xboole_0(A_317, B_318), C_319)) | ~r1_tarski(A_316, k2_zfmisc_1(B_318, C_319)))), inference(superposition, [status(thm), theory('equality')], [c_3569, c_4])).
% 5.64/2.14  tff(c_3430, plain, (![C_240, A_241, B_242]: (k2_xboole_0(k2_zfmisc_1(C_240, A_241), k2_zfmisc_1(C_240, B_242))=k2_zfmisc_1(C_240, k2_xboole_0(A_241, B_242)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.64/2.14  tff(c_4508, plain, (![A_302, C_303, A_304, B_305]: (r1_tarski(A_302, k2_zfmisc_1(C_303, k2_xboole_0(A_304, B_305))) | ~r1_tarski(A_302, k2_zfmisc_1(C_303, B_305)))), inference(superposition, [status(thm), theory('equality')], [c_3430, c_4])).
% 5.64/2.14  tff(c_14, plain, (![B_17, A_16]: (k2_tarski(B_17, A_16)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.64/2.14  tff(c_100, plain, (![A_34, B_35]: (k3_tarski(k2_tarski(A_34, B_35))=k2_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.64/2.14  tff(c_154, plain, (![B_42, A_43]: (k3_tarski(k2_tarski(B_42, A_43))=k2_xboole_0(A_43, B_42))), inference(superposition, [status(thm), theory('equality')], [c_14, c_100])).
% 5.64/2.14  tff(c_18, plain, (![A_20, B_21]: (k3_tarski(k2_tarski(A_20, B_21))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.64/2.14  tff(c_160, plain, (![B_42, A_43]: (k2_xboole_0(B_42, A_43)=k2_xboole_0(A_43, B_42))), inference(superposition, [status(thm), theory('equality')], [c_154, c_18])).
% 5.64/2.14  tff(c_24, plain, (![A_25, C_27, B_26]: (k2_xboole_0(k2_zfmisc_1(A_25, C_27), k2_zfmisc_1(B_26, C_27))=k2_zfmisc_1(k2_xboole_0(A_25, B_26), C_27))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.64/2.14  tff(c_892, plain, (![C_89, A_90, B_91]: (k2_xboole_0(k2_zfmisc_1(C_89, A_90), k2_zfmisc_1(C_89, B_91))=k2_zfmisc_1(C_89, k2_xboole_0(A_90, B_91)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.64/2.14  tff(c_10, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.64/2.14  tff(c_934, plain, (![C_89, A_90, B_91]: (r1_tarski(k2_zfmisc_1(C_89, A_90), k2_zfmisc_1(C_89, k2_xboole_0(A_90, B_91))))), inference(superposition, [status(thm), theory('equality')], [c_892, c_10])).
% 5.64/2.14  tff(c_32, plain, (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.64/2.14  tff(c_235, plain, (![A_48, C_49, B_50]: (r1_tarski(A_48, k2_xboole_0(C_49, B_50)) | ~r1_tarski(A_48, B_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.64/2.14  tff(c_8, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.64/2.14  tff(c_378, plain, (![A_68, C_69, B_70]: (k3_xboole_0(A_68, k2_xboole_0(C_69, B_70))=A_68 | ~r1_tarski(A_68, B_70))), inference(resolution, [status(thm)], [c_235, c_8])).
% 5.64/2.14  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.64/2.14  tff(c_274, plain, (![A_53, B_54, C_55]: (r1_tarski(A_53, B_54) | ~r1_tarski(A_53, k3_xboole_0(B_54, C_55)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.64/2.14  tff(c_289, plain, (![A_53, A_1, B_2]: (r1_tarski(A_53, A_1) | ~r1_tarski(A_53, k3_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_274])).
% 5.64/2.14  tff(c_978, plain, (![A_98, C_99, B_100, A_101]: (r1_tarski(A_98, k2_xboole_0(C_99, B_100)) | ~r1_tarski(A_98, A_101) | ~r1_tarski(A_101, B_100))), inference(superposition, [status(thm), theory('equality')], [c_378, c_289])).
% 5.64/2.14  tff(c_1129, plain, (![C_111, B_112]: (r1_tarski('#skF_1', k2_xboole_0(C_111, B_112)) | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), B_112))), inference(resolution, [status(thm)], [c_32, c_978])).
% 5.64/2.14  tff(c_1277, plain, (![C_119, B_120]: (r1_tarski('#skF_1', k2_xboole_0(C_119, k2_zfmisc_1('#skF_3', k2_xboole_0('#skF_4', B_120)))))), inference(resolution, [status(thm)], [c_934, c_1129])).
% 5.64/2.14  tff(c_3290, plain, (![A_230, B_231]: (r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0(A_230, '#skF_3'), k2_xboole_0('#skF_4', B_231))))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1277])).
% 5.64/2.14  tff(c_3307, plain, (![B_42, B_231]: (r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', B_42), k2_xboole_0('#skF_4', B_231))))), inference(superposition, [status(thm), theory('equality')], [c_160, c_3290])).
% 5.64/2.14  tff(c_787, plain, (![A_85, C_86, B_87]: (r1_tarski(k2_xboole_0(A_85, C_86), B_87) | ~r1_tarski(C_86, B_87) | ~r1_tarski(A_85, B_87))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.64/2.14  tff(c_28, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_2'), k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.64/2.14  tff(c_810, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6'))) | ~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(resolution, [status(thm)], [c_787, c_28])).
% 5.64/2.14  tff(c_891, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(splitLeft, [status(thm)], [c_810])).
% 5.64/2.14  tff(c_3423, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3307, c_891])).
% 5.64/2.14  tff(c_3424, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(splitRight, [status(thm)], [c_810])).
% 5.64/2.14  tff(c_4548, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_4508, c_3424])).
% 5.64/2.14  tff(c_4726, plain, (~r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_4720, c_4548])).
% 5.64/2.14  tff(c_4767, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_4726])).
% 5.64/2.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.64/2.14  
% 5.64/2.14  Inference rules
% 5.64/2.14  ----------------------
% 5.64/2.14  #Ref     : 0
% 5.64/2.14  #Sup     : 1202
% 5.64/2.14  #Fact    : 0
% 5.64/2.14  #Define  : 0
% 5.64/2.14  #Split   : 2
% 5.64/2.14  #Chain   : 0
% 5.64/2.14  #Close   : 0
% 5.64/2.14  
% 5.64/2.14  Ordering : KBO
% 5.64/2.14  
% 5.64/2.14  Simplification rules
% 5.64/2.14  ----------------------
% 5.64/2.14  #Subsume      : 74
% 5.64/2.14  #Demod        : 203
% 5.64/2.14  #Tautology    : 332
% 5.64/2.14  #SimpNegUnit  : 0
% 5.64/2.14  #BackRed      : 1
% 5.64/2.14  
% 5.64/2.14  #Partial instantiations: 0
% 5.64/2.14  #Strategies tried      : 1
% 5.64/2.14  
% 5.64/2.14  Timing (in seconds)
% 5.64/2.14  ----------------------
% 5.64/2.14  Preprocessing        : 0.30
% 5.64/2.14  Parsing              : 0.16
% 5.64/2.14  CNF conversion       : 0.02
% 5.64/2.14  Main loop            : 1.04
% 5.64/2.14  Inferencing          : 0.33
% 5.64/2.14  Reduction            : 0.41
% 5.64/2.14  Demodulation         : 0.33
% 5.64/2.14  BG Simplification    : 0.04
% 5.64/2.14  Subsumption          : 0.19
% 5.64/2.14  Abstraction          : 0.04
% 5.64/2.14  MUC search           : 0.00
% 5.64/2.14  Cooper               : 0.00
% 5.64/2.14  Total                : 1.37
% 5.64/2.14  Index Insertion      : 0.00
% 5.64/2.14  Index Deletion       : 0.00
% 5.64/2.14  Index Matching       : 0.00
% 5.64/2.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
