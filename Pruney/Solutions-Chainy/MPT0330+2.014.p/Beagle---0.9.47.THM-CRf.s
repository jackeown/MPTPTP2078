%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:41 EST 2020

% Result     : Theorem 9.45s
% Output     : CNFRefutation 9.64s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 198 expanded)
%              Number of leaves         :   23 (  79 expanded)
%              Depth                    :   12
%              Number of atoms          :   72 ( 275 expanded)
%              Number of equality atoms :   22 ( 112 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( ( r1_tarski(A,k2_zfmisc_1(C,D))
          & r1_tarski(B,k2_zfmisc_1(E,F)) )
       => r1_tarski(k2_xboole_0(A,B),k2_zfmisc_1(k2_xboole_0(C,E),k2_xboole_0(D,F))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).

tff(c_936,plain,(
    ! [C_63,A_64,B_65] : k2_xboole_0(k2_zfmisc_1(C_63,A_64),k2_zfmisc_1(C_63,B_65)) = k2_zfmisc_1(C_63,k2_xboole_0(A_64,B_65)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_989,plain,(
    ! [C_63,B_65,A_64] : k2_xboole_0(k2_zfmisc_1(C_63,B_65),k2_zfmisc_1(C_63,A_64)) = k2_zfmisc_1(C_63,k2_xboole_0(A_64,B_65)) ),
    inference(superposition,[status(thm),theory(equality)],[c_936,c_2])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,(
    r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_34,plain,(
    ! [B_26,A_27] : k2_xboole_0(B_26,A_27) = k2_xboole_0(A_27,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_103,plain,(
    ! [B_31,A_32] : r1_tarski(B_31,k2_xboole_0(A_32,B_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_14])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_116,plain,(
    ! [B_31,A_32] : k2_xboole_0(B_31,k2_xboole_0(A_32,B_31)) = k2_xboole_0(A_32,B_31) ),
    inference(resolution,[status(thm)],[c_103,c_10])).

tff(c_73,plain,(
    ! [A_28,B_29] :
      ( k2_xboole_0(A_28,B_29) = B_29
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_158,plain,(
    ! [A_39,B_40] : k2_xboole_0(A_39,k2_xboole_0(A_39,B_40)) = k2_xboole_0(A_39,B_40) ),
    inference(resolution,[status(thm)],[c_14,c_73])).

tff(c_182,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k2_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_158])).

tff(c_87,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = k2_xboole_0(A_11,B_12) ),
    inference(resolution,[status(thm)],[c_14,c_73])).

tff(c_209,plain,(
    ! [A_41,C_42,B_43] :
      ( r1_tarski(k2_xboole_0(A_41,C_42),k2_xboole_0(B_43,C_42))
      | ~ r1_tarski(A_41,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8006,plain,(
    ! [A_163,C_164,B_165] :
      ( k2_xboole_0(k2_xboole_0(A_163,C_164),k2_xboole_0(B_165,C_164)) = k2_xboole_0(B_165,C_164)
      | ~ r1_tarski(A_163,B_165) ) ),
    inference(resolution,[status(thm)],[c_209,c_10])).

tff(c_8377,plain,(
    ! [A_163,A_11,B_12] :
      ( k2_xboole_0(k2_xboole_0(A_163,k2_xboole_0(A_11,B_12)),k2_xboole_0(A_11,B_12)) = k2_xboole_0(A_11,k2_xboole_0(A_11,B_12))
      | ~ r1_tarski(A_163,A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_8006])).

tff(c_8503,plain,(
    ! [A_166,A_167,B_168] :
      ( k2_xboole_0(A_166,k2_xboole_0(A_167,B_168)) = k2_xboole_0(A_167,B_168)
      | ~ r1_tarski(A_166,A_167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_87,c_2,c_8377])).

tff(c_8856,plain,(
    ! [A_166,A_1,B_2] :
      ( k2_xboole_0(A_166,k2_xboole_0(A_1,B_2)) = k2_xboole_0(A_1,k2_xboole_0(B_2,A_1))
      | ~ r1_tarski(A_166,A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_8503])).

tff(c_11399,plain,(
    ! [A_197,A_198,B_199] :
      ( k2_xboole_0(A_197,k2_xboole_0(A_198,B_199)) = k2_xboole_0(B_199,A_198)
      | ~ r1_tarski(A_197,A_198) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_8856])).

tff(c_8751,plain,(
    ! [A_166,A_167,B_168] :
      ( r1_tarski(A_166,k2_xboole_0(A_167,B_168))
      | ~ r1_tarski(A_166,A_167) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8503,c_14])).

tff(c_13483,plain,(
    ! [A_213,B_214,A_215,A_216] :
      ( r1_tarski(A_213,k2_xboole_0(B_214,A_215))
      | ~ r1_tarski(A_213,A_216)
      | ~ r1_tarski(A_216,A_215) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11399,c_8751])).

tff(c_14829,plain,(
    ! [B_233,A_234] :
      ( r1_tarski('#skF_1',k2_xboole_0(B_233,A_234))
      | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),A_234) ) ),
    inference(resolution,[status(thm)],[c_30,c_13483])).

tff(c_14886,plain,(
    ! [B_235] : r1_tarski('#skF_1',k2_xboole_0(B_235,k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_8,c_14829])).

tff(c_14926,plain,(
    ! [B_65] : r1_tarski('#skF_1',k2_zfmisc_1('#skF_3',k2_xboole_0('#skF_4',B_65))) ),
    inference(superposition,[status(thm),theory(equality)],[c_989,c_14886])).

tff(c_24,plain,(
    ! [C_22,A_20,B_21] : k2_xboole_0(k2_zfmisc_1(C_22,A_20),k2_zfmisc_1(C_22,B_21)) = k2_zfmisc_1(C_22,k2_xboole_0(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_28,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_15655,plain,(
    ! [B_245,A_246] :
      ( r1_tarski('#skF_2',k2_xboole_0(B_245,A_246))
      | ~ r1_tarski(k2_zfmisc_1('#skF_5','#skF_6'),A_246) ) ),
    inference(resolution,[status(thm)],[c_28,c_13483])).

tff(c_15716,plain,(
    ! [B_247] : r1_tarski('#skF_2',k2_xboole_0(B_247,k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_8,c_15655])).

tff(c_15772,plain,(
    ! [A_20] : r1_tarski('#skF_2',k2_zfmisc_1('#skF_5',k2_xboole_0(A_20,'#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_15716])).

tff(c_22,plain,(
    ! [A_20,C_22,B_21] : k2_xboole_0(k2_zfmisc_1(A_20,C_22),k2_zfmisc_1(B_21,C_22)) = k2_zfmisc_1(k2_xboole_0(A_20,B_21),C_22) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1666,plain,(
    ! [A_72,C_73,B_74,D_75] :
      ( r1_tarski(k2_xboole_0(A_72,C_73),k2_xboole_0(B_74,D_75))
      | ~ r1_tarski(C_73,D_75)
      | ~ r1_tarski(A_72,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16319,plain,(
    ! [A_258,C_255,C_259,A_256,B_257] :
      ( r1_tarski(k2_xboole_0(A_256,C_259),k2_zfmisc_1(k2_xboole_0(A_258,B_257),C_255))
      | ~ r1_tarski(C_259,k2_zfmisc_1(B_257,C_255))
      | ~ r1_tarski(A_256,k2_zfmisc_1(A_258,C_255)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1666])).

tff(c_26,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_2'),k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16588,plain,
    ( ~ r1_tarski('#skF_2',k2_zfmisc_1('#skF_5',k2_xboole_0('#skF_4','#skF_6')))
    | ~ r1_tarski('#skF_1',k2_zfmisc_1('#skF_3',k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_16319,c_26])).

tff(c_16673,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1('#skF_3',k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15772,c_16588])).

tff(c_17276,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14926,c_16673])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:54:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.45/3.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.45/3.78  
% 9.45/3.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.45/3.78  %$ r1_tarski > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.45/3.78  
% 9.45/3.78  %Foreground sorts:
% 9.45/3.78  
% 9.45/3.78  
% 9.45/3.78  %Background operators:
% 9.45/3.78  
% 9.45/3.78  
% 9.45/3.78  %Foreground operators:
% 9.45/3.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.45/3.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.45/3.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.45/3.78  tff('#skF_5', type, '#skF_5': $i).
% 9.45/3.78  tff('#skF_6', type, '#skF_6': $i).
% 9.45/3.78  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.45/3.78  tff('#skF_2', type, '#skF_2': $i).
% 9.45/3.78  tff('#skF_3', type, '#skF_3': $i).
% 9.45/3.78  tff('#skF_1', type, '#skF_1': $i).
% 9.45/3.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.45/3.78  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.45/3.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.45/3.78  tff('#skF_4', type, '#skF_4': $i).
% 9.45/3.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.45/3.78  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.45/3.78  
% 9.64/3.80  tff(f_57, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 9.64/3.80  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 9.64/3.80  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.64/3.80  tff(f_64, negated_conjecture, ~(![A, B, C, D, E, F]: ((r1_tarski(A, k2_zfmisc_1(C, D)) & r1_tarski(B, k2_zfmisc_1(E, F))) => r1_tarski(k2_xboole_0(A, B), k2_zfmisc_1(k2_xboole_0(C, E), k2_xboole_0(D, F))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 9.64/3.80  tff(f_45, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 9.64/3.80  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 9.64/3.80  tff(f_49, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_xboole_1)).
% 9.64/3.80  tff(f_43, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_xboole_1)).
% 9.64/3.80  tff(c_936, plain, (![C_63, A_64, B_65]: (k2_xboole_0(k2_zfmisc_1(C_63, A_64), k2_zfmisc_1(C_63, B_65))=k2_zfmisc_1(C_63, k2_xboole_0(A_64, B_65)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.64/3.80  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.64/3.80  tff(c_989, plain, (![C_63, B_65, A_64]: (k2_xboole_0(k2_zfmisc_1(C_63, B_65), k2_zfmisc_1(C_63, A_64))=k2_zfmisc_1(C_63, k2_xboole_0(A_64, B_65)))), inference(superposition, [status(thm), theory('equality')], [c_936, c_2])).
% 9.64/3.80  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.64/3.80  tff(c_30, plain, (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.64/3.80  tff(c_34, plain, (![B_26, A_27]: (k2_xboole_0(B_26, A_27)=k2_xboole_0(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.64/3.80  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.64/3.80  tff(c_103, plain, (![B_31, A_32]: (r1_tarski(B_31, k2_xboole_0(A_32, B_31)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_14])).
% 9.64/3.80  tff(c_10, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.64/3.80  tff(c_116, plain, (![B_31, A_32]: (k2_xboole_0(B_31, k2_xboole_0(A_32, B_31))=k2_xboole_0(A_32, B_31))), inference(resolution, [status(thm)], [c_103, c_10])).
% 9.64/3.80  tff(c_73, plain, (![A_28, B_29]: (k2_xboole_0(A_28, B_29)=B_29 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.64/3.80  tff(c_158, plain, (![A_39, B_40]: (k2_xboole_0(A_39, k2_xboole_0(A_39, B_40))=k2_xboole_0(A_39, B_40))), inference(resolution, [status(thm)], [c_14, c_73])).
% 9.64/3.80  tff(c_182, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k2_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_158])).
% 9.64/3.80  tff(c_87, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k2_xboole_0(A_11, B_12))=k2_xboole_0(A_11, B_12))), inference(resolution, [status(thm)], [c_14, c_73])).
% 9.64/3.80  tff(c_209, plain, (![A_41, C_42, B_43]: (r1_tarski(k2_xboole_0(A_41, C_42), k2_xboole_0(B_43, C_42)) | ~r1_tarski(A_41, B_43))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.64/3.80  tff(c_8006, plain, (![A_163, C_164, B_165]: (k2_xboole_0(k2_xboole_0(A_163, C_164), k2_xboole_0(B_165, C_164))=k2_xboole_0(B_165, C_164) | ~r1_tarski(A_163, B_165))), inference(resolution, [status(thm)], [c_209, c_10])).
% 9.64/3.80  tff(c_8377, plain, (![A_163, A_11, B_12]: (k2_xboole_0(k2_xboole_0(A_163, k2_xboole_0(A_11, B_12)), k2_xboole_0(A_11, B_12))=k2_xboole_0(A_11, k2_xboole_0(A_11, B_12)) | ~r1_tarski(A_163, A_11))), inference(superposition, [status(thm), theory('equality')], [c_87, c_8006])).
% 9.64/3.80  tff(c_8503, plain, (![A_166, A_167, B_168]: (k2_xboole_0(A_166, k2_xboole_0(A_167, B_168))=k2_xboole_0(A_167, B_168) | ~r1_tarski(A_166, A_167))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_87, c_2, c_8377])).
% 9.64/3.80  tff(c_8856, plain, (![A_166, A_1, B_2]: (k2_xboole_0(A_166, k2_xboole_0(A_1, B_2))=k2_xboole_0(A_1, k2_xboole_0(B_2, A_1)) | ~r1_tarski(A_166, A_1))), inference(superposition, [status(thm), theory('equality')], [c_182, c_8503])).
% 9.64/3.80  tff(c_11399, plain, (![A_197, A_198, B_199]: (k2_xboole_0(A_197, k2_xboole_0(A_198, B_199))=k2_xboole_0(B_199, A_198) | ~r1_tarski(A_197, A_198))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_8856])).
% 9.64/3.80  tff(c_8751, plain, (![A_166, A_167, B_168]: (r1_tarski(A_166, k2_xboole_0(A_167, B_168)) | ~r1_tarski(A_166, A_167))), inference(superposition, [status(thm), theory('equality')], [c_8503, c_14])).
% 9.64/3.80  tff(c_13483, plain, (![A_213, B_214, A_215, A_216]: (r1_tarski(A_213, k2_xboole_0(B_214, A_215)) | ~r1_tarski(A_213, A_216) | ~r1_tarski(A_216, A_215))), inference(superposition, [status(thm), theory('equality')], [c_11399, c_8751])).
% 9.64/3.80  tff(c_14829, plain, (![B_233, A_234]: (r1_tarski('#skF_1', k2_xboole_0(B_233, A_234)) | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), A_234))), inference(resolution, [status(thm)], [c_30, c_13483])).
% 9.64/3.80  tff(c_14886, plain, (![B_235]: (r1_tarski('#skF_1', k2_xboole_0(B_235, k2_zfmisc_1('#skF_3', '#skF_4'))))), inference(resolution, [status(thm)], [c_8, c_14829])).
% 9.64/3.80  tff(c_14926, plain, (![B_65]: (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', k2_xboole_0('#skF_4', B_65))))), inference(superposition, [status(thm), theory('equality')], [c_989, c_14886])).
% 9.64/3.80  tff(c_24, plain, (![C_22, A_20, B_21]: (k2_xboole_0(k2_zfmisc_1(C_22, A_20), k2_zfmisc_1(C_22, B_21))=k2_zfmisc_1(C_22, k2_xboole_0(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.64/3.80  tff(c_28, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.64/3.80  tff(c_15655, plain, (![B_245, A_246]: (r1_tarski('#skF_2', k2_xboole_0(B_245, A_246)) | ~r1_tarski(k2_zfmisc_1('#skF_5', '#skF_6'), A_246))), inference(resolution, [status(thm)], [c_28, c_13483])).
% 9.64/3.80  tff(c_15716, plain, (![B_247]: (r1_tarski('#skF_2', k2_xboole_0(B_247, k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(resolution, [status(thm)], [c_8, c_15655])).
% 9.64/3.80  tff(c_15772, plain, (![A_20]: (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', k2_xboole_0(A_20, '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_24, c_15716])).
% 9.64/3.80  tff(c_22, plain, (![A_20, C_22, B_21]: (k2_xboole_0(k2_zfmisc_1(A_20, C_22), k2_zfmisc_1(B_21, C_22))=k2_zfmisc_1(k2_xboole_0(A_20, B_21), C_22))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.64/3.80  tff(c_1666, plain, (![A_72, C_73, B_74, D_75]: (r1_tarski(k2_xboole_0(A_72, C_73), k2_xboole_0(B_74, D_75)) | ~r1_tarski(C_73, D_75) | ~r1_tarski(A_72, B_74))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.64/3.80  tff(c_16319, plain, (![A_258, C_255, C_259, A_256, B_257]: (r1_tarski(k2_xboole_0(A_256, C_259), k2_zfmisc_1(k2_xboole_0(A_258, B_257), C_255)) | ~r1_tarski(C_259, k2_zfmisc_1(B_257, C_255)) | ~r1_tarski(A_256, k2_zfmisc_1(A_258, C_255)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1666])).
% 9.64/3.80  tff(c_26, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_2'), k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.64/3.80  tff(c_16588, plain, (~r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', k2_xboole_0('#skF_4', '#skF_6'))) | ~r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', k2_xboole_0('#skF_4', '#skF_6')))), inference(resolution, [status(thm)], [c_16319, c_26])).
% 9.64/3.80  tff(c_16673, plain, (~r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', k2_xboole_0('#skF_4', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_15772, c_16588])).
% 9.64/3.80  tff(c_17276, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14926, c_16673])).
% 9.64/3.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.64/3.80  
% 9.64/3.80  Inference rules
% 9.64/3.80  ----------------------
% 9.64/3.80  #Ref     : 0
% 9.64/3.80  #Sup     : 4566
% 9.64/3.80  #Fact    : 0
% 9.64/3.80  #Define  : 0
% 9.64/3.80  #Split   : 4
% 9.64/3.80  #Chain   : 0
% 9.64/3.80  #Close   : 0
% 9.64/3.80  
% 9.64/3.80  Ordering : KBO
% 9.64/3.80  
% 9.64/3.80  Simplification rules
% 9.64/3.80  ----------------------
% 9.64/3.80  #Subsume      : 836
% 9.64/3.80  #Demod        : 2892
% 9.64/3.80  #Tautology    : 1506
% 9.64/3.80  #SimpNegUnit  : 11
% 9.64/3.80  #BackRed      : 1
% 9.64/3.80  
% 9.64/3.80  #Partial instantiations: 0
% 9.64/3.80  #Strategies tried      : 1
% 9.64/3.80  
% 9.64/3.80  Timing (in seconds)
% 9.64/3.80  ----------------------
% 9.64/3.80  Preprocessing        : 0.29
% 9.64/3.80  Parsing              : 0.16
% 9.64/3.80  CNF conversion       : 0.02
% 9.64/3.80  Main loop            : 2.71
% 9.64/3.80  Inferencing          : 0.57
% 9.64/3.80  Reduction            : 1.33
% 9.64/3.80  Demodulation         : 1.16
% 9.64/3.80  BG Simplification    : 0.07
% 9.64/3.80  Subsumption          : 0.62
% 9.64/3.80  Abstraction          : 0.12
% 9.64/3.80  MUC search           : 0.00
% 9.64/3.80  Cooper               : 0.00
% 9.64/3.80  Total                : 3.04
% 9.64/3.80  Index Insertion      : 0.00
% 9.64/3.80  Index Deletion       : 0.00
% 9.64/3.80  Index Matching       : 0.00
% 9.64/3.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
