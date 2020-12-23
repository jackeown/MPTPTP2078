%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:07 EST 2020

% Result     : Theorem 7.65s
% Output     : CNFRefutation 7.65s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 128 expanded)
%              Number of leaves         :   17 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :   83 ( 203 expanded)
%              Number of equality atoms :   15 (  56 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_60,plain,(
    ! [A_19,B_20] :
      ( r1_xboole_0(A_19,B_20)
      | k3_xboole_0(A_19,B_20) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_68,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_20])).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(k3_xboole_0(A_5,C_7),k3_xboole_0(B_6,C_7))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_21,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_16])).

tff(c_55,plain,(
    ! [A_17,B_18] :
      ( k3_xboole_0(A_17,B_18) = k1_xboole_0
      | ~ r1_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_21,c_55])).

tff(c_88,plain,(
    ! [A_23,B_24] :
      ( ~ r1_xboole_0(k3_xboole_0(A_23,B_24),B_24)
      | r1_xboole_0(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_105,plain,(
    ! [B_25,A_26] :
      ( ~ r1_xboole_0(k3_xboole_0(B_25,A_26),B_25)
      | r1_xboole_0(A_26,B_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_88])).

tff(c_108,plain,
    ( ~ r1_xboole_0(k1_xboole_0,'#skF_1')
    | r1_xboole_0(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_105])).

tff(c_121,plain,(
    ~ r1_xboole_0(k1_xboole_0,'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_229,plain,(
    ! [A_36,C_37,B_38] :
      ( r1_tarski(k3_xboole_0(A_36,C_37),k3_xboole_0(B_38,C_37))
      | ~ r1_tarski(A_36,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_244,plain,(
    ! [B_2,A_1,B_38] :
      ( r1_tarski(k3_xboole_0(B_2,A_1),k3_xboole_0(B_38,B_2))
      | ~ r1_tarski(A_1,B_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_229])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_127,plain,(
    ! [A_27,C_28,B_29] :
      ( r1_xboole_0(A_27,C_28)
      | ~ r1_xboole_0(B_29,C_28)
      | ~ r1_tarski(A_27,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_399,plain,(
    ! [A_47,B_48,A_49] :
      ( r1_xboole_0(A_47,B_48)
      | ~ r1_tarski(A_47,A_49)
      | k3_xboole_0(A_49,B_48) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_127])).

tff(c_1454,plain,(
    ! [B_101,A_102,B_103,B_104] :
      ( r1_xboole_0(k3_xboole_0(B_101,A_102),B_103)
      | k3_xboole_0(k3_xboole_0(B_104,B_101),B_103) != k1_xboole_0
      | ~ r1_tarski(A_102,B_104) ) ),
    inference(resolution,[status(thm)],[c_244,c_399])).

tff(c_7384,plain,(
    ! [B_202,A_203,B_204,B_205] :
      ( r1_xboole_0(k3_xboole_0(B_202,A_203),B_204)
      | k3_xboole_0(B_204,k3_xboole_0(B_205,B_202)) != k1_xboole_0
      | ~ r1_tarski(A_203,B_205) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1454])).

tff(c_7477,plain,(
    ! [A_206] :
      ( r1_xboole_0(k3_xboole_0('#skF_2',A_206),'#skF_1')
      | ~ r1_tarski(A_206,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_7384])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( ~ r1_xboole_0(k3_xboole_0(A_13,B_14),B_14)
      | r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_7483,plain,
    ( r1_xboole_0('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_7477,c_14])).

tff(c_7538,plain,(
    r1_xboole_0('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_7483])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_7554,plain,(
    k3_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7538,c_4])).

tff(c_7476,plain,(
    ! [A_203] :
      ( r1_xboole_0(k3_xboole_0('#skF_2',A_203),'#skF_1')
      | ~ r1_tarski(A_203,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_7384])).

tff(c_7558,plain,
    ( r1_xboole_0(k1_xboole_0,'#skF_1')
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7554,c_7476])).

tff(c_7683,plain,(
    r1_xboole_0(k1_xboole_0,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_7558])).

tff(c_7685,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_7683])).

tff(c_7686,plain,(
    r1_xboole_0(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_12,plain,(
    ! [A_10,C_12,B_11] :
      ( r1_xboole_0(A_10,C_12)
      | ~ r1_xboole_0(B_11,C_12)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_7856,plain,(
    ! [A_216] :
      ( r1_xboole_0(A_216,'#skF_1')
      | ~ r1_tarski(A_216,k3_xboole_0('#skF_3','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_7686,c_12])).

tff(c_7961,plain,(
    ! [A_221] :
      ( r1_xboole_0(k3_xboole_0(A_221,'#skF_2'),'#skF_1')
      | ~ r1_tarski(A_221,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_8,c_7856])).

tff(c_98,plain,(
    ! [B_2,A_1] :
      ( ~ r1_xboole_0(k3_xboole_0(B_2,A_1),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_88])).

tff(c_7967,plain,
    ( r1_xboole_0('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_7961,c_98])).

tff(c_7982,plain,(
    r1_xboole_0('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_7967])).

tff(c_7991,plain,(
    k3_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7982,c_4])).

tff(c_8016,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7991,c_2])).

tff(c_8033,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_8016])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:46:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.65/2.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.65/2.87  
% 7.65/2.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.65/2.88  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 7.65/2.88  
% 7.65/2.88  %Foreground sorts:
% 7.65/2.88  
% 7.65/2.88  
% 7.65/2.88  %Background operators:
% 7.65/2.88  
% 7.65/2.88  
% 7.65/2.88  %Foreground operators:
% 7.65/2.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.65/2.88  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.65/2.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.65/2.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.65/2.88  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.65/2.88  tff('#skF_2', type, '#skF_2': $i).
% 7.65/2.88  tff('#skF_3', type, '#skF_3': $i).
% 7.65/2.88  tff('#skF_1', type, '#skF_1': $i).
% 7.65/2.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.65/2.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.65/2.88  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.65/2.88  
% 7.65/2.89  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.65/2.89  tff(f_58, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 7.65/2.89  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_xboole_1)).
% 7.65/2.89  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.65/2.89  tff(f_49, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_xboole_1)).
% 7.65/2.89  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 7.65/2.89  tff(c_60, plain, (![A_19, B_20]: (r1_xboole_0(A_19, B_20) | k3_xboole_0(A_19, B_20)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.65/2.89  tff(c_20, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.65/2.89  tff(c_68, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_60, c_20])).
% 7.65/2.89  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.65/2.89  tff(c_8, plain, (![A_5, C_7, B_6]: (r1_tarski(k3_xboole_0(A_5, C_7), k3_xboole_0(B_6, C_7)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.65/2.89  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.65/2.89  tff(c_16, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.65/2.89  tff(c_21, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_16])).
% 7.65/2.89  tff(c_55, plain, (![A_17, B_18]: (k3_xboole_0(A_17, B_18)=k1_xboole_0 | ~r1_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.65/2.89  tff(c_59, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_21, c_55])).
% 7.65/2.89  tff(c_88, plain, (![A_23, B_24]: (~r1_xboole_0(k3_xboole_0(A_23, B_24), B_24) | r1_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.65/2.89  tff(c_105, plain, (![B_25, A_26]: (~r1_xboole_0(k3_xboole_0(B_25, A_26), B_25) | r1_xboole_0(A_26, B_25))), inference(superposition, [status(thm), theory('equality')], [c_2, c_88])).
% 7.65/2.89  tff(c_108, plain, (~r1_xboole_0(k1_xboole_0, '#skF_1') | r1_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_59, c_105])).
% 7.65/2.89  tff(c_121, plain, (~r1_xboole_0(k1_xboole_0, '#skF_1')), inference(splitLeft, [status(thm)], [c_108])).
% 7.65/2.89  tff(c_229, plain, (![A_36, C_37, B_38]: (r1_tarski(k3_xboole_0(A_36, C_37), k3_xboole_0(B_38, C_37)) | ~r1_tarski(A_36, B_38))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.65/2.89  tff(c_244, plain, (![B_2, A_1, B_38]: (r1_tarski(k3_xboole_0(B_2, A_1), k3_xboole_0(B_38, B_2)) | ~r1_tarski(A_1, B_38))), inference(superposition, [status(thm), theory('equality')], [c_2, c_229])).
% 7.65/2.89  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.65/2.89  tff(c_127, plain, (![A_27, C_28, B_29]: (r1_xboole_0(A_27, C_28) | ~r1_xboole_0(B_29, C_28) | ~r1_tarski(A_27, B_29))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.65/2.89  tff(c_399, plain, (![A_47, B_48, A_49]: (r1_xboole_0(A_47, B_48) | ~r1_tarski(A_47, A_49) | k3_xboole_0(A_49, B_48)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_127])).
% 7.65/2.89  tff(c_1454, plain, (![B_101, A_102, B_103, B_104]: (r1_xboole_0(k3_xboole_0(B_101, A_102), B_103) | k3_xboole_0(k3_xboole_0(B_104, B_101), B_103)!=k1_xboole_0 | ~r1_tarski(A_102, B_104))), inference(resolution, [status(thm)], [c_244, c_399])).
% 7.65/2.89  tff(c_7384, plain, (![B_202, A_203, B_204, B_205]: (r1_xboole_0(k3_xboole_0(B_202, A_203), B_204) | k3_xboole_0(B_204, k3_xboole_0(B_205, B_202))!=k1_xboole_0 | ~r1_tarski(A_203, B_205))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1454])).
% 7.65/2.89  tff(c_7477, plain, (![A_206]: (r1_xboole_0(k3_xboole_0('#skF_2', A_206), '#skF_1') | ~r1_tarski(A_206, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_59, c_7384])).
% 7.65/2.89  tff(c_14, plain, (![A_13, B_14]: (~r1_xboole_0(k3_xboole_0(A_13, B_14), B_14) | r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.65/2.89  tff(c_7483, plain, (r1_xboole_0('#skF_2', '#skF_1') | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_7477, c_14])).
% 7.65/2.89  tff(c_7538, plain, (r1_xboole_0('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_7483])).
% 7.65/2.89  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.65/2.89  tff(c_7554, plain, (k3_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_7538, c_4])).
% 7.65/2.89  tff(c_7476, plain, (![A_203]: (r1_xboole_0(k3_xboole_0('#skF_2', A_203), '#skF_1') | ~r1_tarski(A_203, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_59, c_7384])).
% 7.65/2.89  tff(c_7558, plain, (r1_xboole_0(k1_xboole_0, '#skF_1') | ~r1_tarski('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7554, c_7476])).
% 7.65/2.89  tff(c_7683, plain, (r1_xboole_0(k1_xboole_0, '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_7558])).
% 7.65/2.89  tff(c_7685, plain, $false, inference(negUnitSimplification, [status(thm)], [c_121, c_7683])).
% 7.65/2.89  tff(c_7686, plain, (r1_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_108])).
% 7.65/2.89  tff(c_12, plain, (![A_10, C_12, B_11]: (r1_xboole_0(A_10, C_12) | ~r1_xboole_0(B_11, C_12) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.65/2.89  tff(c_7856, plain, (![A_216]: (r1_xboole_0(A_216, '#skF_1') | ~r1_tarski(A_216, k3_xboole_0('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_7686, c_12])).
% 7.65/2.89  tff(c_7961, plain, (![A_221]: (r1_xboole_0(k3_xboole_0(A_221, '#skF_2'), '#skF_1') | ~r1_tarski(A_221, '#skF_3'))), inference(resolution, [status(thm)], [c_8, c_7856])).
% 7.65/2.89  tff(c_98, plain, (![B_2, A_1]: (~r1_xboole_0(k3_xboole_0(B_2, A_1), B_2) | r1_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_88])).
% 7.65/2.89  tff(c_7967, plain, (r1_xboole_0('#skF_2', '#skF_1') | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_7961, c_98])).
% 7.65/2.89  tff(c_7982, plain, (r1_xboole_0('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_7967])).
% 7.65/2.89  tff(c_7991, plain, (k3_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_7982, c_4])).
% 7.65/2.89  tff(c_8016, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_7991, c_2])).
% 7.65/2.89  tff(c_8033, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_8016])).
% 7.65/2.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.65/2.89  
% 7.65/2.89  Inference rules
% 7.65/2.89  ----------------------
% 7.65/2.89  #Ref     : 0
% 7.65/2.89  #Sup     : 2145
% 7.65/2.89  #Fact    : 0
% 7.65/2.89  #Define  : 0
% 7.65/2.89  #Split   : 12
% 7.65/2.89  #Chain   : 0
% 7.65/2.89  #Close   : 0
% 7.65/2.89  
% 7.65/2.89  Ordering : KBO
% 7.65/2.89  
% 7.65/2.89  Simplification rules
% 7.65/2.89  ----------------------
% 7.65/2.89  #Subsume      : 808
% 7.65/2.89  #Demod        : 422
% 7.65/2.89  #Tautology    : 144
% 7.65/2.89  #SimpNegUnit  : 13
% 7.65/2.89  #BackRed      : 0
% 7.65/2.89  
% 7.65/2.89  #Partial instantiations: 0
% 7.65/2.89  #Strategies tried      : 1
% 7.65/2.89  
% 7.65/2.89  Timing (in seconds)
% 7.65/2.89  ----------------------
% 7.65/2.89  Preprocessing        : 0.27
% 7.65/2.89  Parsing              : 0.15
% 7.65/2.89  CNF conversion       : 0.02
% 7.65/2.89  Main loop            : 1.85
% 7.65/2.89  Inferencing          : 0.44
% 7.65/2.89  Reduction            : 0.66
% 7.65/2.89  Demodulation         : 0.49
% 7.65/2.89  BG Simplification    : 0.05
% 7.65/2.89  Subsumption          : 0.62
% 7.65/2.89  Abstraction          : 0.05
% 7.65/2.89  MUC search           : 0.00
% 7.65/2.89  Cooper               : 0.00
% 7.65/2.89  Total                : 2.16
% 7.65/2.89  Index Insertion      : 0.00
% 7.65/2.89  Index Deletion       : 0.00
% 7.65/2.89  Index Matching       : 0.00
% 7.65/2.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
