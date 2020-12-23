%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:41 EST 2020

% Result     : Theorem 6.71s
% Output     : CNFRefutation 6.71s
% Verified   : 
% Statistics : Number of formulae       :   55 (  85 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :    6
%              Number of atoms          :   68 ( 115 expanded)
%              Number of equality atoms :   13 (  25 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( ( r1_tarski(A,k2_zfmisc_1(C,D))
          & r1_tarski(B,k2_zfmisc_1(E,F)) )
       => r1_tarski(k2_xboole_0(A,B),k2_zfmisc_1(k2_xboole_0(C,E),k2_xboole_0(D,F))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_10,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_70,plain,(
    ! [A_27,B_28] : k3_tarski(k2_tarski(A_27,B_28)) = k2_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_94,plain,(
    ! [B_31,A_32] : k3_tarski(k2_tarski(B_31,A_32)) = k2_xboole_0(A_32,B_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_70])).

tff(c_14,plain,(
    ! [A_15,B_16] : k3_tarski(k2_tarski(A_15,B_16)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_117,plain,(
    ! [B_33,A_34] : k2_xboole_0(B_33,A_34) = k2_xboole_0(A_34,B_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_14])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_132,plain,(
    ! [A_34,B_33] : r1_tarski(A_34,k2_xboole_0(B_33,A_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_6])).

tff(c_344,plain,(
    ! [A_54,C_55,B_56,D_57] :
      ( r1_tarski(k2_zfmisc_1(A_54,C_55),k2_zfmisc_1(B_56,D_57))
      | ~ r1_tarski(C_55,D_57)
      | ~ r1_tarski(A_54,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6958,plain,(
    ! [A_206,C_207,B_208,D_209] :
      ( k2_xboole_0(k2_zfmisc_1(A_206,C_207),k2_zfmisc_1(B_208,D_209)) = k2_zfmisc_1(B_208,D_209)
      | ~ r1_tarski(C_207,D_209)
      | ~ r1_tarski(A_206,B_208) ) ),
    inference(resolution,[status(thm)],[c_344,c_4])).

tff(c_20,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_57,plain,(
    ! [A_25,B_26] :
      ( k2_xboole_0(A_25,B_26) = B_26
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_68,plain,(
    k2_xboole_0('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) = k2_zfmisc_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_57])).

tff(c_171,plain,(
    ! [A_37,C_38,B_39] :
      ( r1_tarski(A_37,C_38)
      | ~ r1_tarski(k2_xboole_0(A_37,B_39),C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_187,plain,(
    ! [A_37,B_39,B_7] : r1_tarski(A_37,k2_xboole_0(k2_xboole_0(A_37,B_39),B_7)) ),
    inference(resolution,[status(thm)],[c_6,c_171])).

tff(c_398,plain,(
    ! [B_7] : r1_tarski('#skF_2',k2_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'),B_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_187])).

tff(c_10669,plain,(
    ! [B_295,D_296] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(B_295,D_296))
      | ~ r1_tarski('#skF_6',D_296)
      | ~ r1_tarski('#skF_5',B_295) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6958,c_398])).

tff(c_16,plain,(
    ! [A_17,C_19,B_18,D_20] :
      ( r1_tarski(k2_zfmisc_1(A_17,C_19),k2_zfmisc_1(B_18,D_20))
      | ~ r1_tarski(C_19,D_20)
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_69,plain,(
    k2_xboole_0('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_57])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_689,plain,(
    ! [C_70] :
      ( r1_tarski('#skF_1',C_70)
      | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),C_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_2])).

tff(c_5516,plain,(
    ! [B_182,D_183] :
      ( r1_tarski('#skF_1',k2_zfmisc_1(B_182,D_183))
      | ~ r1_tarski('#skF_4',D_183)
      | ~ r1_tarski('#skF_3',B_182) ) ),
    inference(resolution,[status(thm)],[c_16,c_689])).

tff(c_188,plain,(
    ! [A_40,C_41,B_42] :
      ( r1_tarski(k2_xboole_0(A_40,C_41),B_42)
      | ~ r1_tarski(C_41,B_42)
      | ~ r1_tarski(A_40,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_2'),k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_205,plain,
    ( ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6')))
    | ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_188,c_18])).

tff(c_542,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_205])).

tff(c_5523,plain,
    ( ~ r1_tarski('#skF_4',k2_xboole_0('#skF_4','#skF_6'))
    | ~ r1_tarski('#skF_3',k2_xboole_0('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_5516,c_542])).

tff(c_5532,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_5523])).

tff(c_5533,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_205])).

tff(c_10676,plain,
    ( ~ r1_tarski('#skF_6',k2_xboole_0('#skF_4','#skF_6'))
    | ~ r1_tarski('#skF_5',k2_xboole_0('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_10669,c_5533])).

tff(c_10685,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_132,c_10676])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:19:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.71/2.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.71/2.45  
% 6.71/2.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.71/2.45  %$ r1_tarski > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.71/2.45  
% 6.71/2.45  %Foreground sorts:
% 6.71/2.45  
% 6.71/2.45  
% 6.71/2.45  %Background operators:
% 6.71/2.45  
% 6.71/2.45  
% 6.71/2.45  %Foreground operators:
% 6.71/2.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.71/2.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.71/2.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.71/2.45  tff('#skF_5', type, '#skF_5': $i).
% 6.71/2.45  tff('#skF_6', type, '#skF_6': $i).
% 6.71/2.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.71/2.45  tff('#skF_2', type, '#skF_2': $i).
% 6.71/2.45  tff('#skF_3', type, '#skF_3': $i).
% 6.71/2.45  tff('#skF_1', type, '#skF_1': $i).
% 6.71/2.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.71/2.45  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.71/2.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.71/2.45  tff('#skF_4', type, '#skF_4': $i).
% 6.71/2.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.71/2.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.71/2.45  
% 6.71/2.46  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.71/2.46  tff(f_47, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.71/2.46  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.71/2.46  tff(f_53, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_zfmisc_1)).
% 6.71/2.46  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.71/2.46  tff(f_60, negated_conjecture, ~(![A, B, C, D, E, F]: ((r1_tarski(A, k2_zfmisc_1(C, D)) & r1_tarski(B, k2_zfmisc_1(E, F))) => r1_tarski(k2_xboole_0(A, B), k2_zfmisc_1(k2_xboole_0(C, E), k2_xboole_0(D, F))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 6.71/2.46  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 6.71/2.46  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 6.71/2.46  tff(c_10, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.71/2.46  tff(c_70, plain, (![A_27, B_28]: (k3_tarski(k2_tarski(A_27, B_28))=k2_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.71/2.46  tff(c_94, plain, (![B_31, A_32]: (k3_tarski(k2_tarski(B_31, A_32))=k2_xboole_0(A_32, B_31))), inference(superposition, [status(thm), theory('equality')], [c_10, c_70])).
% 6.71/2.46  tff(c_14, plain, (![A_15, B_16]: (k3_tarski(k2_tarski(A_15, B_16))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.71/2.46  tff(c_117, plain, (![B_33, A_34]: (k2_xboole_0(B_33, A_34)=k2_xboole_0(A_34, B_33))), inference(superposition, [status(thm), theory('equality')], [c_94, c_14])).
% 6.71/2.46  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.71/2.46  tff(c_132, plain, (![A_34, B_33]: (r1_tarski(A_34, k2_xboole_0(B_33, A_34)))), inference(superposition, [status(thm), theory('equality')], [c_117, c_6])).
% 6.71/2.46  tff(c_344, plain, (![A_54, C_55, B_56, D_57]: (r1_tarski(k2_zfmisc_1(A_54, C_55), k2_zfmisc_1(B_56, D_57)) | ~r1_tarski(C_55, D_57) | ~r1_tarski(A_54, B_56))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.71/2.46  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.71/2.46  tff(c_6958, plain, (![A_206, C_207, B_208, D_209]: (k2_xboole_0(k2_zfmisc_1(A_206, C_207), k2_zfmisc_1(B_208, D_209))=k2_zfmisc_1(B_208, D_209) | ~r1_tarski(C_207, D_209) | ~r1_tarski(A_206, B_208))), inference(resolution, [status(thm)], [c_344, c_4])).
% 6.71/2.46  tff(c_20, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.71/2.46  tff(c_57, plain, (![A_25, B_26]: (k2_xboole_0(A_25, B_26)=B_26 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.71/2.46  tff(c_68, plain, (k2_xboole_0('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))=k2_zfmisc_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_20, c_57])).
% 6.71/2.46  tff(c_171, plain, (![A_37, C_38, B_39]: (r1_tarski(A_37, C_38) | ~r1_tarski(k2_xboole_0(A_37, B_39), C_38))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.71/2.46  tff(c_187, plain, (![A_37, B_39, B_7]: (r1_tarski(A_37, k2_xboole_0(k2_xboole_0(A_37, B_39), B_7)))), inference(resolution, [status(thm)], [c_6, c_171])).
% 6.71/2.46  tff(c_398, plain, (![B_7]: (r1_tarski('#skF_2', k2_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'), B_7)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_187])).
% 6.71/2.46  tff(c_10669, plain, (![B_295, D_296]: (r1_tarski('#skF_2', k2_zfmisc_1(B_295, D_296)) | ~r1_tarski('#skF_6', D_296) | ~r1_tarski('#skF_5', B_295))), inference(superposition, [status(thm), theory('equality')], [c_6958, c_398])).
% 6.71/2.46  tff(c_16, plain, (![A_17, C_19, B_18, D_20]: (r1_tarski(k2_zfmisc_1(A_17, C_19), k2_zfmisc_1(B_18, D_20)) | ~r1_tarski(C_19, D_20) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.71/2.46  tff(c_22, plain, (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.71/2.46  tff(c_69, plain, (k2_xboole_0('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_22, c_57])).
% 6.71/2.46  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.71/2.46  tff(c_689, plain, (![C_70]: (r1_tarski('#skF_1', C_70) | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), C_70))), inference(superposition, [status(thm), theory('equality')], [c_69, c_2])).
% 6.71/2.46  tff(c_5516, plain, (![B_182, D_183]: (r1_tarski('#skF_1', k2_zfmisc_1(B_182, D_183)) | ~r1_tarski('#skF_4', D_183) | ~r1_tarski('#skF_3', B_182))), inference(resolution, [status(thm)], [c_16, c_689])).
% 6.71/2.46  tff(c_188, plain, (![A_40, C_41, B_42]: (r1_tarski(k2_xboole_0(A_40, C_41), B_42) | ~r1_tarski(C_41, B_42) | ~r1_tarski(A_40, B_42))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.71/2.46  tff(c_18, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_2'), k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.71/2.46  tff(c_205, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6'))) | ~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(resolution, [status(thm)], [c_188, c_18])).
% 6.71/2.46  tff(c_542, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(splitLeft, [status(thm)], [c_205])).
% 6.71/2.46  tff(c_5523, plain, (~r1_tarski('#skF_4', k2_xboole_0('#skF_4', '#skF_6')) | ~r1_tarski('#skF_3', k2_xboole_0('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_5516, c_542])).
% 6.71/2.46  tff(c_5532, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_5523])).
% 6.71/2.46  tff(c_5533, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(splitRight, [status(thm)], [c_205])).
% 6.71/2.46  tff(c_10676, plain, (~r1_tarski('#skF_6', k2_xboole_0('#skF_4', '#skF_6')) | ~r1_tarski('#skF_5', k2_xboole_0('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_10669, c_5533])).
% 6.71/2.46  tff(c_10685, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_132, c_132, c_10676])).
% 6.71/2.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.71/2.46  
% 6.71/2.46  Inference rules
% 6.71/2.46  ----------------------
% 6.71/2.46  #Ref     : 0
% 6.71/2.46  #Sup     : 2575
% 6.71/2.46  #Fact    : 0
% 6.71/2.46  #Define  : 0
% 6.71/2.46  #Split   : 1
% 6.71/2.46  #Chain   : 0
% 6.71/2.46  #Close   : 0
% 6.71/2.46  
% 6.71/2.46  Ordering : KBO
% 6.71/2.46  
% 6.71/2.46  Simplification rules
% 6.71/2.46  ----------------------
% 6.71/2.46  #Subsume      : 182
% 6.71/2.46  #Demod        : 1773
% 6.71/2.46  #Tautology    : 1452
% 6.71/2.46  #SimpNegUnit  : 0
% 6.71/2.46  #BackRed      : 0
% 6.71/2.46  
% 6.71/2.46  #Partial instantiations: 0
% 6.71/2.46  #Strategies tried      : 1
% 6.71/2.46  
% 6.71/2.46  Timing (in seconds)
% 6.71/2.46  ----------------------
% 6.71/2.47  Preprocessing        : 0.28
% 6.71/2.47  Parsing              : 0.15
% 6.71/2.47  CNF conversion       : 0.02
% 6.71/2.47  Main loop            : 1.41
% 6.71/2.47  Inferencing          : 0.36
% 6.71/2.47  Reduction            : 0.70
% 6.71/2.47  Demodulation         : 0.61
% 6.71/2.47  BG Simplification    : 0.04
% 6.71/2.47  Subsumption          : 0.23
% 6.71/2.47  Abstraction          : 0.06
% 6.71/2.47  MUC search           : 0.00
% 6.71/2.47  Cooper               : 0.00
% 6.71/2.47  Total                : 1.72
% 6.71/2.47  Index Insertion      : 0.00
% 6.71/2.47  Index Deletion       : 0.00
% 6.71/2.47  Index Matching       : 0.00
% 6.71/2.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
