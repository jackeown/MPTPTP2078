%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:41 EST 2020

% Result     : Theorem 5.37s
% Output     : CNFRefutation 5.37s
% Verified   : 
% Statistics : Number of formulae       :   48 (  60 expanded)
%              Number of leaves         :   22 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   48 (  70 expanded)
%              Number of equality atoms :   16 (  23 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( ( r1_tarski(A,k2_zfmisc_1(C,D))
          & r1_tarski(B,k2_zfmisc_1(E,F)) )
       => r1_tarski(k2_xboole_0(A,B),k2_zfmisc_1(k2_xboole_0(C,E),k2_xboole_0(D,F))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_45,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).

tff(c_373,plain,(
    ! [A_51,C_52,B_53] : k2_xboole_0(k2_zfmisc_1(A_51,C_52),k2_zfmisc_1(B_53,C_52)) = k2_zfmisc_1(k2_xboole_0(A_51,B_53),C_52) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_57,plain,(
    ! [A_23,B_24] :
      ( k2_xboole_0(A_23,B_24) = B_24
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_69,plain,(
    k2_xboole_0('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_57])).

tff(c_8,plain,(
    ! [A_10,B_11] : r1_tarski(A_10,k2_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_162,plain,(
    ! [A_33,C_34,B_35] :
      ( r1_tarski(A_33,C_34)
      | ~ r1_tarski(k2_xboole_0(A_33,B_35),C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_178,plain,(
    ! [A_33,B_35,B_11] : r1_tarski(A_33,k2_xboole_0(k2_xboole_0(A_33,B_35),B_11)) ),
    inference(resolution,[status(thm)],[c_8,c_162])).

tff(c_304,plain,(
    ! [B_11] : r1_tarski('#skF_1',k2_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),B_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_178])).

tff(c_384,plain,(
    ! [B_53] : r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3',B_53),'#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_304])).

tff(c_14,plain,(
    ! [A_16,C_18,B_17] : k2_xboole_0(k2_zfmisc_1(A_16,C_18),k2_zfmisc_1(B_17,C_18)) = k2_zfmisc_1(k2_xboole_0(A_16,B_17),C_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_70,plain,(
    ! [A_25,B_26] : k3_tarski(k2_tarski(A_25,B_26)) = k2_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_85,plain,(
    ! [B_27,A_28] : k3_tarski(k2_tarski(B_27,A_28)) = k2_xboole_0(A_28,B_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_70])).

tff(c_12,plain,(
    ! [A_14,B_15] : k3_tarski(k2_tarski(A_14,B_15)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_91,plain,(
    ! [B_27,A_28] : k2_xboole_0(B_27,A_28) = k2_xboole_0(A_28,B_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_12])).

tff(c_20,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_68,plain,(
    k2_xboole_0('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) = k2_zfmisc_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_57])).

tff(c_511,plain,(
    ! [B_58] : r1_tarski('#skF_2',k2_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'),B_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_178])).

tff(c_558,plain,(
    ! [B_61] : r1_tarski('#skF_2',k2_xboole_0(B_61,k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_511])).

tff(c_567,plain,(
    ! [A_16] : r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0(A_16,'#skF_5'),'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_558])).

tff(c_16,plain,(
    ! [C_18,A_16,B_17] : k2_xboole_0(k2_zfmisc_1(C_18,A_16),k2_zfmisc_1(C_18,B_17)) = k2_zfmisc_1(C_18,k2_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_585,plain,(
    ! [A_62,C_63,B_64,D_65] :
      ( r1_tarski(k2_xboole_0(A_62,C_63),k2_xboole_0(B_64,D_65))
      | ~ r1_tarski(C_63,D_65)
      | ~ r1_tarski(A_62,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5541,plain,(
    ! [A_191,C_193,B_190,A_192,C_189] :
      ( r1_tarski(k2_xboole_0(A_191,C_189),k2_zfmisc_1(C_193,k2_xboole_0(A_192,B_190)))
      | ~ r1_tarski(C_189,k2_zfmisc_1(C_193,B_190))
      | ~ r1_tarski(A_191,k2_zfmisc_1(C_193,A_192)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_585])).

tff(c_18,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_2'),k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_5552,plain,
    ( ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),'#skF_6'))
    | ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_5541,c_18])).

tff(c_5647,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_567,c_5552])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:51:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.37/2.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.37/2.16  
% 5.37/2.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.37/2.16  %$ r1_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.37/2.16  
% 5.37/2.16  %Foreground sorts:
% 5.37/2.16  
% 5.37/2.16  
% 5.37/2.16  %Background operators:
% 5.37/2.16  
% 5.37/2.16  
% 5.37/2.16  %Foreground operators:
% 5.37/2.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.37/2.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.37/2.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.37/2.16  tff('#skF_5', type, '#skF_5': $i).
% 5.37/2.16  tff('#skF_6', type, '#skF_6': $i).
% 5.37/2.16  tff('#skF_2', type, '#skF_2': $i).
% 5.37/2.16  tff('#skF_3', type, '#skF_3': $i).
% 5.37/2.16  tff('#skF_1', type, '#skF_1': $i).
% 5.37/2.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.37/2.16  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.37/2.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.37/2.16  tff('#skF_4', type, '#skF_4': $i).
% 5.37/2.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.37/2.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.37/2.16  
% 5.37/2.17  tff(f_49, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 5.37/2.17  tff(f_56, negated_conjecture, ~(![A, B, C, D, E, F]: ((r1_tarski(A, k2_zfmisc_1(C, D)) & r1_tarski(B, k2_zfmisc_1(E, F))) => r1_tarski(k2_xboole_0(A, B), k2_zfmisc_1(k2_xboole_0(C, E), k2_xboole_0(D, F))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 5.37/2.17  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.37/2.17  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.37/2.17  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 5.37/2.17  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.37/2.17  tff(f_45, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.37/2.17  tff(f_39, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_xboole_1)).
% 5.37/2.17  tff(c_373, plain, (![A_51, C_52, B_53]: (k2_xboole_0(k2_zfmisc_1(A_51, C_52), k2_zfmisc_1(B_53, C_52))=k2_zfmisc_1(k2_xboole_0(A_51, B_53), C_52))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.37/2.17  tff(c_22, plain, (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.37/2.17  tff(c_57, plain, (![A_23, B_24]: (k2_xboole_0(A_23, B_24)=B_24 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.37/2.17  tff(c_69, plain, (k2_xboole_0('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_22, c_57])).
% 5.37/2.17  tff(c_8, plain, (![A_10, B_11]: (r1_tarski(A_10, k2_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.37/2.17  tff(c_162, plain, (![A_33, C_34, B_35]: (r1_tarski(A_33, C_34) | ~r1_tarski(k2_xboole_0(A_33, B_35), C_34))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.37/2.17  tff(c_178, plain, (![A_33, B_35, B_11]: (r1_tarski(A_33, k2_xboole_0(k2_xboole_0(A_33, B_35), B_11)))), inference(resolution, [status(thm)], [c_8, c_162])).
% 5.37/2.17  tff(c_304, plain, (![B_11]: (r1_tarski('#skF_1', k2_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), B_11)))), inference(superposition, [status(thm), theory('equality')], [c_69, c_178])).
% 5.37/2.17  tff(c_384, plain, (![B_53]: (r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', B_53), '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_373, c_304])).
% 5.37/2.17  tff(c_14, plain, (![A_16, C_18, B_17]: (k2_xboole_0(k2_zfmisc_1(A_16, C_18), k2_zfmisc_1(B_17, C_18))=k2_zfmisc_1(k2_xboole_0(A_16, B_17), C_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.37/2.17  tff(c_10, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.37/2.17  tff(c_70, plain, (![A_25, B_26]: (k3_tarski(k2_tarski(A_25, B_26))=k2_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.37/2.17  tff(c_85, plain, (![B_27, A_28]: (k3_tarski(k2_tarski(B_27, A_28))=k2_xboole_0(A_28, B_27))), inference(superposition, [status(thm), theory('equality')], [c_10, c_70])).
% 5.37/2.17  tff(c_12, plain, (![A_14, B_15]: (k3_tarski(k2_tarski(A_14, B_15))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.37/2.17  tff(c_91, plain, (![B_27, A_28]: (k2_xboole_0(B_27, A_28)=k2_xboole_0(A_28, B_27))), inference(superposition, [status(thm), theory('equality')], [c_85, c_12])).
% 5.37/2.17  tff(c_20, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.37/2.17  tff(c_68, plain, (k2_xboole_0('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))=k2_zfmisc_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_20, c_57])).
% 5.37/2.17  tff(c_511, plain, (![B_58]: (r1_tarski('#skF_2', k2_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'), B_58)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_178])).
% 5.37/2.17  tff(c_558, plain, (![B_61]: (r1_tarski('#skF_2', k2_xboole_0(B_61, k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_91, c_511])).
% 5.37/2.17  tff(c_567, plain, (![A_16]: (r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0(A_16, '#skF_5'), '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_14, c_558])).
% 5.37/2.17  tff(c_16, plain, (![C_18, A_16, B_17]: (k2_xboole_0(k2_zfmisc_1(C_18, A_16), k2_zfmisc_1(C_18, B_17))=k2_zfmisc_1(C_18, k2_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.37/2.17  tff(c_585, plain, (![A_62, C_63, B_64, D_65]: (r1_tarski(k2_xboole_0(A_62, C_63), k2_xboole_0(B_64, D_65)) | ~r1_tarski(C_63, D_65) | ~r1_tarski(A_62, B_64))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.37/2.17  tff(c_5541, plain, (![A_191, C_193, B_190, A_192, C_189]: (r1_tarski(k2_xboole_0(A_191, C_189), k2_zfmisc_1(C_193, k2_xboole_0(A_192, B_190))) | ~r1_tarski(C_189, k2_zfmisc_1(C_193, B_190)) | ~r1_tarski(A_191, k2_zfmisc_1(C_193, A_192)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_585])).
% 5.37/2.17  tff(c_18, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_2'), k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.37/2.17  tff(c_5552, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), '#skF_6')) | ~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_5541, c_18])).
% 5.37/2.17  tff(c_5647, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_384, c_567, c_5552])).
% 5.37/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.37/2.17  
% 5.37/2.17  Inference rules
% 5.37/2.17  ----------------------
% 5.37/2.17  #Ref     : 0
% 5.37/2.17  #Sup     : 1377
% 5.37/2.17  #Fact    : 0
% 5.37/2.17  #Define  : 0
% 5.37/2.17  #Split   : 0
% 5.37/2.17  #Chain   : 0
% 5.37/2.17  #Close   : 0
% 5.37/2.17  
% 5.37/2.17  Ordering : KBO
% 5.37/2.17  
% 5.37/2.17  Simplification rules
% 5.37/2.17  ----------------------
% 5.37/2.17  #Subsume      : 42
% 5.37/2.17  #Demod        : 711
% 5.37/2.17  #Tautology    : 602
% 5.37/2.17  #SimpNegUnit  : 0
% 5.37/2.17  #BackRed      : 0
% 5.37/2.17  
% 5.37/2.17  #Partial instantiations: 0
% 5.37/2.17  #Strategies tried      : 1
% 5.37/2.17  
% 5.37/2.17  Timing (in seconds)
% 5.37/2.17  ----------------------
% 5.37/2.18  Preprocessing        : 0.34
% 5.37/2.18  Parsing              : 0.19
% 5.37/2.18  CNF conversion       : 0.02
% 5.37/2.18  Main loop            : 1.03
% 5.37/2.18  Inferencing          : 0.29
% 5.37/2.18  Reduction            : 0.48
% 5.37/2.18  Demodulation         : 0.41
% 5.37/2.18  BG Simplification    : 0.03
% 5.37/2.18  Subsumption          : 0.17
% 5.37/2.18  Abstraction          : 0.04
% 5.37/2.18  MUC search           : 0.00
% 5.37/2.18  Cooper               : 0.00
% 5.37/2.18  Total                : 1.40
% 5.37/2.18  Index Insertion      : 0.00
% 5.37/2.18  Index Deletion       : 0.00
% 5.37/2.18  Index Matching       : 0.00
% 5.37/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
