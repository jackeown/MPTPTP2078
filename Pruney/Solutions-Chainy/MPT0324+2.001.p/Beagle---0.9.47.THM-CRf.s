%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:19 EST 2020

% Result     : Theorem 10.76s
% Output     : CNFRefutation 10.76s
% Verified   : 
% Statistics : Number of formulae       :   46 (  67 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 (  90 expanded)
%              Number of equality atoms :    6 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( ( r2_hidden(A,k2_zfmisc_1(B,C))
          & r2_hidden(A,k2_zfmisc_1(D,E)) )
       => r2_hidden(A,k2_zfmisc_1(k3_xboole_0(B,D),k3_xboole_0(C,E))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_50,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(c_24,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_22,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(k1_tarski(A_9),B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( r1_xboole_0(k1_tarski(A_11),B_12)
      | r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_209,plain,(
    ! [A_48,C_49,B_50,D_51] : k3_xboole_0(k2_zfmisc_1(A_48,C_49),k2_zfmisc_1(B_50,D_51)) = k2_zfmisc_1(k3_xboole_0(A_48,B_50),k3_xboole_0(C_49,D_51)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] :
      ( ~ r1_xboole_0(A_5,k3_xboole_0(B_6,C_7))
      | ~ r1_tarski(A_5,C_7)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_584,plain,(
    ! [D_70,C_74,A_72,A_73,B_71] :
      ( ~ r1_xboole_0(A_73,k2_zfmisc_1(k3_xboole_0(A_72,B_71),k3_xboole_0(C_74,D_70)))
      | ~ r1_tarski(A_73,k2_zfmisc_1(B_71,D_70))
      | r1_xboole_0(A_73,k2_zfmisc_1(A_72,C_74)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_6])).

tff(c_1220,plain,(
    ! [A_101,B_99,A_100,C_98,D_102] :
      ( ~ r1_xboole_0(A_101,k2_zfmisc_1(k3_xboole_0(A_100,B_99),k3_xboole_0(C_98,D_102)))
      | ~ r1_tarski(A_101,k2_zfmisc_1(A_100,D_102))
      | r1_xboole_0(A_101,k2_zfmisc_1(B_99,C_98)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_584])).

tff(c_9243,plain,(
    ! [D_238,C_234,A_237,B_235,A_236] :
      ( ~ r1_tarski(k1_tarski(A_236),k2_zfmisc_1(A_237,D_238))
      | r1_xboole_0(k1_tarski(A_236),k2_zfmisc_1(B_235,C_234))
      | r2_hidden(A_236,k2_zfmisc_1(k3_xboole_0(A_237,B_235),k3_xboole_0(C_234,D_238))) ) ),
    inference(resolution,[status(thm)],[c_14,c_1220])).

tff(c_20,plain,(
    ~ r2_hidden('#skF_1',k2_zfmisc_1(k3_xboole_0('#skF_2','#skF_4'),k3_xboole_0('#skF_3','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_25,plain,(
    ~ r2_hidden('#skF_1',k2_zfmisc_1(k3_xboole_0('#skF_4','#skF_2'),k3_xboole_0('#skF_3','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_9409,plain,
    ( ~ r1_tarski(k1_tarski('#skF_1'),k2_zfmisc_1('#skF_4','#skF_5'))
    | r1_xboole_0(k1_tarski('#skF_1'),k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_9243,c_25])).

tff(c_9410,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_9409])).

tff(c_9413,plain,(
    ~ r2_hidden('#skF_1',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_12,c_9410])).

tff(c_9417,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_9413])).

tff(c_9418,plain,(
    r1_xboole_0(k1_tarski('#skF_1'),k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_9409])).

tff(c_8,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_90,plain,(
    ! [A_31,C_32,B_33] :
      ( ~ r2_hidden(A_31,C_32)
      | ~ r1_xboole_0(k2_tarski(A_31,B_33),C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_93,plain,(
    ! [A_8,C_32] :
      ( ~ r2_hidden(A_8,C_32)
      | ~ r1_xboole_0(k1_tarski(A_8),C_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_90])).

tff(c_9422,plain,(
    ~ r2_hidden('#skF_1',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_9418,c_93])).

tff(c_9426,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_9422])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:07:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.76/4.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.76/4.23  
% 10.76/4.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.76/4.24  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.76/4.24  
% 10.76/4.24  %Foreground sorts:
% 10.76/4.24  
% 10.76/4.24  
% 10.76/4.24  %Background operators:
% 10.76/4.24  
% 10.76/4.24  
% 10.76/4.24  %Foreground operators:
% 10.76/4.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.76/4.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.76/4.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.76/4.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.76/4.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.76/4.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.76/4.24  tff('#skF_5', type, '#skF_5': $i).
% 10.76/4.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.76/4.24  tff('#skF_2', type, '#skF_2': $i).
% 10.76/4.24  tff('#skF_3', type, '#skF_3': $i).
% 10.76/4.24  tff('#skF_1', type, '#skF_1': $i).
% 10.76/4.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.76/4.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.76/4.24  tff('#skF_4', type, '#skF_4': $i).
% 10.76/4.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.76/4.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.76/4.24  
% 10.76/4.25  tff(f_62, negated_conjecture, ~(![A, B, C, D, E]: ((r2_hidden(A, k2_zfmisc_1(B, C)) & r2_hidden(A, k2_zfmisc_1(D, E))) => r2_hidden(A, k2_zfmisc_1(k3_xboole_0(B, D), k3_xboole_0(C, E))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_zfmisc_1)).
% 10.76/4.25  tff(f_43, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 10.76/4.25  tff(f_48, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 10.76/4.25  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.76/4.25  tff(f_50, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 10.76/4.25  tff(f_37, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 10.76/4.25  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 10.76/4.25  tff(f_55, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 10.76/4.25  tff(c_24, plain, (r2_hidden('#skF_1', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.76/4.25  tff(c_22, plain, (r2_hidden('#skF_1', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.76/4.25  tff(c_12, plain, (![A_9, B_10]: (r1_tarski(k1_tarski(A_9), B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.76/4.25  tff(c_14, plain, (![A_11, B_12]: (r1_xboole_0(k1_tarski(A_11), B_12) | r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.76/4.25  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.76/4.25  tff(c_209, plain, (![A_48, C_49, B_50, D_51]: (k3_xboole_0(k2_zfmisc_1(A_48, C_49), k2_zfmisc_1(B_50, D_51))=k2_zfmisc_1(k3_xboole_0(A_48, B_50), k3_xboole_0(C_49, D_51)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.76/4.25  tff(c_6, plain, (![A_5, B_6, C_7]: (~r1_xboole_0(A_5, k3_xboole_0(B_6, C_7)) | ~r1_tarski(A_5, C_7) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.76/4.25  tff(c_584, plain, (![D_70, C_74, A_72, A_73, B_71]: (~r1_xboole_0(A_73, k2_zfmisc_1(k3_xboole_0(A_72, B_71), k3_xboole_0(C_74, D_70))) | ~r1_tarski(A_73, k2_zfmisc_1(B_71, D_70)) | r1_xboole_0(A_73, k2_zfmisc_1(A_72, C_74)))), inference(superposition, [status(thm), theory('equality')], [c_209, c_6])).
% 10.76/4.25  tff(c_1220, plain, (![A_101, B_99, A_100, C_98, D_102]: (~r1_xboole_0(A_101, k2_zfmisc_1(k3_xboole_0(A_100, B_99), k3_xboole_0(C_98, D_102))) | ~r1_tarski(A_101, k2_zfmisc_1(A_100, D_102)) | r1_xboole_0(A_101, k2_zfmisc_1(B_99, C_98)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_584])).
% 10.76/4.25  tff(c_9243, plain, (![D_238, C_234, A_237, B_235, A_236]: (~r1_tarski(k1_tarski(A_236), k2_zfmisc_1(A_237, D_238)) | r1_xboole_0(k1_tarski(A_236), k2_zfmisc_1(B_235, C_234)) | r2_hidden(A_236, k2_zfmisc_1(k3_xboole_0(A_237, B_235), k3_xboole_0(C_234, D_238))))), inference(resolution, [status(thm)], [c_14, c_1220])).
% 10.76/4.25  tff(c_20, plain, (~r2_hidden('#skF_1', k2_zfmisc_1(k3_xboole_0('#skF_2', '#skF_4'), k3_xboole_0('#skF_3', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.76/4.25  tff(c_25, plain, (~r2_hidden('#skF_1', k2_zfmisc_1(k3_xboole_0('#skF_4', '#skF_2'), k3_xboole_0('#skF_3', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20])).
% 10.76/4.25  tff(c_9409, plain, (~r1_tarski(k1_tarski('#skF_1'), k2_zfmisc_1('#skF_4', '#skF_5')) | r1_xboole_0(k1_tarski('#skF_1'), k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_9243, c_25])).
% 10.76/4.25  tff(c_9410, plain, (~r1_tarski(k1_tarski('#skF_1'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_9409])).
% 10.76/4.25  tff(c_9413, plain, (~r2_hidden('#skF_1', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_12, c_9410])).
% 10.76/4.25  tff(c_9417, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_9413])).
% 10.76/4.25  tff(c_9418, plain, (r1_xboole_0(k1_tarski('#skF_1'), k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_9409])).
% 10.76/4.25  tff(c_8, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.76/4.25  tff(c_90, plain, (![A_31, C_32, B_33]: (~r2_hidden(A_31, C_32) | ~r1_xboole_0(k2_tarski(A_31, B_33), C_32))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.76/4.25  tff(c_93, plain, (![A_8, C_32]: (~r2_hidden(A_8, C_32) | ~r1_xboole_0(k1_tarski(A_8), C_32))), inference(superposition, [status(thm), theory('equality')], [c_8, c_90])).
% 10.76/4.25  tff(c_9422, plain, (~r2_hidden('#skF_1', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_9418, c_93])).
% 10.76/4.25  tff(c_9426, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_9422])).
% 10.76/4.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.76/4.25  
% 10.76/4.25  Inference rules
% 10.76/4.25  ----------------------
% 10.76/4.25  #Ref     : 0
% 10.76/4.25  #Sup     : 2656
% 10.76/4.25  #Fact    : 0
% 10.76/4.25  #Define  : 0
% 10.76/4.25  #Split   : 3
% 10.76/4.25  #Chain   : 0
% 10.76/4.25  #Close   : 0
% 10.76/4.25  
% 10.76/4.25  Ordering : KBO
% 10.76/4.25  
% 10.76/4.25  Simplification rules
% 10.76/4.25  ----------------------
% 10.76/4.25  #Subsume      : 325
% 10.76/4.25  #Demod        : 1540
% 10.76/4.25  #Tautology    : 332
% 10.76/4.25  #SimpNegUnit  : 0
% 10.76/4.25  #BackRed      : 0
% 10.76/4.25  
% 10.76/4.25  #Partial instantiations: 0
% 10.76/4.25  #Strategies tried      : 1
% 10.76/4.25  
% 10.76/4.25  Timing (in seconds)
% 10.76/4.25  ----------------------
% 10.76/4.25  Preprocessing        : 0.27
% 10.76/4.25  Parsing              : 0.14
% 10.76/4.25  CNF conversion       : 0.02
% 10.76/4.25  Main loop            : 3.18
% 10.76/4.25  Inferencing          : 0.63
% 10.76/4.25  Reduction            : 1.99
% 10.76/4.25  Demodulation         : 1.85
% 10.76/4.25  BG Simplification    : 0.10
% 10.76/4.25  Subsumption          : 0.37
% 10.76/4.25  Abstraction          : 0.16
% 10.76/4.25  MUC search           : 0.00
% 10.76/4.25  Cooper               : 0.00
% 10.76/4.25  Total                : 3.48
% 10.76/4.25  Index Insertion      : 0.00
% 10.76/4.25  Index Deletion       : 0.00
% 10.76/4.25  Index Matching       : 0.00
% 10.76/4.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
