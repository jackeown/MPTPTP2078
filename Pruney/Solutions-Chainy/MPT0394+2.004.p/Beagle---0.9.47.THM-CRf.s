%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:21 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   46 (  67 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   46 (  75 expanded)
%              Number of equality atoms :   34 (  52 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_zfmisc_1)).

tff(f_68,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_66,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_172,plain,(
    ! [A_41,B_42] :
      ( r1_xboole_0(A_41,B_42)
      | k3_xboole_0(A_41,B_42) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( ~ r2_hidden(A_19,B_20)
      | ~ r1_xboole_0(k1_tarski(A_19),B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_249,plain,(
    ! [A_53,B_54] :
      ( ~ r2_hidden(A_53,B_54)
      | k3_xboole_0(k1_tarski(A_53),B_54) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_172,c_22])).

tff(c_262,plain,(
    ! [A_53] : ~ r2_hidden(A_53,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_249])).

tff(c_58,plain,(
    ! [B_31,A_32] : k3_xboole_0(B_31,A_32) = k3_xboole_0(A_32,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_74,plain,(
    ! [A_32] : k3_xboole_0(k1_xboole_0,A_32) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_8])).

tff(c_235,plain,(
    ! [B_50,A_51] :
      ( r2_hidden(B_50,A_51)
      | k3_xboole_0(A_51,k1_tarski(B_50)) != k1_tarski(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_239,plain,(
    ! [B_50] :
      ( r2_hidden(B_50,k1_xboole_0)
      | k1_tarski(B_50) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_235])).

tff(c_263,plain,(
    ! [B_50] : k1_tarski(B_50) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_262,c_239])).

tff(c_30,plain,(
    ! [A_27] : k1_setfam_1(k1_tarski(A_27)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_12,plain,(
    ! [A_8,B_9] : k2_xboole_0(k1_tarski(A_8),k1_tarski(B_9)) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_404,plain,(
    ! [A_72,B_73] :
      ( k3_xboole_0(k1_setfam_1(A_72),k1_setfam_1(B_73)) = k1_setfam_1(k2_xboole_0(A_72,B_73))
      | k1_xboole_0 = B_73
      | k1_xboole_0 = A_72 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_428,plain,(
    ! [A_27,B_73] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_27),B_73)) = k3_xboole_0(A_27,k1_setfam_1(B_73))
      | k1_xboole_0 = B_73
      | k1_tarski(A_27) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_404])).

tff(c_481,plain,(
    ! [A_76,B_77] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_76),B_77)) = k3_xboole_0(A_76,k1_setfam_1(B_77))
      | k1_xboole_0 = B_77 ) ),
    inference(negUnitSimplification,[status(thm)],[c_263,c_428])).

tff(c_499,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,k1_setfam_1(k1_tarski(B_9))) = k1_setfam_1(k2_tarski(A_8,B_9))
      | k1_tarski(B_9) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_481])).

tff(c_506,plain,(
    ! [A_8,B_9] :
      ( k1_setfam_1(k2_tarski(A_8,B_9)) = k3_xboole_0(A_8,B_9)
      | k1_tarski(B_9) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_499])).

tff(c_507,plain,(
    ! [A_8,B_9] : k1_setfam_1(k2_tarski(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(negUnitSimplification,[status(thm)],[c_263,c_506])).

tff(c_32,plain,(
    k1_setfam_1(k2_tarski('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_624,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_507,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:18:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.31  
% 2.09/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.32  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.09/1.32  
% 2.09/1.32  %Foreground sorts:
% 2.09/1.32  
% 2.09/1.32  
% 2.09/1.32  %Background operators:
% 2.09/1.32  
% 2.09/1.32  
% 2.09/1.32  %Foreground operators:
% 2.09/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.09/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.09/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.09/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.09/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.09/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.09/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.09/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.09/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.09/1.32  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.09/1.32  
% 2.09/1.33  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.09/1.33  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.09/1.33  tff(f_50, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.09/1.33  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.09/1.33  tff(f_54, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 2.09/1.33  tff(f_68, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.09/1.33  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.09/1.33  tff(f_66, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_setfam_1)).
% 2.09/1.33  tff(f_71, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.09/1.33  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.09/1.33  tff(c_172, plain, (![A_41, B_42]: (r1_xboole_0(A_41, B_42) | k3_xboole_0(A_41, B_42)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.09/1.33  tff(c_22, plain, (![A_19, B_20]: (~r2_hidden(A_19, B_20) | ~r1_xboole_0(k1_tarski(A_19), B_20))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.09/1.33  tff(c_249, plain, (![A_53, B_54]: (~r2_hidden(A_53, B_54) | k3_xboole_0(k1_tarski(A_53), B_54)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_172, c_22])).
% 2.09/1.33  tff(c_262, plain, (![A_53]: (~r2_hidden(A_53, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_249])).
% 2.09/1.33  tff(c_58, plain, (![B_31, A_32]: (k3_xboole_0(B_31, A_32)=k3_xboole_0(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.09/1.33  tff(c_74, plain, (![A_32]: (k3_xboole_0(k1_xboole_0, A_32)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_58, c_8])).
% 2.09/1.33  tff(c_235, plain, (![B_50, A_51]: (r2_hidden(B_50, A_51) | k3_xboole_0(A_51, k1_tarski(B_50))!=k1_tarski(B_50))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.09/1.33  tff(c_239, plain, (![B_50]: (r2_hidden(B_50, k1_xboole_0) | k1_tarski(B_50)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_74, c_235])).
% 2.09/1.33  tff(c_263, plain, (![B_50]: (k1_tarski(B_50)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_262, c_239])).
% 2.09/1.33  tff(c_30, plain, (![A_27]: (k1_setfam_1(k1_tarski(A_27))=A_27)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.09/1.33  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(k1_tarski(A_8), k1_tarski(B_9))=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.09/1.33  tff(c_404, plain, (![A_72, B_73]: (k3_xboole_0(k1_setfam_1(A_72), k1_setfam_1(B_73))=k1_setfam_1(k2_xboole_0(A_72, B_73)) | k1_xboole_0=B_73 | k1_xboole_0=A_72)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.09/1.33  tff(c_428, plain, (![A_27, B_73]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_27), B_73))=k3_xboole_0(A_27, k1_setfam_1(B_73)) | k1_xboole_0=B_73 | k1_tarski(A_27)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30, c_404])).
% 2.09/1.33  tff(c_481, plain, (![A_76, B_77]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_76), B_77))=k3_xboole_0(A_76, k1_setfam_1(B_77)) | k1_xboole_0=B_77)), inference(negUnitSimplification, [status(thm)], [c_263, c_428])).
% 2.09/1.33  tff(c_499, plain, (![A_8, B_9]: (k3_xboole_0(A_8, k1_setfam_1(k1_tarski(B_9)))=k1_setfam_1(k2_tarski(A_8, B_9)) | k1_tarski(B_9)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_481])).
% 2.09/1.33  tff(c_506, plain, (![A_8, B_9]: (k1_setfam_1(k2_tarski(A_8, B_9))=k3_xboole_0(A_8, B_9) | k1_tarski(B_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_499])).
% 2.09/1.33  tff(c_507, plain, (![A_8, B_9]: (k1_setfam_1(k2_tarski(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(negUnitSimplification, [status(thm)], [c_263, c_506])).
% 2.09/1.33  tff(c_32, plain, (k1_setfam_1(k2_tarski('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.09/1.33  tff(c_624, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_507, c_32])).
% 2.09/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.33  
% 2.09/1.33  Inference rules
% 2.09/1.33  ----------------------
% 2.09/1.33  #Ref     : 0
% 2.09/1.33  #Sup     : 140
% 2.09/1.33  #Fact    : 0
% 2.09/1.33  #Define  : 0
% 2.09/1.33  #Split   : 0
% 2.09/1.33  #Chain   : 0
% 2.09/1.33  #Close   : 0
% 2.09/1.33  
% 2.09/1.33  Ordering : KBO
% 2.09/1.33  
% 2.09/1.33  Simplification rules
% 2.09/1.33  ----------------------
% 2.09/1.33  #Subsume      : 10
% 2.09/1.33  #Demod        : 53
% 2.09/1.33  #Tautology    : 88
% 2.09/1.33  #SimpNegUnit  : 6
% 2.09/1.33  #BackRed      : 2
% 2.09/1.33  
% 2.09/1.33  #Partial instantiations: 0
% 2.09/1.33  #Strategies tried      : 1
% 2.09/1.33  
% 2.09/1.33  Timing (in seconds)
% 2.09/1.33  ----------------------
% 2.09/1.33  Preprocessing        : 0.29
% 2.09/1.33  Parsing              : 0.16
% 2.09/1.33  CNF conversion       : 0.02
% 2.09/1.33  Main loop            : 0.25
% 2.49/1.33  Inferencing          : 0.10
% 2.49/1.33  Reduction            : 0.09
% 2.49/1.33  Demodulation         : 0.07
% 2.49/1.33  BG Simplification    : 0.02
% 2.49/1.33  Subsumption          : 0.04
% 2.49/1.33  Abstraction          : 0.02
% 2.49/1.33  MUC search           : 0.00
% 2.49/1.33  Cooper               : 0.00
% 2.49/1.33  Total                : 0.57
% 2.49/1.33  Index Insertion      : 0.00
% 2.49/1.33  Index Deletion       : 0.00
% 2.49/1.33  Index Matching       : 0.00
% 2.49/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
