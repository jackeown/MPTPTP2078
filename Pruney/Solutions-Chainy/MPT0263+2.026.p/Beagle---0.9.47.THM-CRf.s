%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:17 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   50 (  56 expanded)
%              Number of leaves         :   25 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   56 (  63 expanded)
%              Number of equality atoms :   29 (  35 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_92,plain,(
    ! [A_33,B_34] :
      ( r1_xboole_0(k1_tarski(A_33),B_34)
      | r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_36,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_100,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_92,c_36])).

tff(c_20,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_405,plain,(
    ! [A_70,B_71,C_72] :
      ( r1_tarski(k2_tarski(A_70,B_71),C_72)
      | ~ r2_hidden(B_71,C_72)
      | ~ r2_hidden(A_70,C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_671,plain,(
    ! [A_91,C_92] :
      ( r1_tarski(k1_tarski(A_91),C_92)
      | ~ r2_hidden(A_91,C_92)
      | ~ r2_hidden(A_91,C_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_405])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_679,plain,(
    ! [A_91,C_92] :
      ( k4_xboole_0(k1_tarski(A_91),C_92) = k1_xboole_0
      | ~ r2_hidden(A_91,C_92) ) ),
    inference(resolution,[status(thm)],[c_671,c_10])).

tff(c_12,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_176,plain,(
    ! [A_53,B_54] : k4_xboole_0(A_53,k4_xboole_0(A_53,B_54)) = k3_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_179,plain,(
    ! [A_53,B_54] : k4_xboole_0(A_53,k3_xboole_0(A_53,B_54)) = k3_xboole_0(A_53,k4_xboole_0(A_53,B_54)) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_14])).

tff(c_192,plain,(
    ! [A_53,B_54] : k3_xboole_0(A_53,k4_xboole_0(A_53,B_54)) = k4_xboole_0(A_53,B_54) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_179])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_115,plain,(
    ! [A_39,B_40] :
      ( k4_xboole_0(A_39,B_40) = A_39
      | ~ r1_xboole_0(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_268,plain,(
    ! [A_61,B_62] :
      ( k4_xboole_0(A_61,B_62) = A_61
      | k3_xboole_0(A_61,B_62) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_115])).

tff(c_301,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | k3_xboole_0(A_9,k4_xboole_0(A_9,B_10)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_268])).

tff(c_747,plain,(
    ! [A_95,B_96] :
      ( k3_xboole_0(A_95,B_96) = A_95
      | k4_xboole_0(A_95,B_96) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_301])).

tff(c_770,plain,(
    ! [A_97,C_98] :
      ( k3_xboole_0(k1_tarski(A_97),C_98) = k1_tarski(A_97)
      | ~ r2_hidden(A_97,C_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_679,c_747])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_845,plain,(
    ! [C_99,A_100] :
      ( k3_xboole_0(C_99,k1_tarski(A_100)) = k1_tarski(A_100)
      | ~ r2_hidden(A_100,C_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_770,c_2])).

tff(c_34,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_37,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_34])).

tff(c_877,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_845,c_37])).

tff(c_914,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_877])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:31:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.38  
% 2.70/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.38  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.70/1.38  
% 2.70/1.38  %Foreground sorts:
% 2.70/1.38  
% 2.70/1.38  
% 2.70/1.38  %Background operators:
% 2.70/1.38  
% 2.70/1.38  
% 2.70/1.38  %Foreground operators:
% 2.70/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.70/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.70/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.70/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.70/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.70/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.70/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.70/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.70/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.70/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.70/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.70/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.70/1.38  
% 2.70/1.39  tff(f_54, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.70/1.39  tff(f_65, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 2.70/1.39  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.70/1.39  tff(f_60, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.70/1.39  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.70/1.39  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.70/1.39  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.70/1.39  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.70/1.39  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.70/1.39  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.70/1.39  tff(c_92, plain, (![A_33, B_34]: (r1_xboole_0(k1_tarski(A_33), B_34) | r2_hidden(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.70/1.39  tff(c_36, plain, (~r1_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.70/1.39  tff(c_100, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_92, c_36])).
% 2.70/1.39  tff(c_20, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.70/1.39  tff(c_405, plain, (![A_70, B_71, C_72]: (r1_tarski(k2_tarski(A_70, B_71), C_72) | ~r2_hidden(B_71, C_72) | ~r2_hidden(A_70, C_72))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.70/1.39  tff(c_671, plain, (![A_91, C_92]: (r1_tarski(k1_tarski(A_91), C_92) | ~r2_hidden(A_91, C_92) | ~r2_hidden(A_91, C_92))), inference(superposition, [status(thm), theory('equality')], [c_20, c_405])).
% 2.70/1.39  tff(c_10, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.70/1.39  tff(c_679, plain, (![A_91, C_92]: (k4_xboole_0(k1_tarski(A_91), C_92)=k1_xboole_0 | ~r2_hidden(A_91, C_92))), inference(resolution, [status(thm)], [c_671, c_10])).
% 2.70/1.39  tff(c_12, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.70/1.39  tff(c_176, plain, (![A_53, B_54]: (k4_xboole_0(A_53, k4_xboole_0(A_53, B_54))=k3_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.70/1.39  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.70/1.39  tff(c_179, plain, (![A_53, B_54]: (k4_xboole_0(A_53, k3_xboole_0(A_53, B_54))=k3_xboole_0(A_53, k4_xboole_0(A_53, B_54)))), inference(superposition, [status(thm), theory('equality')], [c_176, c_14])).
% 2.70/1.39  tff(c_192, plain, (![A_53, B_54]: (k3_xboole_0(A_53, k4_xboole_0(A_53, B_54))=k4_xboole_0(A_53, B_54))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_179])).
% 2.70/1.39  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.70/1.39  tff(c_115, plain, (![A_39, B_40]: (k4_xboole_0(A_39, B_40)=A_39 | ~r1_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.70/1.39  tff(c_268, plain, (![A_61, B_62]: (k4_xboole_0(A_61, B_62)=A_61 | k3_xboole_0(A_61, B_62)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_115])).
% 2.70/1.39  tff(c_301, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | k3_xboole_0(A_9, k4_xboole_0(A_9, B_10))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_268])).
% 2.70/1.39  tff(c_747, plain, (![A_95, B_96]: (k3_xboole_0(A_95, B_96)=A_95 | k4_xboole_0(A_95, B_96)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_192, c_301])).
% 2.70/1.39  tff(c_770, plain, (![A_97, C_98]: (k3_xboole_0(k1_tarski(A_97), C_98)=k1_tarski(A_97) | ~r2_hidden(A_97, C_98))), inference(superposition, [status(thm), theory('equality')], [c_679, c_747])).
% 2.70/1.39  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.70/1.39  tff(c_845, plain, (![C_99, A_100]: (k3_xboole_0(C_99, k1_tarski(A_100))=k1_tarski(A_100) | ~r2_hidden(A_100, C_99))), inference(superposition, [status(thm), theory('equality')], [c_770, c_2])).
% 2.70/1.39  tff(c_34, plain, (k3_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.70/1.39  tff(c_37, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_34])).
% 2.70/1.39  tff(c_877, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_845, c_37])).
% 2.70/1.39  tff(c_914, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_877])).
% 2.70/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.39  
% 2.70/1.39  Inference rules
% 2.70/1.39  ----------------------
% 2.70/1.39  #Ref     : 0
% 2.70/1.39  #Sup     : 215
% 2.70/1.39  #Fact    : 2
% 2.70/1.39  #Define  : 0
% 2.70/1.39  #Split   : 0
% 2.70/1.39  #Chain   : 0
% 2.70/1.39  #Close   : 0
% 2.70/1.39  
% 2.70/1.39  Ordering : KBO
% 2.70/1.39  
% 2.70/1.39  Simplification rules
% 2.70/1.39  ----------------------
% 2.70/1.39  #Subsume      : 22
% 2.70/1.39  #Demod        : 57
% 2.70/1.39  #Tautology    : 83
% 2.70/1.39  #SimpNegUnit  : 0
% 2.70/1.39  #BackRed      : 0
% 2.70/1.39  
% 2.70/1.39  #Partial instantiations: 0
% 2.70/1.39  #Strategies tried      : 1
% 2.70/1.39  
% 2.70/1.39  Timing (in seconds)
% 2.70/1.39  ----------------------
% 2.70/1.39  Preprocessing        : 0.29
% 2.70/1.39  Parsing              : 0.16
% 2.70/1.39  CNF conversion       : 0.02
% 2.70/1.39  Main loop            : 0.33
% 2.70/1.39  Inferencing          : 0.12
% 2.70/1.39  Reduction            : 0.11
% 2.70/1.39  Demodulation         : 0.09
% 2.70/1.39  BG Simplification    : 0.02
% 2.70/1.39  Subsumption          : 0.05
% 2.70/1.39  Abstraction          : 0.02
% 2.70/1.39  MUC search           : 0.00
% 2.70/1.39  Cooper               : 0.00
% 2.70/1.39  Total                : 0.65
% 2.70/1.39  Index Insertion      : 0.00
% 2.70/1.39  Index Deletion       : 0.00
% 2.70/1.39  Index Matching       : 0.00
% 2.70/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
