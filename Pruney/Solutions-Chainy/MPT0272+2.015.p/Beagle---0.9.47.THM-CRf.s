%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:08 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   56 (  84 expanded)
%              Number of leaves         :   28 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :   50 (  79 expanded)
%              Number of equality atoms :   31 (  60 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
        | k4_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_8,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_193,plain,(
    ! [A_60,B_61] : k5_xboole_0(A_60,k3_xboole_0(A_60,B_61)) = k4_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_211,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = k4_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_193])).

tff(c_225,plain,(
    ! [A_65] : k4_xboole_0(A_65,k1_xboole_0) = A_65 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_211])).

tff(c_10,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_231,plain,(
    ! [A_65] : k4_xboole_0(A_65,A_65) = k3_xboole_0(A_65,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_10])).

tff(c_236,plain,(
    ! [A_65] : k4_xboole_0(A_65,A_65) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_231])).

tff(c_215,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_211])).

tff(c_269,plain,(
    ! [A_67] : k4_xboole_0(A_67,A_67) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_231])).

tff(c_281,plain,(
    ! [A_67] : k4_xboole_0(A_67,k1_xboole_0) = k3_xboole_0(A_67,A_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_10])).

tff(c_298,plain,(
    ! [A_68] : k3_xboole_0(A_68,A_68) = A_68 ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_281])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_304,plain,(
    ! [A_68] : k5_xboole_0(A_68,A_68) = k4_xboole_0(A_68,A_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_4])).

tff(c_325,plain,(
    ! [A_68] : k5_xboole_0(A_68,A_68) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_304])).

tff(c_149,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(k1_tarski(A_48),B_49)
      | ~ r2_hidden(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_397,plain,(
    ! [A_76,B_77] :
      ( k3_xboole_0(k1_tarski(A_76),B_77) = k1_tarski(A_76)
      | ~ r2_hidden(A_76,B_77) ) ),
    inference(resolution,[status(thm)],[c_149,c_6])).

tff(c_410,plain,(
    ! [A_76,B_77] :
      ( k5_xboole_0(k1_tarski(A_76),k1_tarski(A_76)) = k4_xboole_0(k1_tarski(A_76),B_77)
      | ~ r2_hidden(A_76,B_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_4])).

tff(c_455,plain,(
    ! [A_84,B_85] :
      ( k4_xboole_0(k1_tarski(A_84),B_85) = k1_xboole_0
      | ~ r2_hidden(A_84,B_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_410])).

tff(c_38,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_498,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_455,c_38])).

tff(c_34,plain,(
    ! [A_36,B_37] :
      ( r1_xboole_0(k1_tarski(A_36),B_37)
      | r2_hidden(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_169,plain,(
    ! [A_56,B_57] :
      ( k4_xboole_0(A_56,B_57) = A_56
      | ~ r1_xboole_0(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_510,plain,(
    ! [A_92,B_93] :
      ( k4_xboole_0(k1_tarski(A_92),B_93) = k1_tarski(A_92)
      | r2_hidden(A_92,B_93) ) ),
    inference(resolution,[status(thm)],[c_34,c_169])).

tff(c_36,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_534,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_36])).

tff(c_562,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_498,c_534])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:15:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.28  
% 2.11/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.28  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.11/1.28  
% 2.11/1.28  %Foreground sorts:
% 2.11/1.28  
% 2.11/1.28  
% 2.11/1.28  %Background operators:
% 2.11/1.28  
% 2.11/1.28  
% 2.11/1.28  %Foreground operators:
% 2.11/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.11/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.11/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.11/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.11/1.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.11/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.11/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.11/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.11/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.11/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.11/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.11/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.11/1.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.11/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.11/1.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.11/1.28  
% 2.11/1.29  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.11/1.29  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.11/1.29  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.11/1.29  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.11/1.29  tff(f_59, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.11/1.29  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.11/1.29  tff(f_69, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) | (k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 2.11/1.29  tff(f_64, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.11/1.29  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.11/1.29  tff(c_8, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.11/1.29  tff(c_12, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.11/1.29  tff(c_193, plain, (![A_60, B_61]: (k5_xboole_0(A_60, k3_xboole_0(A_60, B_61))=k4_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.11/1.29  tff(c_211, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=k4_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_193])).
% 2.11/1.29  tff(c_225, plain, (![A_65]: (k4_xboole_0(A_65, k1_xboole_0)=A_65)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_211])).
% 2.11/1.29  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.11/1.29  tff(c_231, plain, (![A_65]: (k4_xboole_0(A_65, A_65)=k3_xboole_0(A_65, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_225, c_10])).
% 2.11/1.29  tff(c_236, plain, (![A_65]: (k4_xboole_0(A_65, A_65)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_231])).
% 2.11/1.29  tff(c_215, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_211])).
% 2.11/1.29  tff(c_269, plain, (![A_67]: (k4_xboole_0(A_67, A_67)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_231])).
% 2.11/1.29  tff(c_281, plain, (![A_67]: (k4_xboole_0(A_67, k1_xboole_0)=k3_xboole_0(A_67, A_67))), inference(superposition, [status(thm), theory('equality')], [c_269, c_10])).
% 2.11/1.29  tff(c_298, plain, (![A_68]: (k3_xboole_0(A_68, A_68)=A_68)), inference(demodulation, [status(thm), theory('equality')], [c_215, c_281])).
% 2.11/1.29  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.11/1.29  tff(c_304, plain, (![A_68]: (k5_xboole_0(A_68, A_68)=k4_xboole_0(A_68, A_68))), inference(superposition, [status(thm), theory('equality')], [c_298, c_4])).
% 2.11/1.29  tff(c_325, plain, (![A_68]: (k5_xboole_0(A_68, A_68)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_236, c_304])).
% 2.11/1.29  tff(c_149, plain, (![A_48, B_49]: (r1_tarski(k1_tarski(A_48), B_49) | ~r2_hidden(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.11/1.29  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.11/1.29  tff(c_397, plain, (![A_76, B_77]: (k3_xboole_0(k1_tarski(A_76), B_77)=k1_tarski(A_76) | ~r2_hidden(A_76, B_77))), inference(resolution, [status(thm)], [c_149, c_6])).
% 2.11/1.29  tff(c_410, plain, (![A_76, B_77]: (k5_xboole_0(k1_tarski(A_76), k1_tarski(A_76))=k4_xboole_0(k1_tarski(A_76), B_77) | ~r2_hidden(A_76, B_77))), inference(superposition, [status(thm), theory('equality')], [c_397, c_4])).
% 2.11/1.29  tff(c_455, plain, (![A_84, B_85]: (k4_xboole_0(k1_tarski(A_84), B_85)=k1_xboole_0 | ~r2_hidden(A_84, B_85))), inference(demodulation, [status(thm), theory('equality')], [c_325, c_410])).
% 2.11/1.29  tff(c_38, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.11/1.29  tff(c_498, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_455, c_38])).
% 2.11/1.29  tff(c_34, plain, (![A_36, B_37]: (r1_xboole_0(k1_tarski(A_36), B_37) | r2_hidden(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.11/1.29  tff(c_169, plain, (![A_56, B_57]: (k4_xboole_0(A_56, B_57)=A_56 | ~r1_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.11/1.29  tff(c_510, plain, (![A_92, B_93]: (k4_xboole_0(k1_tarski(A_92), B_93)=k1_tarski(A_92) | r2_hidden(A_92, B_93))), inference(resolution, [status(thm)], [c_34, c_169])).
% 2.11/1.29  tff(c_36, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.11/1.29  tff(c_534, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_510, c_36])).
% 2.11/1.29  tff(c_562, plain, $false, inference(negUnitSimplification, [status(thm)], [c_498, c_534])).
% 2.11/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.29  
% 2.11/1.29  Inference rules
% 2.11/1.29  ----------------------
% 2.11/1.29  #Ref     : 0
% 2.11/1.29  #Sup     : 123
% 2.11/1.29  #Fact    : 0
% 2.11/1.29  #Define  : 0
% 2.11/1.29  #Split   : 0
% 2.11/1.29  #Chain   : 0
% 2.11/1.29  #Close   : 0
% 2.11/1.29  
% 2.11/1.29  Ordering : KBO
% 2.11/1.29  
% 2.11/1.29  Simplification rules
% 2.11/1.29  ----------------------
% 2.11/1.29  #Subsume      : 5
% 2.11/1.30  #Demod        : 32
% 2.11/1.30  #Tautology    : 87
% 2.11/1.30  #SimpNegUnit  : 1
% 2.11/1.30  #BackRed      : 0
% 2.11/1.30  
% 2.11/1.30  #Partial instantiations: 0
% 2.11/1.30  #Strategies tried      : 1
% 2.11/1.30  
% 2.11/1.30  Timing (in seconds)
% 2.11/1.30  ----------------------
% 2.11/1.30  Preprocessing        : 0.31
% 2.11/1.30  Parsing              : 0.17
% 2.11/1.30  CNF conversion       : 0.02
% 2.11/1.30  Main loop            : 0.23
% 2.11/1.30  Inferencing          : 0.10
% 2.11/1.30  Reduction            : 0.07
% 2.11/1.30  Demodulation         : 0.06
% 2.11/1.30  BG Simplification    : 0.01
% 2.11/1.30  Subsumption          : 0.03
% 2.11/1.30  Abstraction          : 0.02
% 2.11/1.30  MUC search           : 0.00
% 2.11/1.30  Cooper               : 0.00
% 2.11/1.30  Total                : 0.56
% 2.11/1.30  Index Insertion      : 0.00
% 2.11/1.30  Index Deletion       : 0.00
% 2.11/1.30  Index Matching       : 0.00
% 2.11/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
