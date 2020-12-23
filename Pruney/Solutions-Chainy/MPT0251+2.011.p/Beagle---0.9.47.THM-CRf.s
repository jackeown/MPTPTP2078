%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:47 EST 2020

% Result     : Theorem 3.82s
% Output     : CNFRefutation 4.04s
% Verified   : 
% Statistics : Number of formulae       :   70 (  98 expanded)
%              Number of leaves         :   34 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :   59 (  93 expanded)
%              Number of equality atoms :   38 (  64 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_112,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_79,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_32,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_87,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_85,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_89,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_105,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_74,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_44,plain,(
    ! [A_26] : k2_xboole_0(A_26,k1_xboole_0) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_108,plain,(
    ! [B_59,A_60] : k2_xboole_0(B_59,A_60) = k2_xboole_0(A_60,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_124,plain,(
    ! [A_60] : k2_xboole_0(k1_xboole_0,A_60) = A_60 ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_44])).

tff(c_587,plain,(
    ! [A_117,B_118] : k2_xboole_0(A_117,k4_xboole_0(B_118,A_117)) = k2_xboole_0(A_117,B_118) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_597,plain,(
    ! [B_118] : k4_xboole_0(B_118,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_587,c_124])).

tff(c_636,plain,(
    ! [B_119] : k4_xboole_0(B_119,k1_xboole_0) = B_119 ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_597])).

tff(c_48,plain,(
    ! [A_29] : r1_tarski(k1_xboole_0,A_29) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_203,plain,(
    ! [A_65,B_66] :
      ( k3_xboole_0(A_65,B_66) = A_65
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_210,plain,(
    ! [A_29] : k3_xboole_0(k1_xboole_0,A_29) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_203])).

tff(c_359,plain,(
    ! [A_100,B_101] : k5_xboole_0(A_100,k3_xboole_0(A_100,B_101)) = k4_xboole_0(A_100,B_101) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_408,plain,(
    ! [A_105] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_359])).

tff(c_371,plain,(
    ! [A_29] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_359])).

tff(c_411,plain,(
    ! [A_29,A_105] : k4_xboole_0(k1_xboole_0,A_29) = k4_xboole_0(k1_xboole_0,A_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_371])).

tff(c_646,plain,(
    ! [A_105] : k4_xboole_0(k1_xboole_0,A_105) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_636,c_411])).

tff(c_374,plain,(
    ! [A_102,B_103] : k4_xboole_0(k2_xboole_0(A_102,B_103),B_103) = k4_xboole_0(A_102,B_103) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_386,plain,(
    ! [A_60] : k4_xboole_0(k1_xboole_0,A_60) = k4_xboole_0(A_60,A_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_374])).

tff(c_677,plain,(
    ! [A_60] : k4_xboole_0(A_60,A_60) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_646,c_386])).

tff(c_40,plain,(
    ! [B_23] : r1_tarski(B_23,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_211,plain,(
    ! [B_23] : k3_xboole_0(B_23,B_23) = B_23 ),
    inference(resolution,[status(thm)],[c_40,c_203])).

tff(c_368,plain,(
    ! [B_23] : k5_xboole_0(B_23,B_23) = k4_xboole_0(B_23,B_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_359])).

tff(c_723,plain,(
    ! [B_23] : k5_xboole_0(B_23,B_23) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_677,c_368])).

tff(c_282,plain,(
    ! [A_79,B_80] :
      ( r1_tarski(k1_tarski(A_79),B_80)
      | ~ r2_hidden(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_46,plain,(
    ! [A_27,B_28] :
      ( k3_xboole_0(A_27,B_28) = A_27
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1509,plain,(
    ! [A_181,B_182] :
      ( k3_xboole_0(k1_tarski(A_181),B_182) = k1_tarski(A_181)
      | ~ r2_hidden(A_181,B_182) ) ),
    inference(resolution,[status(thm)],[c_282,c_46])).

tff(c_42,plain,(
    ! [A_24,B_25] : k5_xboole_0(A_24,k3_xboole_0(A_24,B_25)) = k4_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1521,plain,(
    ! [A_181,B_182] :
      ( k5_xboole_0(k1_tarski(A_181),k1_tarski(A_181)) = k4_xboole_0(k1_tarski(A_181),B_182)
      | ~ r2_hidden(A_181,B_182) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1509,c_42])).

tff(c_1685,plain,(
    ! [A_192,B_193] :
      ( k4_xboole_0(k1_tarski(A_192),B_193) = k1_xboole_0
      | ~ r2_hidden(A_192,B_193) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_723,c_1521])).

tff(c_50,plain,(
    ! [A_30,B_31] : k2_xboole_0(A_30,k4_xboole_0(B_31,A_30)) = k2_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1719,plain,(
    ! [B_193,A_192] :
      ( k2_xboole_0(B_193,k1_tarski(A_192)) = k2_xboole_0(B_193,k1_xboole_0)
      | ~ r2_hidden(A_192,B_193) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1685,c_50])).

tff(c_2570,plain,(
    ! [B_217,A_218] :
      ( k2_xboole_0(B_217,k1_tarski(A_218)) = B_217
      | ~ r2_hidden(A_218,B_217) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1719])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_xboole_0(B_4,A_3) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_72,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_76,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_72])).

tff(c_2625,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2570,c_76])).

tff(c_2668,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2625])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:03:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.82/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/1.69  
% 4.04/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/1.69  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 4.04/1.69  
% 4.04/1.69  %Foreground sorts:
% 4.04/1.69  
% 4.04/1.69  
% 4.04/1.69  %Background operators:
% 4.04/1.69  
% 4.04/1.69  
% 4.04/1.69  %Foreground operators:
% 4.04/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.04/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.04/1.69  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.04/1.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.04/1.69  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.04/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.04/1.69  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.04/1.69  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.04/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.04/1.69  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.04/1.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.04/1.69  tff('#skF_5', type, '#skF_5': $i).
% 4.04/1.69  tff('#skF_6', type, '#skF_6': $i).
% 4.04/1.69  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.04/1.69  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.04/1.69  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.04/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.04/1.69  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.04/1.69  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.04/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.04/1.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.04/1.69  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.04/1.69  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.04/1.69  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.04/1.69  
% 4.04/1.71  tff(f_112, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 4.04/1.71  tff(f_79, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.04/1.71  tff(f_32, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.04/1.71  tff(f_87, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.04/1.71  tff(f_85, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.04/1.71  tff(f_83, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.04/1.71  tff(f_77, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.04/1.71  tff(f_89, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 4.04/1.71  tff(f_75, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.04/1.71  tff(f_105, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.04/1.71  tff(c_74, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.04/1.71  tff(c_44, plain, (![A_26]: (k2_xboole_0(A_26, k1_xboole_0)=A_26)), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.04/1.71  tff(c_108, plain, (![B_59, A_60]: (k2_xboole_0(B_59, A_60)=k2_xboole_0(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.04/1.71  tff(c_124, plain, (![A_60]: (k2_xboole_0(k1_xboole_0, A_60)=A_60)), inference(superposition, [status(thm), theory('equality')], [c_108, c_44])).
% 4.04/1.71  tff(c_587, plain, (![A_117, B_118]: (k2_xboole_0(A_117, k4_xboole_0(B_118, A_117))=k2_xboole_0(A_117, B_118))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.04/1.71  tff(c_597, plain, (![B_118]: (k4_xboole_0(B_118, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_118))), inference(superposition, [status(thm), theory('equality')], [c_587, c_124])).
% 4.04/1.71  tff(c_636, plain, (![B_119]: (k4_xboole_0(B_119, k1_xboole_0)=B_119)), inference(demodulation, [status(thm), theory('equality')], [c_124, c_597])).
% 4.04/1.71  tff(c_48, plain, (![A_29]: (r1_tarski(k1_xboole_0, A_29))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.04/1.71  tff(c_203, plain, (![A_65, B_66]: (k3_xboole_0(A_65, B_66)=A_65 | ~r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.04/1.71  tff(c_210, plain, (![A_29]: (k3_xboole_0(k1_xboole_0, A_29)=k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_203])).
% 4.04/1.71  tff(c_359, plain, (![A_100, B_101]: (k5_xboole_0(A_100, k3_xboole_0(A_100, B_101))=k4_xboole_0(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.04/1.71  tff(c_408, plain, (![A_105]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_105))), inference(superposition, [status(thm), theory('equality')], [c_210, c_359])).
% 4.04/1.71  tff(c_371, plain, (![A_29]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_29))), inference(superposition, [status(thm), theory('equality')], [c_210, c_359])).
% 4.04/1.71  tff(c_411, plain, (![A_29, A_105]: (k4_xboole_0(k1_xboole_0, A_29)=k4_xboole_0(k1_xboole_0, A_105))), inference(superposition, [status(thm), theory('equality')], [c_408, c_371])).
% 4.04/1.71  tff(c_646, plain, (![A_105]: (k4_xboole_0(k1_xboole_0, A_105)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_636, c_411])).
% 4.04/1.71  tff(c_374, plain, (![A_102, B_103]: (k4_xboole_0(k2_xboole_0(A_102, B_103), B_103)=k4_xboole_0(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.04/1.71  tff(c_386, plain, (![A_60]: (k4_xboole_0(k1_xboole_0, A_60)=k4_xboole_0(A_60, A_60))), inference(superposition, [status(thm), theory('equality')], [c_124, c_374])).
% 4.04/1.71  tff(c_677, plain, (![A_60]: (k4_xboole_0(A_60, A_60)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_646, c_386])).
% 4.04/1.71  tff(c_40, plain, (![B_23]: (r1_tarski(B_23, B_23))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.04/1.71  tff(c_211, plain, (![B_23]: (k3_xboole_0(B_23, B_23)=B_23)), inference(resolution, [status(thm)], [c_40, c_203])).
% 4.04/1.71  tff(c_368, plain, (![B_23]: (k5_xboole_0(B_23, B_23)=k4_xboole_0(B_23, B_23))), inference(superposition, [status(thm), theory('equality')], [c_211, c_359])).
% 4.04/1.71  tff(c_723, plain, (![B_23]: (k5_xboole_0(B_23, B_23)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_677, c_368])).
% 4.04/1.71  tff(c_282, plain, (![A_79, B_80]: (r1_tarski(k1_tarski(A_79), B_80) | ~r2_hidden(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.04/1.71  tff(c_46, plain, (![A_27, B_28]: (k3_xboole_0(A_27, B_28)=A_27 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.04/1.71  tff(c_1509, plain, (![A_181, B_182]: (k3_xboole_0(k1_tarski(A_181), B_182)=k1_tarski(A_181) | ~r2_hidden(A_181, B_182))), inference(resolution, [status(thm)], [c_282, c_46])).
% 4.04/1.71  tff(c_42, plain, (![A_24, B_25]: (k5_xboole_0(A_24, k3_xboole_0(A_24, B_25))=k4_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.04/1.71  tff(c_1521, plain, (![A_181, B_182]: (k5_xboole_0(k1_tarski(A_181), k1_tarski(A_181))=k4_xboole_0(k1_tarski(A_181), B_182) | ~r2_hidden(A_181, B_182))), inference(superposition, [status(thm), theory('equality')], [c_1509, c_42])).
% 4.04/1.71  tff(c_1685, plain, (![A_192, B_193]: (k4_xboole_0(k1_tarski(A_192), B_193)=k1_xboole_0 | ~r2_hidden(A_192, B_193))), inference(demodulation, [status(thm), theory('equality')], [c_723, c_1521])).
% 4.04/1.71  tff(c_50, plain, (![A_30, B_31]: (k2_xboole_0(A_30, k4_xboole_0(B_31, A_30))=k2_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.04/1.71  tff(c_1719, plain, (![B_193, A_192]: (k2_xboole_0(B_193, k1_tarski(A_192))=k2_xboole_0(B_193, k1_xboole_0) | ~r2_hidden(A_192, B_193))), inference(superposition, [status(thm), theory('equality')], [c_1685, c_50])).
% 4.04/1.71  tff(c_2570, plain, (![B_217, A_218]: (k2_xboole_0(B_217, k1_tarski(A_218))=B_217 | ~r2_hidden(A_218, B_217))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1719])).
% 4.04/1.71  tff(c_4, plain, (![B_4, A_3]: (k2_xboole_0(B_4, A_3)=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.04/1.71  tff(c_72, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.04/1.71  tff(c_76, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_4, c_72])).
% 4.04/1.71  tff(c_2625, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2570, c_76])).
% 4.04/1.71  tff(c_2668, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_2625])).
% 4.04/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/1.71  
% 4.04/1.71  Inference rules
% 4.04/1.71  ----------------------
% 4.04/1.71  #Ref     : 0
% 4.04/1.71  #Sup     : 622
% 4.04/1.71  #Fact    : 0
% 4.04/1.71  #Define  : 0
% 4.04/1.71  #Split   : 1
% 4.04/1.71  #Chain   : 0
% 4.04/1.71  #Close   : 0
% 4.04/1.71  
% 4.04/1.71  Ordering : KBO
% 4.04/1.71  
% 4.04/1.71  Simplification rules
% 4.04/1.71  ----------------------
% 4.04/1.71  #Subsume      : 69
% 4.04/1.71  #Demod        : 455
% 4.04/1.71  #Tautology    : 390
% 4.04/1.71  #SimpNegUnit  : 1
% 4.04/1.71  #BackRed      : 5
% 4.04/1.71  
% 4.04/1.71  #Partial instantiations: 0
% 4.04/1.71  #Strategies tried      : 1
% 4.04/1.71  
% 4.04/1.71  Timing (in seconds)
% 4.04/1.71  ----------------------
% 4.04/1.71  Preprocessing        : 0.33
% 4.04/1.71  Parsing              : 0.18
% 4.04/1.71  CNF conversion       : 0.02
% 4.04/1.71  Main loop            : 0.59
% 4.04/1.71  Inferencing          : 0.20
% 4.04/1.71  Reduction            : 0.22
% 4.04/1.71  Demodulation         : 0.18
% 4.04/1.71  BG Simplification    : 0.03
% 4.04/1.71  Subsumption          : 0.10
% 4.04/1.71  Abstraction          : 0.03
% 4.04/1.71  MUC search           : 0.00
% 4.04/1.71  Cooper               : 0.00
% 4.04/1.71  Total                : 0.96
% 4.04/1.71  Index Insertion      : 0.00
% 4.04/1.71  Index Deletion       : 0.00
% 4.04/1.71  Index Matching       : 0.00
% 4.04/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
