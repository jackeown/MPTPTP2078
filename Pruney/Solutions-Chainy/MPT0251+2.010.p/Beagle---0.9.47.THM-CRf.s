%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:47 EST 2020

% Result     : Theorem 5.73s
% Output     : CNFRefutation 5.73s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 104 expanded)
%              Number of leaves         :   34 (  51 expanded)
%              Depth                    :   14
%              Number of atoms          :   60 ( 101 expanded)
%              Number of equality atoms :   38 (  70 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_116,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_87,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_32,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_93,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_97,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_85,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_95,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_60,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_34,plain,(
    ! [A_28] : k2_xboole_0(A_28,k1_xboole_0) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_92,plain,(
    ! [B_58,A_59] : k2_xboole_0(B_58,A_59) = k2_xboole_0(A_59,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_114,plain,(
    ! [A_59] : k2_xboole_0(k1_xboole_0,A_59) = A_59 ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_34])).

tff(c_615,plain,(
    ! [A_114,B_115] : k2_xboole_0(A_114,k4_xboole_0(B_115,A_114)) = k2_xboole_0(A_114,B_115) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_643,plain,(
    ! [B_115] : k4_xboole_0(B_115,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_615,c_114])).

tff(c_657,plain,(
    ! [B_115] : k4_xboole_0(B_115,k1_xboole_0) = B_115 ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_643])).

tff(c_150,plain,(
    ! [A_61] : k2_xboole_0(k1_xboole_0,A_61) = A_61 ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_34])).

tff(c_42,plain,(
    ! [A_35,B_36] : r1_tarski(A_35,k2_xboole_0(A_35,B_36)) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_162,plain,(
    ! [A_61] : r1_tarski(k1_xboole_0,A_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_42])).

tff(c_219,plain,(
    ! [A_67,B_68] :
      ( k3_xboole_0(A_67,B_68) = A_67
      | ~ r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_233,plain,(
    ! [A_61] : k3_xboole_0(k1_xboole_0,A_61) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_162,c_219])).

tff(c_752,plain,(
    ! [A_128,B_129] : k5_xboole_0(A_128,k3_xboole_0(A_128,B_129)) = k4_xboole_0(A_128,B_129) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1211,plain,(
    ! [A_149] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_149) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_752])).

tff(c_30,plain,(
    ! [B_25] : r1_tarski(B_25,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_235,plain,(
    ! [B_25] : k3_xboole_0(B_25,B_25) = B_25 ),
    inference(resolution,[status(thm)],[c_30,c_219])).

tff(c_773,plain,(
    ! [B_25] : k5_xboole_0(B_25,B_25) = k4_xboole_0(B_25,B_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_752])).

tff(c_1226,plain,(
    ! [A_149] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_149) ),
    inference(superposition,[status(thm),theory(equality)],[c_1211,c_773])).

tff(c_1241,plain,(
    ! [A_149] : k4_xboole_0(k1_xboole_0,A_149) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_657,c_1226])).

tff(c_808,plain,(
    ! [A_132,B_133] : k4_xboole_0(k2_xboole_0(A_132,B_133),B_133) = k4_xboole_0(A_132,B_133) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_834,plain,(
    ! [A_59] : k4_xboole_0(k1_xboole_0,A_59) = k4_xboole_0(A_59,A_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_808])).

tff(c_1248,plain,(
    ! [A_59] : k4_xboole_0(A_59,A_59) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1241,c_834])).

tff(c_1303,plain,(
    ! [B_25] : k5_xboole_0(B_25,B_25) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1248,c_773])).

tff(c_341,plain,(
    ! [A_76,B_77] :
      ( r1_tarski(k1_tarski(A_76),B_77)
      | ~ r2_hidden(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_36,plain,(
    ! [A_29,B_30] :
      ( k3_xboole_0(A_29,B_30) = A_29
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3122,plain,(
    ! [A_264,B_265] :
      ( k3_xboole_0(k1_tarski(A_264),B_265) = k1_tarski(A_264)
      | ~ r2_hidden(A_264,B_265) ) ),
    inference(resolution,[status(thm)],[c_341,c_36])).

tff(c_32,plain,(
    ! [A_26,B_27] : k5_xboole_0(A_26,k3_xboole_0(A_26,B_27)) = k4_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3156,plain,(
    ! [A_264,B_265] :
      ( k5_xboole_0(k1_tarski(A_264),k1_tarski(A_264)) = k4_xboole_0(k1_tarski(A_264),B_265)
      | ~ r2_hidden(A_264,B_265) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3122,c_32])).

tff(c_6119,plain,(
    ! [A_434,B_435] :
      ( k4_xboole_0(k1_tarski(A_434),B_435) = k1_xboole_0
      | ~ r2_hidden(A_434,B_435) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1303,c_3156])).

tff(c_38,plain,(
    ! [A_31,B_32] : k2_xboole_0(A_31,k4_xboole_0(B_32,A_31)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6159,plain,(
    ! [B_435,A_434] :
      ( k2_xboole_0(B_435,k1_tarski(A_434)) = k2_xboole_0(B_435,k1_xboole_0)
      | ~ r2_hidden(A_434,B_435) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6119,c_38])).

tff(c_6811,plain,(
    ! [B_455,A_456] :
      ( k2_xboole_0(B_455,k1_tarski(A_456)) = B_455
      | ~ r2_hidden(A_456,B_455) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_6159])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_xboole_0(B_4,A_3) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_62,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_58])).

tff(c_7085,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_6811,c_62])).

tff(c_7136,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_7085])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:27:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.73/2.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.73/2.26  
% 5.73/2.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.73/2.26  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 5.73/2.26  
% 5.73/2.26  %Foreground sorts:
% 5.73/2.26  
% 5.73/2.26  
% 5.73/2.26  %Background operators:
% 5.73/2.26  
% 5.73/2.26  
% 5.73/2.26  %Foreground operators:
% 5.73/2.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.73/2.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.73/2.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.73/2.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.73/2.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.73/2.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.73/2.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.73/2.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.73/2.26  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.73/2.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.73/2.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.73/2.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.73/2.26  tff('#skF_5', type, '#skF_5': $i).
% 5.73/2.26  tff('#skF_6', type, '#skF_6': $i).
% 5.73/2.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.73/2.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.73/2.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.73/2.26  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.73/2.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.73/2.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.73/2.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.73/2.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.73/2.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.73/2.26  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.73/2.26  
% 5.73/2.27  tff(f_116, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 5.73/2.27  tff(f_87, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 5.73/2.27  tff(f_32, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.73/2.27  tff(f_93, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.73/2.27  tff(f_97, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.73/2.27  tff(f_91, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.73/2.27  tff(f_85, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.73/2.27  tff(f_83, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.73/2.27  tff(f_95, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 5.73/2.27  tff(f_109, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 5.73/2.27  tff(c_60, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.73/2.27  tff(c_34, plain, (![A_28]: (k2_xboole_0(A_28, k1_xboole_0)=A_28)), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.73/2.27  tff(c_92, plain, (![B_58, A_59]: (k2_xboole_0(B_58, A_59)=k2_xboole_0(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.73/2.27  tff(c_114, plain, (![A_59]: (k2_xboole_0(k1_xboole_0, A_59)=A_59)), inference(superposition, [status(thm), theory('equality')], [c_92, c_34])).
% 5.73/2.27  tff(c_615, plain, (![A_114, B_115]: (k2_xboole_0(A_114, k4_xboole_0(B_115, A_114))=k2_xboole_0(A_114, B_115))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.73/2.27  tff(c_643, plain, (![B_115]: (k4_xboole_0(B_115, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_115))), inference(superposition, [status(thm), theory('equality')], [c_615, c_114])).
% 5.73/2.27  tff(c_657, plain, (![B_115]: (k4_xboole_0(B_115, k1_xboole_0)=B_115)), inference(demodulation, [status(thm), theory('equality')], [c_114, c_643])).
% 5.73/2.27  tff(c_150, plain, (![A_61]: (k2_xboole_0(k1_xboole_0, A_61)=A_61)), inference(superposition, [status(thm), theory('equality')], [c_92, c_34])).
% 5.73/2.27  tff(c_42, plain, (![A_35, B_36]: (r1_tarski(A_35, k2_xboole_0(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.73/2.27  tff(c_162, plain, (![A_61]: (r1_tarski(k1_xboole_0, A_61))), inference(superposition, [status(thm), theory('equality')], [c_150, c_42])).
% 5.73/2.27  tff(c_219, plain, (![A_67, B_68]: (k3_xboole_0(A_67, B_68)=A_67 | ~r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.73/2.27  tff(c_233, plain, (![A_61]: (k3_xboole_0(k1_xboole_0, A_61)=k1_xboole_0)), inference(resolution, [status(thm)], [c_162, c_219])).
% 5.73/2.27  tff(c_752, plain, (![A_128, B_129]: (k5_xboole_0(A_128, k3_xboole_0(A_128, B_129))=k4_xboole_0(A_128, B_129))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.73/2.27  tff(c_1211, plain, (![A_149]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_149))), inference(superposition, [status(thm), theory('equality')], [c_233, c_752])).
% 5.73/2.27  tff(c_30, plain, (![B_25]: (r1_tarski(B_25, B_25))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.73/2.27  tff(c_235, plain, (![B_25]: (k3_xboole_0(B_25, B_25)=B_25)), inference(resolution, [status(thm)], [c_30, c_219])).
% 5.73/2.27  tff(c_773, plain, (![B_25]: (k5_xboole_0(B_25, B_25)=k4_xboole_0(B_25, B_25))), inference(superposition, [status(thm), theory('equality')], [c_235, c_752])).
% 5.73/2.27  tff(c_1226, plain, (![A_149]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_149))), inference(superposition, [status(thm), theory('equality')], [c_1211, c_773])).
% 5.73/2.27  tff(c_1241, plain, (![A_149]: (k4_xboole_0(k1_xboole_0, A_149)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_657, c_1226])).
% 5.73/2.27  tff(c_808, plain, (![A_132, B_133]: (k4_xboole_0(k2_xboole_0(A_132, B_133), B_133)=k4_xboole_0(A_132, B_133))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.73/2.27  tff(c_834, plain, (![A_59]: (k4_xboole_0(k1_xboole_0, A_59)=k4_xboole_0(A_59, A_59))), inference(superposition, [status(thm), theory('equality')], [c_114, c_808])).
% 5.73/2.27  tff(c_1248, plain, (![A_59]: (k4_xboole_0(A_59, A_59)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1241, c_834])).
% 5.73/2.27  tff(c_1303, plain, (![B_25]: (k5_xboole_0(B_25, B_25)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1248, c_773])).
% 5.73/2.27  tff(c_341, plain, (![A_76, B_77]: (r1_tarski(k1_tarski(A_76), B_77) | ~r2_hidden(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.73/2.27  tff(c_36, plain, (![A_29, B_30]: (k3_xboole_0(A_29, B_30)=A_29 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.73/2.27  tff(c_3122, plain, (![A_264, B_265]: (k3_xboole_0(k1_tarski(A_264), B_265)=k1_tarski(A_264) | ~r2_hidden(A_264, B_265))), inference(resolution, [status(thm)], [c_341, c_36])).
% 5.73/2.27  tff(c_32, plain, (![A_26, B_27]: (k5_xboole_0(A_26, k3_xboole_0(A_26, B_27))=k4_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.73/2.27  tff(c_3156, plain, (![A_264, B_265]: (k5_xboole_0(k1_tarski(A_264), k1_tarski(A_264))=k4_xboole_0(k1_tarski(A_264), B_265) | ~r2_hidden(A_264, B_265))), inference(superposition, [status(thm), theory('equality')], [c_3122, c_32])).
% 5.73/2.27  tff(c_6119, plain, (![A_434, B_435]: (k4_xboole_0(k1_tarski(A_434), B_435)=k1_xboole_0 | ~r2_hidden(A_434, B_435))), inference(demodulation, [status(thm), theory('equality')], [c_1303, c_3156])).
% 5.73/2.27  tff(c_38, plain, (![A_31, B_32]: (k2_xboole_0(A_31, k4_xboole_0(B_32, A_31))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.73/2.27  tff(c_6159, plain, (![B_435, A_434]: (k2_xboole_0(B_435, k1_tarski(A_434))=k2_xboole_0(B_435, k1_xboole_0) | ~r2_hidden(A_434, B_435))), inference(superposition, [status(thm), theory('equality')], [c_6119, c_38])).
% 5.73/2.27  tff(c_6811, plain, (![B_455, A_456]: (k2_xboole_0(B_455, k1_tarski(A_456))=B_455 | ~r2_hidden(A_456, B_455))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_6159])).
% 5.73/2.27  tff(c_4, plain, (![B_4, A_3]: (k2_xboole_0(B_4, A_3)=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.73/2.27  tff(c_58, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.73/2.27  tff(c_62, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_4, c_58])).
% 5.73/2.27  tff(c_7085, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_6811, c_62])).
% 5.73/2.27  tff(c_7136, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_7085])).
% 5.73/2.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.73/2.27  
% 5.73/2.27  Inference rules
% 5.73/2.27  ----------------------
% 5.73/2.27  #Ref     : 0
% 5.73/2.27  #Sup     : 1792
% 5.73/2.27  #Fact    : 0
% 5.73/2.27  #Define  : 0
% 5.73/2.27  #Split   : 3
% 5.73/2.27  #Chain   : 0
% 5.73/2.27  #Close   : 0
% 5.73/2.27  
% 5.73/2.27  Ordering : KBO
% 5.73/2.27  
% 5.73/2.27  Simplification rules
% 5.73/2.27  ----------------------
% 5.73/2.27  #Subsume      : 696
% 5.73/2.27  #Demod        : 854
% 5.73/2.27  #Tautology    : 627
% 5.73/2.27  #SimpNegUnit  : 9
% 5.73/2.27  #BackRed      : 13
% 5.73/2.27  
% 5.73/2.27  #Partial instantiations: 0
% 5.73/2.27  #Strategies tried      : 1
% 5.73/2.27  
% 5.73/2.27  Timing (in seconds)
% 5.73/2.27  ----------------------
% 5.73/2.28  Preprocessing        : 0.34
% 5.73/2.28  Parsing              : 0.19
% 5.73/2.28  CNF conversion       : 0.02
% 5.73/2.28  Main loop            : 1.11
% 5.73/2.28  Inferencing          : 0.36
% 5.73/2.28  Reduction            : 0.42
% 5.73/2.28  Demodulation         : 0.32
% 5.73/2.28  BG Simplification    : 0.03
% 5.73/2.28  Subsumption          : 0.23
% 5.73/2.28  Abstraction          : 0.04
% 5.73/2.28  MUC search           : 0.00
% 5.73/2.28  Cooper               : 0.00
% 5.73/2.28  Total                : 1.49
% 5.73/2.28  Index Insertion      : 0.00
% 5.73/2.28  Index Deletion       : 0.00
% 5.73/2.28  Index Matching       : 0.00
% 5.73/2.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
