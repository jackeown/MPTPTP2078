%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:37 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   55 (  68 expanded)
%              Number of leaves         :   27 (  35 expanded)
%              Depth                    :    6
%              Number of atoms          :   49 (  75 expanded)
%              Number of equality atoms :   22 (  32 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_34,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_90,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_10,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_107,plain,(
    ! [A_46,B_47] :
      ( r1_xboole_0(k1_tarski(A_46),B_47)
      | r2_hidden(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_111,plain,(
    ! [A_46,B_47] :
      ( k3_xboole_0(k1_tarski(A_46),B_47) = k1_xboole_0
      | r2_hidden(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_107,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_113,plain,(
    ! [A_48,B_49] : k5_xboole_0(A_48,k3_xboole_0(A_48,B_49)) = k4_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_164,plain,(
    ! [A_55,B_56] : k5_xboole_0(A_55,k3_xboole_0(B_56,A_55)) = k4_xboole_0(A_55,B_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_113])).

tff(c_177,plain,(
    ! [B_47,A_46] :
      ( k4_xboole_0(B_47,k1_tarski(A_46)) = k5_xboole_0(B_47,k1_xboole_0)
      | r2_hidden(A_46,B_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_164])).

tff(c_237,plain,(
    ! [B_59,A_60] :
      ( k4_xboole_0(B_59,k1_tarski(A_60)) = B_59
      | r2_hidden(A_60,B_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_177])).

tff(c_32,plain,
    ( k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_112,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_243,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_112])).

tff(c_254,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_243])).

tff(c_255,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_256,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_36,plain,
    ( k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1'
    | k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_343,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_36])).

tff(c_28,plain,(
    ! [C_33,B_32] : ~ r2_hidden(C_33,k4_xboole_0(B_32,k1_tarski(C_33))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_350,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_28])).

tff(c_355,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_350])).

tff(c_356,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_357,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_38,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_395,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_38])).

tff(c_399,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_395,c_28])).

tff(c_404,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_399])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:57:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.28  
% 2.20/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.29  %$ r2_hidden > r1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.20/1.29  
% 2.20/1.29  %Foreground sorts:
% 2.20/1.29  
% 2.20/1.29  
% 2.20/1.29  %Background operators:
% 2.20/1.29  
% 2.20/1.29  
% 2.20/1.29  %Foreground operators:
% 2.20/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.20/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.20/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.20/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.20/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.20/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.20/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.20/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.20/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.20/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.20/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.20/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.20/1.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.20/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.20/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.20/1.29  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.20/1.29  
% 2.20/1.30  tff(f_65, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.20/1.30  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.20/1.30  tff(f_52, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.20/1.30  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.20/1.30  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.20/1.30  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.20/1.30  tff(f_59, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.20/1.30  tff(c_34, plain, (~r2_hidden('#skF_2', '#skF_1') | r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.20/1.30  tff(c_90, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_34])).
% 2.20/1.30  tff(c_10, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.20/1.30  tff(c_107, plain, (![A_46, B_47]: (r1_xboole_0(k1_tarski(A_46), B_47) | r2_hidden(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.20/1.30  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.20/1.30  tff(c_111, plain, (![A_46, B_47]: (k3_xboole_0(k1_tarski(A_46), B_47)=k1_xboole_0 | r2_hidden(A_46, B_47))), inference(resolution, [status(thm)], [c_107, c_4])).
% 2.20/1.30  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.20/1.30  tff(c_113, plain, (![A_48, B_49]: (k5_xboole_0(A_48, k3_xboole_0(A_48, B_49))=k4_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.20/1.30  tff(c_164, plain, (![A_55, B_56]: (k5_xboole_0(A_55, k3_xboole_0(B_56, A_55))=k4_xboole_0(A_55, B_56))), inference(superposition, [status(thm), theory('equality')], [c_2, c_113])).
% 2.20/1.30  tff(c_177, plain, (![B_47, A_46]: (k4_xboole_0(B_47, k1_tarski(A_46))=k5_xboole_0(B_47, k1_xboole_0) | r2_hidden(A_46, B_47))), inference(superposition, [status(thm), theory('equality')], [c_111, c_164])).
% 2.20/1.30  tff(c_237, plain, (![B_59, A_60]: (k4_xboole_0(B_59, k1_tarski(A_60))=B_59 | r2_hidden(A_60, B_59))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_177])).
% 2.20/1.30  tff(c_32, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1' | r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.20/1.30  tff(c_112, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_32])).
% 2.20/1.30  tff(c_243, plain, (r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_237, c_112])).
% 2.20/1.30  tff(c_254, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_243])).
% 2.20/1.30  tff(c_255, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_32])).
% 2.20/1.30  tff(c_256, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))='#skF_1'), inference(splitRight, [status(thm)], [c_32])).
% 2.20/1.30  tff(c_36, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1' | k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.20/1.30  tff(c_343, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_256, c_36])).
% 2.20/1.30  tff(c_28, plain, (![C_33, B_32]: (~r2_hidden(C_33, k4_xboole_0(B_32, k1_tarski(C_33))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.20/1.30  tff(c_350, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_343, c_28])).
% 2.20/1.30  tff(c_355, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_255, c_350])).
% 2.20/1.30  tff(c_356, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_34])).
% 2.20/1.30  tff(c_357, plain, (r2_hidden('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_34])).
% 2.20/1.30  tff(c_38, plain, (~r2_hidden('#skF_2', '#skF_1') | k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.20/1.30  tff(c_395, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_357, c_38])).
% 2.20/1.30  tff(c_399, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_395, c_28])).
% 2.20/1.30  tff(c_404, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_356, c_399])).
% 2.20/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.30  
% 2.20/1.30  Inference rules
% 2.20/1.30  ----------------------
% 2.20/1.30  #Ref     : 0
% 2.20/1.30  #Sup     : 87
% 2.20/1.30  #Fact    : 0
% 2.20/1.30  #Define  : 0
% 2.20/1.30  #Split   : 2
% 2.20/1.30  #Chain   : 0
% 2.20/1.30  #Close   : 0
% 2.20/1.30  
% 2.20/1.30  Ordering : KBO
% 2.20/1.30  
% 2.20/1.30  Simplification rules
% 2.20/1.30  ----------------------
% 2.20/1.30  #Subsume      : 8
% 2.20/1.30  #Demod        : 16
% 2.20/1.30  #Tautology    : 55
% 2.20/1.30  #SimpNegUnit  : 1
% 2.20/1.30  #BackRed      : 0
% 2.20/1.30  
% 2.20/1.30  #Partial instantiations: 0
% 2.20/1.30  #Strategies tried      : 1
% 2.20/1.30  
% 2.20/1.30  Timing (in seconds)
% 2.20/1.30  ----------------------
% 2.20/1.30  Preprocessing        : 0.34
% 2.20/1.30  Parsing              : 0.17
% 2.20/1.30  CNF conversion       : 0.02
% 2.20/1.30  Main loop            : 0.20
% 2.20/1.30  Inferencing          : 0.07
% 2.20/1.30  Reduction            : 0.06
% 2.20/1.30  Demodulation         : 0.04
% 2.20/1.30  BG Simplification    : 0.02
% 2.20/1.30  Subsumption          : 0.03
% 2.20/1.30  Abstraction          : 0.02
% 2.20/1.30  MUC search           : 0.00
% 2.20/1.30  Cooper               : 0.00
% 2.20/1.30  Total                : 0.56
% 2.20/1.30  Index Insertion      : 0.00
% 2.20/1.30  Index Deletion       : 0.00
% 2.20/1.30  Index Matching       : 0.00
% 2.20/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
