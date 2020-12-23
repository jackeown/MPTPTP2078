%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:38 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   61 (  74 expanded)
%              Number of leaves         :   31 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :   57 (  83 expanded)
%              Number of equality atoms :   23 (  33 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_38,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_95,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_12,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_28,plain,(
    ! [A_41,B_42] :
      ( r1_xboole_0(k1_tarski(A_41),B_42)
      | r2_hidden(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_123,plain,(
    ! [A_59,B_60,C_61] :
      ( ~ r1_xboole_0(A_59,B_60)
      | ~ r2_hidden(C_61,k3_xboole_0(A_59,B_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_135,plain,(
    ! [A_62,B_63] :
      ( ~ r1_xboole_0(A_62,B_63)
      | k3_xboole_0(A_62,B_63) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_123])).

tff(c_191,plain,(
    ! [A_74,B_75] :
      ( k3_xboole_0(k1_tarski(A_74),B_75) = k1_xboole_0
      | r2_hidden(A_74,B_75) ) ),
    inference(resolution,[status(thm)],[c_28,c_135])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_108,plain,(
    ! [A_57,B_58] : k5_xboole_0(A_57,k3_xboole_0(A_57,B_58)) = k4_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_120,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_108])).

tff(c_200,plain,(
    ! [B_75,A_74] :
      ( k4_xboole_0(B_75,k1_tarski(A_74)) = k5_xboole_0(B_75,k1_xboole_0)
      | r2_hidden(A_74,B_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_120])).

tff(c_275,plain,(
    ! [B_78,A_79] :
      ( k4_xboole_0(B_78,k1_tarski(A_79)) = B_78
      | r2_hidden(A_79,B_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_200])).

tff(c_36,plain,
    ( k4_xboole_0('#skF_3',k1_tarski('#skF_4')) != '#skF_3'
    | r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_107,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_284,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_107])).

tff(c_295,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_284])).

tff(c_296,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_297,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_40,plain,
    ( k4_xboole_0('#skF_3',k1_tarski('#skF_4')) != '#skF_3'
    | k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_476,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_40])).

tff(c_32,plain,(
    ! [C_45,B_44] : ~ r2_hidden(C_45,k4_xboole_0(B_44,k1_tarski(C_45))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_483,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_476,c_32])).

tff(c_488,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_483])).

tff(c_489,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_490,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_42,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_518,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_42])).

tff(c_522,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_518,c_32])).

tff(c_527,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_489,c_522])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:08:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.29  
% 2.11/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.29  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 2.11/1.29  
% 2.11/1.29  %Foreground sorts:
% 2.11/1.29  
% 2.11/1.29  
% 2.11/1.29  %Background operators:
% 2.11/1.29  
% 2.11/1.29  
% 2.11/1.29  %Foreground operators:
% 2.11/1.29  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.11/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.11/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.11/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.11/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.11/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.11/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.11/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.11/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.11/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.11/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.11/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.11/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.11/1.29  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.11/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.11/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.11/1.29  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.11/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.11/1.29  
% 2.11/1.30  tff(f_85, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.11/1.30  tff(f_53, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.11/1.30  tff(f_72, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.11/1.30  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.11/1.30  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.11/1.30  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.11/1.30  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.11/1.30  tff(f_79, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.11/1.30  tff(c_38, plain, (~r2_hidden('#skF_4', '#skF_3') | r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.11/1.30  tff(c_95, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_38])).
% 2.11/1.30  tff(c_12, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.11/1.30  tff(c_28, plain, (![A_41, B_42]: (r1_xboole_0(k1_tarski(A_41), B_42) | r2_hidden(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.11/1.30  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.11/1.30  tff(c_123, plain, (![A_59, B_60, C_61]: (~r1_xboole_0(A_59, B_60) | ~r2_hidden(C_61, k3_xboole_0(A_59, B_60)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.11/1.30  tff(c_135, plain, (![A_62, B_63]: (~r1_xboole_0(A_62, B_63) | k3_xboole_0(A_62, B_63)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_123])).
% 2.11/1.30  tff(c_191, plain, (![A_74, B_75]: (k3_xboole_0(k1_tarski(A_74), B_75)=k1_xboole_0 | r2_hidden(A_74, B_75))), inference(resolution, [status(thm)], [c_28, c_135])).
% 2.11/1.30  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.11/1.30  tff(c_108, plain, (![A_57, B_58]: (k5_xboole_0(A_57, k3_xboole_0(A_57, B_58))=k4_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.11/1.30  tff(c_120, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_108])).
% 2.11/1.30  tff(c_200, plain, (![B_75, A_74]: (k4_xboole_0(B_75, k1_tarski(A_74))=k5_xboole_0(B_75, k1_xboole_0) | r2_hidden(A_74, B_75))), inference(superposition, [status(thm), theory('equality')], [c_191, c_120])).
% 2.11/1.30  tff(c_275, plain, (![B_78, A_79]: (k4_xboole_0(B_78, k1_tarski(A_79))=B_78 | r2_hidden(A_79, B_78))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_200])).
% 2.11/1.30  tff(c_36, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))!='#skF_3' | r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.11/1.30  tff(c_107, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_36])).
% 2.11/1.30  tff(c_284, plain, (r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_275, c_107])).
% 2.11/1.30  tff(c_295, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_284])).
% 2.11/1.30  tff(c_296, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_36])).
% 2.11/1.30  tff(c_297, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(splitRight, [status(thm)], [c_36])).
% 2.11/1.30  tff(c_40, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))!='#skF_3' | k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.11/1.30  tff(c_476, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_297, c_40])).
% 2.11/1.30  tff(c_32, plain, (![C_45, B_44]: (~r2_hidden(C_45, k4_xboole_0(B_44, k1_tarski(C_45))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.11/1.30  tff(c_483, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_476, c_32])).
% 2.11/1.30  tff(c_488, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_296, c_483])).
% 2.11/1.30  tff(c_489, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_38])).
% 2.11/1.30  tff(c_490, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_38])).
% 2.11/1.30  tff(c_42, plain, (~r2_hidden('#skF_4', '#skF_3') | k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.11/1.30  tff(c_518, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_490, c_42])).
% 2.11/1.30  tff(c_522, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_518, c_32])).
% 2.11/1.30  tff(c_527, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_489, c_522])).
% 2.11/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.30  
% 2.11/1.30  Inference rules
% 2.11/1.30  ----------------------
% 2.11/1.30  #Ref     : 0
% 2.11/1.30  #Sup     : 118
% 2.11/1.30  #Fact    : 0
% 2.11/1.30  #Define  : 0
% 2.11/1.30  #Split   : 2
% 2.11/1.30  #Chain   : 0
% 2.11/1.30  #Close   : 0
% 2.11/1.30  
% 2.11/1.30  Ordering : KBO
% 2.11/1.30  
% 2.11/1.30  Simplification rules
% 2.11/1.30  ----------------------
% 2.11/1.30  #Subsume      : 18
% 2.11/1.30  #Demod        : 18
% 2.11/1.30  #Tautology    : 56
% 2.11/1.30  #SimpNegUnit  : 1
% 2.11/1.30  #BackRed      : 0
% 2.11/1.30  
% 2.11/1.30  #Partial instantiations: 0
% 2.11/1.30  #Strategies tried      : 1
% 2.11/1.30  
% 2.11/1.30  Timing (in seconds)
% 2.11/1.30  ----------------------
% 2.11/1.31  Preprocessing        : 0.32
% 2.11/1.31  Parsing              : 0.17
% 2.11/1.31  CNF conversion       : 0.02
% 2.11/1.31  Main loop            : 0.22
% 2.11/1.31  Inferencing          : 0.08
% 2.11/1.31  Reduction            : 0.07
% 2.11/1.31  Demodulation         : 0.05
% 2.11/1.31  BG Simplification    : 0.02
% 2.11/1.31  Subsumption          : 0.04
% 2.11/1.31  Abstraction          : 0.02
% 2.11/1.31  MUC search           : 0.00
% 2.11/1.31  Cooper               : 0.00
% 2.11/1.31  Total                : 0.57
% 2.11/1.31  Index Insertion      : 0.00
% 2.11/1.31  Index Deletion       : 0.00
% 2.11/1.31  Index Matching       : 0.00
% 2.11/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
