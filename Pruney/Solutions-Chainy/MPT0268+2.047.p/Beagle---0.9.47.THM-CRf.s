%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:40 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   62 (  83 expanded)
%              Number of leaves         :   25 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   68 ( 105 expanded)
%              Number of equality atoms :   31 (  48 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r2_hidden(C,A)
        | r1_tarski(A,k4_xboole_0(B,k1_tarski(C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l2_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_34,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_59,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_14,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_61,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(A_27,B_28) = k1_xboole_0
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_65,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_61])).

tff(c_120,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k4_xboole_0(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_138,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_120])).

tff(c_144,plain,(
    ! [A_41] : k3_xboole_0(A_41,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_138])).

tff(c_12,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_149,plain,(
    ! [A_41] : k5_xboole_0(A_41,k1_xboole_0) = k4_xboole_0(A_41,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_12])).

tff(c_153,plain,(
    ! [A_41] : k5_xboole_0(A_41,k1_xboole_0) = A_41 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_149])).

tff(c_268,plain,(
    ! [A_60,B_61,C_62] :
      ( r1_tarski(A_60,k4_xboole_0(B_61,k1_tarski(C_62)))
      | r2_hidden(C_62,A_60)
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_321,plain,(
    ! [A_70,B_71,C_72] :
      ( k4_xboole_0(A_70,k4_xboole_0(B_71,k1_tarski(C_72))) = k1_xboole_0
      | r2_hidden(C_72,A_70)
      | ~ r1_tarski(A_70,B_71) ) ),
    inference(resolution,[status(thm)],[c_268,c_10])).

tff(c_16,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_333,plain,(
    ! [B_71,C_72] :
      ( k3_xboole_0(B_71,k1_tarski(C_72)) = k1_xboole_0
      | r2_hidden(C_72,B_71)
      | ~ r1_tarski(B_71,B_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_16])).

tff(c_366,plain,(
    ! [B_73,C_74] :
      ( k3_xboole_0(B_73,k1_tarski(C_74)) = k1_xboole_0
      | r2_hidden(C_74,B_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_333])).

tff(c_379,plain,(
    ! [B_73,C_74] :
      ( k4_xboole_0(B_73,k1_tarski(C_74)) = k5_xboole_0(B_73,k1_xboole_0)
      | r2_hidden(C_74,B_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_366,c_12])).

tff(c_444,plain,(
    ! [B_78,C_79] :
      ( k4_xboole_0(B_78,k1_tarski(C_79)) = B_78
      | r2_hidden(C_79,B_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_379])).

tff(c_32,plain,
    ( k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_143,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_470,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_444,c_143])).

tff(c_493,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_470])).

tff(c_494,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_495,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_36,plain,
    ( k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1'
    | k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_576,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_495,c_36])).

tff(c_28,plain,(
    ! [C_21,B_20] : ~ r2_hidden(C_21,k4_xboole_0(B_20,k1_tarski(C_21))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_583,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_576,c_28])).

tff(c_589,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_494,c_583])).

tff(c_590,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_591,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_38,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_635,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_591,c_38])).

tff(c_639,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_635,c_28])).

tff(c_644,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_590,c_639])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:16:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.36  
% 2.42/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.36  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.42/1.36  
% 2.42/1.36  %Foreground sorts:
% 2.42/1.36  
% 2.42/1.36  
% 2.42/1.36  %Background operators:
% 2.42/1.36  
% 2.42/1.36  
% 2.42/1.36  %Foreground operators:
% 2.42/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.42/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.42/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.42/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.42/1.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.42/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.42/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.42/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.42/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.42/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.42/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.42/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.42/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.42/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.42/1.36  
% 2.56/1.38  tff(f_66, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.56/1.38  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.56/1.38  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.56/1.38  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.56/1.38  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.56/1.38  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.56/1.38  tff(f_53, axiom, (![A, B, C]: (r1_tarski(A, B) => (r2_hidden(C, A) | r1_tarski(A, k4_xboole_0(B, k1_tarski(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l2_zfmisc_1)).
% 2.56/1.38  tff(f_60, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.56/1.38  tff(c_34, plain, (~r2_hidden('#skF_2', '#skF_1') | r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.56/1.38  tff(c_59, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_34])).
% 2.56/1.38  tff(c_14, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.56/1.38  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.56/1.38  tff(c_61, plain, (![A_27, B_28]: (k4_xboole_0(A_27, B_28)=k1_xboole_0 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.56/1.38  tff(c_65, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_61])).
% 2.56/1.38  tff(c_120, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k4_xboole_0(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.56/1.38  tff(c_138, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_120])).
% 2.56/1.38  tff(c_144, plain, (![A_41]: (k3_xboole_0(A_41, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_65, c_138])).
% 2.56/1.38  tff(c_12, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.56/1.38  tff(c_149, plain, (![A_41]: (k5_xboole_0(A_41, k1_xboole_0)=k4_xboole_0(A_41, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_144, c_12])).
% 2.56/1.38  tff(c_153, plain, (![A_41]: (k5_xboole_0(A_41, k1_xboole_0)=A_41)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_149])).
% 2.56/1.38  tff(c_268, plain, (![A_60, B_61, C_62]: (r1_tarski(A_60, k4_xboole_0(B_61, k1_tarski(C_62))) | r2_hidden(C_62, A_60) | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.56/1.38  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.56/1.38  tff(c_321, plain, (![A_70, B_71, C_72]: (k4_xboole_0(A_70, k4_xboole_0(B_71, k1_tarski(C_72)))=k1_xboole_0 | r2_hidden(C_72, A_70) | ~r1_tarski(A_70, B_71))), inference(resolution, [status(thm)], [c_268, c_10])).
% 2.56/1.38  tff(c_16, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.56/1.38  tff(c_333, plain, (![B_71, C_72]: (k3_xboole_0(B_71, k1_tarski(C_72))=k1_xboole_0 | r2_hidden(C_72, B_71) | ~r1_tarski(B_71, B_71))), inference(superposition, [status(thm), theory('equality')], [c_321, c_16])).
% 2.56/1.38  tff(c_366, plain, (![B_73, C_74]: (k3_xboole_0(B_73, k1_tarski(C_74))=k1_xboole_0 | r2_hidden(C_74, B_73))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_333])).
% 2.56/1.38  tff(c_379, plain, (![B_73, C_74]: (k4_xboole_0(B_73, k1_tarski(C_74))=k5_xboole_0(B_73, k1_xboole_0) | r2_hidden(C_74, B_73))), inference(superposition, [status(thm), theory('equality')], [c_366, c_12])).
% 2.56/1.38  tff(c_444, plain, (![B_78, C_79]: (k4_xboole_0(B_78, k1_tarski(C_79))=B_78 | r2_hidden(C_79, B_78))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_379])).
% 2.56/1.38  tff(c_32, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1' | r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.56/1.38  tff(c_143, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_32])).
% 2.56/1.38  tff(c_470, plain, (r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_444, c_143])).
% 2.56/1.38  tff(c_493, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_470])).
% 2.56/1.38  tff(c_494, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_32])).
% 2.56/1.38  tff(c_495, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))='#skF_1'), inference(splitRight, [status(thm)], [c_32])).
% 2.56/1.38  tff(c_36, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1' | k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.56/1.38  tff(c_576, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_495, c_36])).
% 2.56/1.38  tff(c_28, plain, (![C_21, B_20]: (~r2_hidden(C_21, k4_xboole_0(B_20, k1_tarski(C_21))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.56/1.38  tff(c_583, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_576, c_28])).
% 2.56/1.38  tff(c_589, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_494, c_583])).
% 2.56/1.38  tff(c_590, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_34])).
% 2.56/1.38  tff(c_591, plain, (r2_hidden('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_34])).
% 2.56/1.38  tff(c_38, plain, (~r2_hidden('#skF_2', '#skF_1') | k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.56/1.38  tff(c_635, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_591, c_38])).
% 2.56/1.38  tff(c_639, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_635, c_28])).
% 2.56/1.38  tff(c_644, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_590, c_639])).
% 2.56/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.38  
% 2.56/1.38  Inference rules
% 2.56/1.38  ----------------------
% 2.56/1.38  #Ref     : 0
% 2.56/1.38  #Sup     : 142
% 2.56/1.38  #Fact    : 0
% 2.56/1.38  #Define  : 0
% 2.56/1.38  #Split   : 3
% 2.56/1.38  #Chain   : 0
% 2.56/1.38  #Close   : 0
% 2.56/1.38  
% 2.56/1.38  Ordering : KBO
% 2.56/1.38  
% 2.56/1.38  Simplification rules
% 2.56/1.38  ----------------------
% 2.56/1.38  #Subsume      : 8
% 2.56/1.38  #Demod        : 46
% 2.56/1.38  #Tautology    : 86
% 2.56/1.38  #SimpNegUnit  : 4
% 2.56/1.38  #BackRed      : 0
% 2.56/1.38  
% 2.56/1.38  #Partial instantiations: 0
% 2.56/1.38  #Strategies tried      : 1
% 2.56/1.38  
% 2.56/1.38  Timing (in seconds)
% 2.56/1.38  ----------------------
% 2.56/1.38  Preprocessing        : 0.31
% 2.56/1.38  Parsing              : 0.17
% 2.56/1.38  CNF conversion       : 0.02
% 2.56/1.38  Main loop            : 0.26
% 2.56/1.38  Inferencing          : 0.10
% 2.56/1.38  Reduction            : 0.08
% 2.56/1.38  Demodulation         : 0.05
% 2.56/1.38  BG Simplification    : 0.01
% 2.56/1.38  Subsumption          : 0.05
% 2.56/1.38  Abstraction          : 0.02
% 2.56/1.38  MUC search           : 0.00
% 2.56/1.38  Cooper               : 0.00
% 2.56/1.38  Total                : 0.60
% 2.56/1.38  Index Insertion      : 0.00
% 2.56/1.38  Index Deletion       : 0.00
% 2.56/1.38  Index Matching       : 0.00
% 2.56/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
