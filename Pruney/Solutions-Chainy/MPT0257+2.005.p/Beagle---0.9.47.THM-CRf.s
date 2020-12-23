%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:05 EST 2020

% Result     : Theorem 10.24s
% Output     : CNFRefutation 10.40s
% Verified   : 
% Statistics : Number of formulae       :   54 (  68 expanded)
%              Number of leaves         :   25 (  33 expanded)
%              Depth                    :   15
%              Number of atoms          :   55 (  73 expanded)
%              Number of equality atoms :   28 (  38 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_69,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_84,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

tff(c_36,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    ! [A_26,B_27] :
      ( k2_xboole_0(k1_tarski(A_26),B_27) = B_27
      | ~ r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_14,plain,(
    ! [A_13,B_14] : k2_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    ! [A_22] : r1_xboole_0(A_22,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_136,plain,(
    ! [A_43,B_44] :
      ( k4_xboole_0(A_43,B_44) = A_43
      | ~ r1_xboole_0(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_144,plain,(
    ! [A_22] : k4_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(resolution,[status(thm)],[c_22,c_136])).

tff(c_256,plain,(
    ! [A_59,B_60] : k4_xboole_0(A_59,k4_xboole_0(A_59,B_60)) = k3_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_201,plain,(
    ! [A_52,B_53] :
      ( r2_hidden('#skF_1'(A_52,B_53),A_52)
      | r1_xboole_0(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_124,plain,(
    ! [A_40,B_41] :
      ( ~ r2_hidden(A_40,B_41)
      | ~ r1_xboole_0(k1_tarski(A_40),B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_134,plain,(
    ! [A_40] : ~ r2_hidden(A_40,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_124])).

tff(c_207,plain,(
    ! [B_54] : r1_xboole_0(k1_xboole_0,B_54) ),
    inference(resolution,[status(thm)],[c_201,c_134])).

tff(c_24,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,B_24) = A_23
      | ~ r1_xboole_0(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_211,plain,(
    ! [B_54] : k4_xboole_0(k1_xboole_0,B_54) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_207,c_24])).

tff(c_292,plain,(
    ! [B_61] : k3_xboole_0(k1_xboole_0,B_61) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_211])).

tff(c_322,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_292])).

tff(c_285,plain,(
    ! [A_22] : k4_xboole_0(A_22,A_22) = k3_xboole_0(A_22,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_256])).

tff(c_433,plain,(
    ! [A_69] : k4_xboole_0(A_69,A_69) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_285])).

tff(c_20,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_438,plain,(
    ! [A_69] : k4_xboole_0(A_69,k1_xboole_0) = k3_xboole_0(A_69,A_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_433,c_20])).

tff(c_456,plain,(
    ! [A_69] : k3_xboole_0(A_69,A_69) = A_69 ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_438])).

tff(c_536,plain,(
    ! [A_72,B_73,C_74] : k2_xboole_0(k3_xboole_0(A_72,B_73),k3_xboole_0(A_72,C_74)) = k3_xboole_0(A_72,k2_xboole_0(B_73,C_74)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_557,plain,(
    ! [A_69,C_74] : k3_xboole_0(A_69,k2_xboole_0(A_69,C_74)) = k2_xboole_0(A_69,k3_xboole_0(A_69,C_74)) ),
    inference(superposition,[status(thm),theory(equality)],[c_456,c_536])).

tff(c_670,plain,(
    ! [A_83,C_84] : k3_xboole_0(A_83,k2_xboole_0(A_83,C_84)) = A_83 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_557])).

tff(c_24839,plain,(
    ! [A_495,B_496] :
      ( k3_xboole_0(k1_tarski(A_495),B_496) = k1_tarski(A_495)
      | ~ r2_hidden(A_495,B_496) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_670])).

tff(c_25715,plain,(
    ! [B_501,A_502] :
      ( k3_xboole_0(B_501,k1_tarski(A_502)) = k1_tarski(A_502)
      | ~ r2_hidden(A_502,B_501) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_24839])).

tff(c_34,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_3')) != k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_26035,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_25715,c_34])).

tff(c_26150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_26035])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:58:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.24/4.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.24/4.33  
% 10.24/4.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.24/4.33  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 10.24/4.33  
% 10.24/4.33  %Foreground sorts:
% 10.24/4.33  
% 10.24/4.33  
% 10.24/4.33  %Background operators:
% 10.24/4.33  
% 10.24/4.33  
% 10.24/4.33  %Foreground operators:
% 10.24/4.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.24/4.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.24/4.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.24/4.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.24/4.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.24/4.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.24/4.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.24/4.33  tff('#skF_3', type, '#skF_3': $i).
% 10.24/4.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.24/4.33  tff('#skF_4', type, '#skF_4': $i).
% 10.24/4.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.24/4.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.24/4.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.24/4.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.24/4.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.24/4.33  
% 10.40/4.35  tff(f_89, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_zfmisc_1)).
% 10.40/4.35  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.40/4.35  tff(f_79, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 10.40/4.35  tff(f_61, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 10.40/4.35  tff(f_69, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 10.40/4.35  tff(f_73, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 10.40/4.35  tff(f_67, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.40/4.35  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 10.40/4.35  tff(f_84, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 10.40/4.35  tff(f_63, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 10.40/4.35  tff(c_36, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.40/4.35  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.40/4.35  tff(c_30, plain, (![A_26, B_27]: (k2_xboole_0(k1_tarski(A_26), B_27)=B_27 | ~r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.40/4.35  tff(c_14, plain, (![A_13, B_14]: (k2_xboole_0(A_13, k3_xboole_0(A_13, B_14))=A_13)), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.40/4.35  tff(c_22, plain, (![A_22]: (r1_xboole_0(A_22, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.40/4.35  tff(c_136, plain, (![A_43, B_44]: (k4_xboole_0(A_43, B_44)=A_43 | ~r1_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.40/4.35  tff(c_144, plain, (![A_22]: (k4_xboole_0(A_22, k1_xboole_0)=A_22)), inference(resolution, [status(thm)], [c_22, c_136])).
% 10.40/4.35  tff(c_256, plain, (![A_59, B_60]: (k4_xboole_0(A_59, k4_xboole_0(A_59, B_60))=k3_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.40/4.35  tff(c_201, plain, (![A_52, B_53]: (r2_hidden('#skF_1'(A_52, B_53), A_52) | r1_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.40/4.35  tff(c_124, plain, (![A_40, B_41]: (~r2_hidden(A_40, B_41) | ~r1_xboole_0(k1_tarski(A_40), B_41))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.40/4.35  tff(c_134, plain, (![A_40]: (~r2_hidden(A_40, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_124])).
% 10.40/4.35  tff(c_207, plain, (![B_54]: (r1_xboole_0(k1_xboole_0, B_54))), inference(resolution, [status(thm)], [c_201, c_134])).
% 10.40/4.35  tff(c_24, plain, (![A_23, B_24]: (k4_xboole_0(A_23, B_24)=A_23 | ~r1_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.40/4.35  tff(c_211, plain, (![B_54]: (k4_xboole_0(k1_xboole_0, B_54)=k1_xboole_0)), inference(resolution, [status(thm)], [c_207, c_24])).
% 10.40/4.35  tff(c_292, plain, (![B_61]: (k3_xboole_0(k1_xboole_0, B_61)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_256, c_211])).
% 10.40/4.35  tff(c_322, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_292])).
% 10.40/4.35  tff(c_285, plain, (![A_22]: (k4_xboole_0(A_22, A_22)=k3_xboole_0(A_22, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_144, c_256])).
% 10.40/4.35  tff(c_433, plain, (![A_69]: (k4_xboole_0(A_69, A_69)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_322, c_285])).
% 10.40/4.35  tff(c_20, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.40/4.35  tff(c_438, plain, (![A_69]: (k4_xboole_0(A_69, k1_xboole_0)=k3_xboole_0(A_69, A_69))), inference(superposition, [status(thm), theory('equality')], [c_433, c_20])).
% 10.40/4.35  tff(c_456, plain, (![A_69]: (k3_xboole_0(A_69, A_69)=A_69)), inference(demodulation, [status(thm), theory('equality')], [c_144, c_438])).
% 10.40/4.35  tff(c_536, plain, (![A_72, B_73, C_74]: (k2_xboole_0(k3_xboole_0(A_72, B_73), k3_xboole_0(A_72, C_74))=k3_xboole_0(A_72, k2_xboole_0(B_73, C_74)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.40/4.35  tff(c_557, plain, (![A_69, C_74]: (k3_xboole_0(A_69, k2_xboole_0(A_69, C_74))=k2_xboole_0(A_69, k3_xboole_0(A_69, C_74)))), inference(superposition, [status(thm), theory('equality')], [c_456, c_536])).
% 10.40/4.35  tff(c_670, plain, (![A_83, C_84]: (k3_xboole_0(A_83, k2_xboole_0(A_83, C_84))=A_83)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_557])).
% 10.40/4.35  tff(c_24839, plain, (![A_495, B_496]: (k3_xboole_0(k1_tarski(A_495), B_496)=k1_tarski(A_495) | ~r2_hidden(A_495, B_496))), inference(superposition, [status(thm), theory('equality')], [c_30, c_670])).
% 10.40/4.35  tff(c_25715, plain, (![B_501, A_502]: (k3_xboole_0(B_501, k1_tarski(A_502))=k1_tarski(A_502) | ~r2_hidden(A_502, B_501))), inference(superposition, [status(thm), theory('equality')], [c_2, c_24839])).
% 10.40/4.35  tff(c_34, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_3'))!=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.40/4.35  tff(c_26035, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_25715, c_34])).
% 10.40/4.35  tff(c_26150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_26035])).
% 10.40/4.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.40/4.35  
% 10.40/4.35  Inference rules
% 10.40/4.35  ----------------------
% 10.40/4.35  #Ref     : 1
% 10.40/4.35  #Sup     : 7005
% 10.40/4.35  #Fact    : 0
% 10.40/4.35  #Define  : 0
% 10.40/4.35  #Split   : 0
% 10.40/4.35  #Chain   : 0
% 10.40/4.35  #Close   : 0
% 10.40/4.35  
% 10.40/4.35  Ordering : KBO
% 10.40/4.35  
% 10.40/4.35  Simplification rules
% 10.40/4.35  ----------------------
% 10.40/4.35  #Subsume      : 2855
% 10.40/4.35  #Demod        : 3369
% 10.40/4.35  #Tautology    : 2223
% 10.40/4.35  #SimpNegUnit  : 94
% 10.40/4.35  #BackRed      : 0
% 10.40/4.35  
% 10.40/4.35  #Partial instantiations: 0
% 10.40/4.35  #Strategies tried      : 1
% 10.40/4.35  
% 10.40/4.35  Timing (in seconds)
% 10.40/4.35  ----------------------
% 10.40/4.35  Preprocessing        : 0.30
% 10.40/4.35  Parsing              : 0.16
% 10.40/4.35  CNF conversion       : 0.02
% 10.40/4.35  Main loop            : 3.28
% 10.40/4.35  Inferencing          : 0.68
% 10.40/4.35  Reduction            : 1.59
% 10.40/4.35  Demodulation         : 1.35
% 10.40/4.35  BG Simplification    : 0.08
% 10.40/4.35  Subsumption          : 0.76
% 10.40/4.35  Abstraction          : 0.13
% 10.40/4.35  MUC search           : 0.00
% 10.40/4.35  Cooper               : 0.00
% 10.40/4.35  Total                : 3.60
% 10.40/4.35  Index Insertion      : 0.00
% 10.40/4.35  Index Deletion       : 0.00
% 10.40/4.35  Index Matching       : 0.00
% 10.40/4.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
