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
% DateTime   : Thu Dec  3 09:44:33 EST 2020

% Result     : Theorem 10.09s
% Output     : CNFRefutation 10.09s
% Verified   : 
% Statistics : Number of formulae       :   52 (  79 expanded)
%              Number of leaves         :   18 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :   56 (  94 expanded)
%              Number of equality atoms :   35 (  56 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(A,C) )
       => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_192,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,B_29)
      | k4_xboole_0(A_28,B_29) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ~ r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_200,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_192,c_18])).

tff(c_314,plain,(
    ! [A_38,B_39,C_40] : k4_xboole_0(k4_xboole_0(A_38,B_39),C_40) = k4_xboole_0(A_38,k2_xboole_0(B_39,C_40)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_32,plain,(
    ! [A_14,B_15] : r1_tarski(k4_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_35,plain,(
    ! [A_7] : r1_tarski(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_32])).

tff(c_38,plain,(
    ! [A_19,B_20] :
      ( k4_xboole_0(A_19,B_20) = k1_xboole_0
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_35,c_38])).

tff(c_337,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k2_xboole_0(B_39,k4_xboole_0(A_38,B_39))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_48])).

tff(c_344,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k2_xboole_0(B_39,k1_xboole_0)) = k4_xboole_0(A_38,B_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_10])).

tff(c_667,plain,(
    ! [A_48,B_49] : k4_xboole_0(A_48,k2_xboole_0(B_49,k1_xboole_0)) = k4_xboole_0(A_48,B_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_10])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_201,plain,(
    ! [A_30,B_31] :
      ( k2_xboole_0(A_30,B_31) = B_31
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_217,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,B_2) = B_2
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_201])).

tff(c_15237,plain,(
    ! [A_221,B_222] :
      ( k2_xboole_0(A_221,k2_xboole_0(B_222,k1_xboole_0)) = k2_xboole_0(B_222,k1_xboole_0)
      | k4_xboole_0(A_221,B_222) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_667,c_217])).

tff(c_62,plain,(
    ! [A_21] : k4_xboole_0(A_21,A_21) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_35,c_38])).

tff(c_8,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_83,plain,(
    ! [A_22] : r1_tarski(k1_xboole_0,A_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_8])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_87,plain,(
    ! [A_22] : k4_xboole_0(k1_xboole_0,A_22) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_83,c_4])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_50,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_38])).

tff(c_372,plain,(
    ! [C_40] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_40)) = k4_xboole_0(k1_xboole_0,C_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_314])).

tff(c_387,plain,(
    ! [C_40] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_40)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_372])).

tff(c_15453,plain,(
    ! [B_222] :
      ( k4_xboole_0('#skF_1',k2_xboole_0(B_222,k1_xboole_0)) = k1_xboole_0
      | k4_xboole_0('#skF_2',B_222) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15237,c_387])).

tff(c_16483,plain,(
    ! [B_228] :
      ( k4_xboole_0('#skF_1',B_228) = k1_xboole_0
      | k4_xboole_0('#skF_2',B_228) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_15453])).

tff(c_31885,plain,(
    ! [B_319] : k4_xboole_0('#skF_1',k2_xboole_0(B_319,k4_xboole_0('#skF_2',B_319))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_16483])).

tff(c_20,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_171,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(A_26,B_27) = A_26
      | ~ r1_xboole_0(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_179,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_20,c_171])).

tff(c_353,plain,(
    ! [C_40] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_3',C_40)) = k4_xboole_0('#skF_1',C_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_314])).

tff(c_32031,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_31885,c_353])).

tff(c_32233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_200,c_32031])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:31:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.09/4.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.09/4.18  
% 10.09/4.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.09/4.18  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 10.09/4.18  
% 10.09/4.18  %Foreground sorts:
% 10.09/4.18  
% 10.09/4.18  
% 10.09/4.18  %Background operators:
% 10.09/4.18  
% 10.09/4.18  
% 10.09/4.18  %Foreground operators:
% 10.09/4.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.09/4.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.09/4.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.09/4.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.09/4.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.09/4.18  tff('#skF_2', type, '#skF_2': $i).
% 10.09/4.18  tff('#skF_3', type, '#skF_3': $i).
% 10.09/4.18  tff('#skF_1', type, '#skF_1': $i).
% 10.09/4.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.09/4.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.09/4.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.09/4.18  
% 10.09/4.20  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 10.09/4.20  tff(f_50, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 10.09/4.20  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 10.09/4.20  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 10.09/4.20  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 10.09/4.20  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 10.09/4.20  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 10.09/4.20  tff(c_192, plain, (![A_28, B_29]: (r1_tarski(A_28, B_29) | k4_xboole_0(A_28, B_29)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.09/4.20  tff(c_18, plain, (~r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.09/4.20  tff(c_200, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_192, c_18])).
% 10.09/4.20  tff(c_314, plain, (![A_38, B_39, C_40]: (k4_xboole_0(k4_xboole_0(A_38, B_39), C_40)=k4_xboole_0(A_38, k2_xboole_0(B_39, C_40)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.09/4.20  tff(c_10, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.09/4.20  tff(c_32, plain, (![A_14, B_15]: (r1_tarski(k4_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.09/4.20  tff(c_35, plain, (![A_7]: (r1_tarski(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_32])).
% 10.09/4.20  tff(c_38, plain, (![A_19, B_20]: (k4_xboole_0(A_19, B_20)=k1_xboole_0 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.09/4.20  tff(c_48, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_35, c_38])).
% 10.09/4.20  tff(c_337, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k2_xboole_0(B_39, k4_xboole_0(A_38, B_39)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_314, c_48])).
% 10.09/4.20  tff(c_344, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k2_xboole_0(B_39, k1_xboole_0))=k4_xboole_0(A_38, B_39))), inference(superposition, [status(thm), theory('equality')], [c_314, c_10])).
% 10.09/4.20  tff(c_667, plain, (![A_48, B_49]: (k4_xboole_0(A_48, k2_xboole_0(B_49, k1_xboole_0))=k4_xboole_0(A_48, B_49))), inference(superposition, [status(thm), theory('equality')], [c_314, c_10])).
% 10.09/4.20  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.09/4.20  tff(c_201, plain, (![A_30, B_31]: (k2_xboole_0(A_30, B_31)=B_31 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.09/4.20  tff(c_217, plain, (![A_1, B_2]: (k2_xboole_0(A_1, B_2)=B_2 | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_201])).
% 10.09/4.20  tff(c_15237, plain, (![A_221, B_222]: (k2_xboole_0(A_221, k2_xboole_0(B_222, k1_xboole_0))=k2_xboole_0(B_222, k1_xboole_0) | k4_xboole_0(A_221, B_222)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_667, c_217])).
% 10.09/4.20  tff(c_62, plain, (![A_21]: (k4_xboole_0(A_21, A_21)=k1_xboole_0)), inference(resolution, [status(thm)], [c_35, c_38])).
% 10.09/4.20  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.09/4.20  tff(c_83, plain, (![A_22]: (r1_tarski(k1_xboole_0, A_22))), inference(superposition, [status(thm), theory('equality')], [c_62, c_8])).
% 10.09/4.20  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.09/4.20  tff(c_87, plain, (![A_22]: (k4_xboole_0(k1_xboole_0, A_22)=k1_xboole_0)), inference(resolution, [status(thm)], [c_83, c_4])).
% 10.09/4.20  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.09/4.20  tff(c_50, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_38])).
% 10.09/4.20  tff(c_372, plain, (![C_40]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_40))=k4_xboole_0(k1_xboole_0, C_40))), inference(superposition, [status(thm), theory('equality')], [c_50, c_314])).
% 10.09/4.20  tff(c_387, plain, (![C_40]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_40))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_87, c_372])).
% 10.09/4.20  tff(c_15453, plain, (![B_222]: (k4_xboole_0('#skF_1', k2_xboole_0(B_222, k1_xboole_0))=k1_xboole_0 | k4_xboole_0('#skF_2', B_222)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_15237, c_387])).
% 10.09/4.20  tff(c_16483, plain, (![B_228]: (k4_xboole_0('#skF_1', B_228)=k1_xboole_0 | k4_xboole_0('#skF_2', B_228)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_344, c_15453])).
% 10.09/4.20  tff(c_31885, plain, (![B_319]: (k4_xboole_0('#skF_1', k2_xboole_0(B_319, k4_xboole_0('#skF_2', B_319)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_337, c_16483])).
% 10.09/4.20  tff(c_20, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.09/4.20  tff(c_171, plain, (![A_26, B_27]: (k4_xboole_0(A_26, B_27)=A_26 | ~r1_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.09/4.20  tff(c_179, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_20, c_171])).
% 10.09/4.20  tff(c_353, plain, (![C_40]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', C_40))=k4_xboole_0('#skF_1', C_40))), inference(superposition, [status(thm), theory('equality')], [c_179, c_314])).
% 10.09/4.20  tff(c_32031, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_31885, c_353])).
% 10.09/4.20  tff(c_32233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_200, c_32031])).
% 10.09/4.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.09/4.20  
% 10.09/4.20  Inference rules
% 10.09/4.20  ----------------------
% 10.09/4.20  #Ref     : 0
% 10.09/4.20  #Sup     : 7877
% 10.09/4.20  #Fact    : 0
% 10.09/4.20  #Define  : 0
% 10.09/4.20  #Split   : 2
% 10.09/4.20  #Chain   : 0
% 10.09/4.20  #Close   : 0
% 10.09/4.20  
% 10.09/4.20  Ordering : KBO
% 10.09/4.20  
% 10.09/4.20  Simplification rules
% 10.09/4.20  ----------------------
% 10.09/4.20  #Subsume      : 1722
% 10.09/4.20  #Demod        : 6152
% 10.09/4.20  #Tautology    : 4077
% 10.09/4.20  #SimpNegUnit  : 261
% 10.09/4.20  #BackRed      : 6
% 10.09/4.20  
% 10.09/4.20  #Partial instantiations: 0
% 10.09/4.20  #Strategies tried      : 1
% 10.09/4.20  
% 10.09/4.20  Timing (in seconds)
% 10.09/4.20  ----------------------
% 10.09/4.20  Preprocessing        : 0.25
% 10.09/4.20  Parsing              : 0.14
% 10.09/4.20  CNF conversion       : 0.02
% 10.09/4.20  Main loop            : 3.19
% 10.09/4.20  Inferencing          : 0.63
% 10.09/4.20  Reduction            : 1.69
% 10.09/4.20  Demodulation         : 1.42
% 10.09/4.20  BG Simplification    : 0.07
% 10.09/4.20  Subsumption          : 0.65
% 10.09/4.20  Abstraction          : 0.11
% 10.09/4.20  MUC search           : 0.00
% 10.09/4.20  Cooper               : 0.00
% 10.09/4.20  Total                : 3.47
% 10.09/4.20  Index Insertion      : 0.00
% 10.09/4.20  Index Deletion       : 0.00
% 10.09/4.20  Index Matching       : 0.00
% 10.09/4.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
