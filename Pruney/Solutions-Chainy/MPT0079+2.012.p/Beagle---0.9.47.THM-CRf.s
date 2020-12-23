%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:44 EST 2020

% Result     : Theorem 5.33s
% Output     : CNFRefutation 5.33s
% Verified   : 
% Statistics : Number of formulae       :   54 (  80 expanded)
%              Number of leaves         :   22 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :   53 (  97 expanded)
%              Number of equality atoms :   30 (  55 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_26,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_222,plain,(
    ! [A_37,B_38] :
      ( k3_xboole_0(A_37,B_38) = k1_xboole_0
      | ~ r1_xboole_0(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_233,plain,(
    k3_xboole_0('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_222])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_387,plain,(
    ! [A_45,B_46] : k4_xboole_0(A_45,k3_xboole_0(A_45,B_46)) = k4_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_799,plain,(
    ! [A_57,B_58] : k4_xboole_0(A_57,k3_xboole_0(B_58,A_57)) = k4_xboole_0(A_57,B_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_387])).

tff(c_848,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k4_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_799])).

tff(c_875,plain,(
    k4_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_848])).

tff(c_32,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_33,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_32])).

tff(c_51,plain,(
    ! [B_26,A_27] : k2_xboole_0(B_26,A_27) = k2_xboole_0(A_27,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [A_20,B_21] : r1_tarski(A_20,k2_xboole_0(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_66,plain,(
    ! [A_27,B_26] : r1_tarski(A_27,k2_xboole_0(B_26,A_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_24])).

tff(c_103,plain,(
    r1_tarski('#skF_2',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_66])).

tff(c_892,plain,(
    ! [A_59,B_60,C_61] :
      ( r1_tarski(k4_xboole_0(A_59,B_60),C_61)
      | ~ r1_tarski(A_59,k2_xboole_0(B_60,C_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1700,plain,(
    ! [A_80,B_81,C_82] :
      ( k2_xboole_0(k4_xboole_0(A_80,B_81),C_82) = C_82
      | ~ r1_tarski(A_80,k2_xboole_0(B_81,C_82)) ) ),
    inference(resolution,[status(thm)],[c_892,c_10])).

tff(c_1733,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2','#skF_4'),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_103,c_1700])).

tff(c_1763,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_875,c_1733])).

tff(c_30,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_234,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_222])).

tff(c_399,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_387])).

tff(c_418,plain,(
    k4_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_399])).

tff(c_6279,plain,(
    ! [C_138] :
      ( r1_tarski('#skF_3',C_138)
      | ~ r1_tarski('#skF_3',k2_xboole_0('#skF_1',C_138)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_892])).

tff(c_6321,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ r1_tarski('#skF_3',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_6279])).

tff(c_6337,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_6321])).

tff(c_6345,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_6337,c_10])).

tff(c_6348,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1763,c_6345])).

tff(c_6350,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_6348])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:56:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.33/1.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.33/2.00  
% 5.33/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.33/2.00  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.33/2.00  
% 5.33/2.00  %Foreground sorts:
% 5.33/2.00  
% 5.33/2.00  
% 5.33/2.00  %Background operators:
% 5.33/2.00  
% 5.33/2.00  
% 5.33/2.00  %Foreground operators:
% 5.33/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.33/2.00  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.33/2.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.33/2.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.33/2.00  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.33/2.00  tff('#skF_2', type, '#skF_2': $i).
% 5.33/2.00  tff('#skF_3', type, '#skF_3': $i).
% 5.33/2.00  tff('#skF_1', type, '#skF_1': $i).
% 5.33/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.33/2.00  tff('#skF_4', type, '#skF_4': $i).
% 5.33/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.33/2.00  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.33/2.00  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.33/2.00  
% 5.33/2.01  tff(f_62, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_xboole_1)).
% 5.33/2.01  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.33/2.01  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.33/2.01  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.33/2.01  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.33/2.01  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 5.33/2.01  tff(f_53, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.33/2.01  tff(f_47, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 5.33/2.01  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.33/2.01  tff(c_26, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.33/2.01  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.33/2.01  tff(c_14, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.33/2.01  tff(c_28, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.33/2.01  tff(c_222, plain, (![A_37, B_38]: (k3_xboole_0(A_37, B_38)=k1_xboole_0 | ~r1_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.33/2.01  tff(c_233, plain, (k3_xboole_0('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_222])).
% 5.33/2.01  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.33/2.01  tff(c_387, plain, (![A_45, B_46]: (k4_xboole_0(A_45, k3_xboole_0(A_45, B_46))=k4_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.33/2.01  tff(c_799, plain, (![A_57, B_58]: (k4_xboole_0(A_57, k3_xboole_0(B_58, A_57))=k4_xboole_0(A_57, B_58))), inference(superposition, [status(thm), theory('equality')], [c_4, c_387])).
% 5.33/2.01  tff(c_848, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k4_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_233, c_799])).
% 5.33/2.01  tff(c_875, plain, (k4_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_848])).
% 5.33/2.01  tff(c_32, plain, (k2_xboole_0('#skF_3', '#skF_4')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.33/2.01  tff(c_33, plain, (k2_xboole_0('#skF_1', '#skF_2')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_32])).
% 5.33/2.01  tff(c_51, plain, (![B_26, A_27]: (k2_xboole_0(B_26, A_27)=k2_xboole_0(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.33/2.01  tff(c_24, plain, (![A_20, B_21]: (r1_tarski(A_20, k2_xboole_0(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.33/2.01  tff(c_66, plain, (![A_27, B_26]: (r1_tarski(A_27, k2_xboole_0(B_26, A_27)))), inference(superposition, [status(thm), theory('equality')], [c_51, c_24])).
% 5.33/2.01  tff(c_103, plain, (r1_tarski('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_33, c_66])).
% 5.33/2.01  tff(c_892, plain, (![A_59, B_60, C_61]: (r1_tarski(k4_xboole_0(A_59, B_60), C_61) | ~r1_tarski(A_59, k2_xboole_0(B_60, C_61)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.33/2.01  tff(c_10, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.33/2.01  tff(c_1700, plain, (![A_80, B_81, C_82]: (k2_xboole_0(k4_xboole_0(A_80, B_81), C_82)=C_82 | ~r1_tarski(A_80, k2_xboole_0(B_81, C_82)))), inference(resolution, [status(thm)], [c_892, c_10])).
% 5.33/2.01  tff(c_1733, plain, (k2_xboole_0(k4_xboole_0('#skF_2', '#skF_4'), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_103, c_1700])).
% 5.33/2.01  tff(c_1763, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_875, c_1733])).
% 5.33/2.01  tff(c_30, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.33/2.01  tff(c_234, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_222])).
% 5.33/2.01  tff(c_399, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_234, c_387])).
% 5.33/2.01  tff(c_418, plain, (k4_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_399])).
% 5.33/2.01  tff(c_6279, plain, (![C_138]: (r1_tarski('#skF_3', C_138) | ~r1_tarski('#skF_3', k2_xboole_0('#skF_1', C_138)))), inference(superposition, [status(thm), theory('equality')], [c_418, c_892])).
% 5.33/2.01  tff(c_6321, plain, (r1_tarski('#skF_3', '#skF_2') | ~r1_tarski('#skF_3', k2_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_33, c_6279])).
% 5.33/2.01  tff(c_6337, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_6321])).
% 5.33/2.01  tff(c_6345, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_6337, c_10])).
% 5.33/2.01  tff(c_6348, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1763, c_6345])).
% 5.33/2.01  tff(c_6350, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_6348])).
% 5.33/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.33/2.01  
% 5.33/2.01  Inference rules
% 5.33/2.01  ----------------------
% 5.33/2.01  #Ref     : 0
% 5.33/2.01  #Sup     : 1592
% 5.33/2.01  #Fact    : 0
% 5.33/2.01  #Define  : 0
% 5.33/2.01  #Split   : 2
% 5.33/2.01  #Chain   : 0
% 5.33/2.01  #Close   : 0
% 5.33/2.01  
% 5.33/2.01  Ordering : KBO
% 5.33/2.01  
% 5.33/2.01  Simplification rules
% 5.33/2.01  ----------------------
% 5.33/2.01  #Subsume      : 24
% 5.33/2.01  #Demod        : 1757
% 5.33/2.01  #Tautology    : 1224
% 5.33/2.01  #SimpNegUnit  : 1
% 5.33/2.01  #BackRed      : 0
% 5.33/2.01  
% 5.33/2.01  #Partial instantiations: 0
% 5.33/2.01  #Strategies tried      : 1
% 5.33/2.01  
% 5.33/2.01  Timing (in seconds)
% 5.33/2.01  ----------------------
% 5.33/2.01  Preprocessing        : 0.29
% 5.33/2.01  Parsing              : 0.16
% 5.33/2.01  CNF conversion       : 0.02
% 5.33/2.01  Main loop            : 0.97
% 5.33/2.01  Inferencing          : 0.27
% 5.33/2.01  Reduction            : 0.46
% 5.33/2.01  Demodulation         : 0.39
% 5.33/2.01  BG Simplification    : 0.03
% 5.33/2.01  Subsumption          : 0.15
% 5.33/2.01  Abstraction          : 0.04
% 5.33/2.01  MUC search           : 0.00
% 5.33/2.01  Cooper               : 0.00
% 5.33/2.01  Total                : 1.28
% 5.33/2.01  Index Insertion      : 0.00
% 5.33/2.01  Index Deletion       : 0.00
% 5.33/2.01  Index Matching       : 0.00
% 5.33/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
