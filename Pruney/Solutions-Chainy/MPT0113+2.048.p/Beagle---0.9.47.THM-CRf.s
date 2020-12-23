%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:17 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   53 (  66 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   51 (  76 expanded)
%              Number of equality atoms :   24 (  30 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_81,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(A_30,B_31)
      | k4_xboole_0(A_30,B_31) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_40,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_85,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_81,c_40])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_36,plain,(
    ! [A_25,B_26] : r1_tarski(k3_xboole_0(A_25,B_26),A_25) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_39,plain,(
    ! [A_3] : r1_tarski(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_36])).

tff(c_100,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_125,plain,(
    ! [A_36] : k4_xboole_0(A_36,A_36) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_39,c_100])).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_tarski(k4_xboole_0(A_13,B_14),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_165,plain,(
    ! [A_40] : r1_tarski(k1_xboole_0,A_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_16])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_174,plain,(
    ! [A_41] : k3_xboole_0(k1_xboole_0,A_41) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_165,c_14])).

tff(c_202,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_174])).

tff(c_123,plain,(
    ! [A_13,B_14] : k4_xboole_0(k4_xboole_0(A_13,B_14),A_13) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_100])).

tff(c_24,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_138,plain,(
    ! [A_37,B_38] :
      ( k3_xboole_0(A_37,B_38) = A_37
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_163,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_24,c_138])).

tff(c_481,plain,(
    ! [A_53,B_54,C_55] : k4_xboole_0(k3_xboole_0(A_53,B_54),C_55) = k3_xboole_0(A_53,k4_xboole_0(B_54,C_55)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_628,plain,(
    ! [C_59] : k3_xboole_0('#skF_1',k4_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_59)) = k4_xboole_0('#skF_1',C_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_481])).

tff(c_664,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_628])).

tff(c_675,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_664])).

tff(c_677,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_675])).

tff(c_678,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_804,plain,(
    ! [A_71,B_72] :
      ( k3_xboole_0(A_71,B_72) = A_71
      | ~ r1_tarski(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_837,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_24,c_804])).

tff(c_1092,plain,(
    ! [A_80,B_81,C_82] : k4_xboole_0(k3_xboole_0(A_80,B_81),C_82) = k3_xboole_0(A_80,k4_xboole_0(B_81,C_82)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [A_18,B_19] : r1_xboole_0(k4_xboole_0(A_18,B_19),B_19) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1418,plain,(
    ! [A_92,B_93,C_94] : r1_xboole_0(k3_xboole_0(A_92,k4_xboole_0(B_93,C_94)),C_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_1092,c_20])).

tff(c_1445,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_837,c_1418])).

tff(c_1475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_678,c_1445])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:48:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.39  
% 2.76/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.39  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.76/1.39  
% 2.76/1.39  %Foreground sorts:
% 2.76/1.39  
% 2.76/1.39  
% 2.76/1.39  %Background operators:
% 2.76/1.39  
% 2.76/1.39  
% 2.76/1.39  %Foreground operators:
% 2.76/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.76/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.76/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.76/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.76/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.76/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.76/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.76/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.76/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.76/1.39  
% 2.76/1.41  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.76/1.41  tff(f_54, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.76/1.41  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.76/1.41  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.76/1.41  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.76/1.41  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.76/1.41  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.76/1.41  tff(f_45, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.76/1.41  tff(f_47, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.76/1.41  tff(c_81, plain, (![A_30, B_31]: (r1_tarski(A_30, B_31) | k4_xboole_0(A_30, B_31)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.76/1.41  tff(c_22, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.76/1.41  tff(c_40, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_22])).
% 2.76/1.41  tff(c_85, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_81, c_40])).
% 2.76/1.41  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.76/1.41  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.76/1.41  tff(c_36, plain, (![A_25, B_26]: (r1_tarski(k3_xboole_0(A_25, B_26), A_25))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.76/1.41  tff(c_39, plain, (![A_3]: (r1_tarski(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_36])).
% 2.76/1.41  tff(c_100, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.76/1.41  tff(c_125, plain, (![A_36]: (k4_xboole_0(A_36, A_36)=k1_xboole_0)), inference(resolution, [status(thm)], [c_39, c_100])).
% 2.76/1.41  tff(c_16, plain, (![A_13, B_14]: (r1_tarski(k4_xboole_0(A_13, B_14), A_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.76/1.41  tff(c_165, plain, (![A_40]: (r1_tarski(k1_xboole_0, A_40))), inference(superposition, [status(thm), theory('equality')], [c_125, c_16])).
% 2.76/1.41  tff(c_14, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.76/1.41  tff(c_174, plain, (![A_41]: (k3_xboole_0(k1_xboole_0, A_41)=k1_xboole_0)), inference(resolution, [status(thm)], [c_165, c_14])).
% 2.76/1.41  tff(c_202, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_174])).
% 2.76/1.41  tff(c_123, plain, (![A_13, B_14]: (k4_xboole_0(k4_xboole_0(A_13, B_14), A_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_100])).
% 2.76/1.41  tff(c_24, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.76/1.41  tff(c_138, plain, (![A_37, B_38]: (k3_xboole_0(A_37, B_38)=A_37 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.76/1.41  tff(c_163, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_24, c_138])).
% 2.76/1.41  tff(c_481, plain, (![A_53, B_54, C_55]: (k4_xboole_0(k3_xboole_0(A_53, B_54), C_55)=k3_xboole_0(A_53, k4_xboole_0(B_54, C_55)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.76/1.41  tff(c_628, plain, (![C_59]: (k3_xboole_0('#skF_1', k4_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_59))=k4_xboole_0('#skF_1', C_59))), inference(superposition, [status(thm), theory('equality')], [c_163, c_481])).
% 2.76/1.41  tff(c_664, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_123, c_628])).
% 2.76/1.41  tff(c_675, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_202, c_664])).
% 2.76/1.41  tff(c_677, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_675])).
% 2.76/1.41  tff(c_678, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_22])).
% 2.76/1.41  tff(c_804, plain, (![A_71, B_72]: (k3_xboole_0(A_71, B_72)=A_71 | ~r1_tarski(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.76/1.41  tff(c_837, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_24, c_804])).
% 2.76/1.41  tff(c_1092, plain, (![A_80, B_81, C_82]: (k4_xboole_0(k3_xboole_0(A_80, B_81), C_82)=k3_xboole_0(A_80, k4_xboole_0(B_81, C_82)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.76/1.41  tff(c_20, plain, (![A_18, B_19]: (r1_xboole_0(k4_xboole_0(A_18, B_19), B_19))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.76/1.41  tff(c_1418, plain, (![A_92, B_93, C_94]: (r1_xboole_0(k3_xboole_0(A_92, k4_xboole_0(B_93, C_94)), C_94))), inference(superposition, [status(thm), theory('equality')], [c_1092, c_20])).
% 2.76/1.41  tff(c_1445, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_837, c_1418])).
% 2.76/1.41  tff(c_1475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_678, c_1445])).
% 2.76/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.41  
% 2.76/1.41  Inference rules
% 2.76/1.41  ----------------------
% 2.76/1.41  #Ref     : 0
% 2.76/1.41  #Sup     : 372
% 2.76/1.41  #Fact    : 0
% 2.76/1.41  #Define  : 0
% 2.76/1.41  #Split   : 1
% 2.76/1.41  #Chain   : 0
% 2.76/1.41  #Close   : 0
% 2.76/1.41  
% 2.76/1.41  Ordering : KBO
% 2.76/1.41  
% 2.76/1.41  Simplification rules
% 2.76/1.41  ----------------------
% 2.76/1.41  #Subsume      : 0
% 2.76/1.41  #Demod        : 193
% 2.76/1.41  #Tautology    : 281
% 2.76/1.41  #SimpNegUnit  : 2
% 2.76/1.41  #BackRed      : 0
% 2.76/1.41  
% 2.76/1.41  #Partial instantiations: 0
% 2.76/1.41  #Strategies tried      : 1
% 2.76/1.41  
% 2.76/1.41  Timing (in seconds)
% 2.76/1.41  ----------------------
% 2.76/1.41  Preprocessing        : 0.28
% 2.76/1.41  Parsing              : 0.15
% 2.76/1.41  CNF conversion       : 0.02
% 2.76/1.41  Main loop            : 0.36
% 2.76/1.41  Inferencing          : 0.13
% 2.76/1.41  Reduction            : 0.14
% 2.76/1.41  Demodulation         : 0.11
% 2.76/1.41  BG Simplification    : 0.02
% 2.76/1.41  Subsumption          : 0.05
% 2.76/1.41  Abstraction          : 0.02
% 2.76/1.41  MUC search           : 0.00
% 2.76/1.41  Cooper               : 0.00
% 2.76/1.41  Total                : 0.67
% 2.76/1.41  Index Insertion      : 0.00
% 2.76/1.41  Index Deletion       : 0.00
% 2.76/1.41  Index Matching       : 0.00
% 2.76/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
