%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:23 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   53 (  70 expanded)
%              Number of leaves         :   20 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   52 (  85 expanded)
%              Number of equality atoms :   29 (  38 expanded)
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

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
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

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(c_1053,plain,(
    ! [A_72,B_73] :
      ( r1_xboole_0(A_72,B_73)
      | k4_xboole_0(A_72,B_73) != A_72 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_40,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(A_21,B_22)
      | k4_xboole_0(A_21,B_22) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_39,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_44,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_39])).

tff(c_12,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_34,plain,(
    ! [A_18,B_19] : r1_tarski(k4_xboole_0(A_18,B_19),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_37,plain,(
    ! [A_9] : r1_tarski(A_9,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_34])).

tff(c_45,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,B_24) = k1_xboole_0
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_60,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_37,c_45])).

tff(c_239,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k4_xboole_0(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_280,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_239])).

tff(c_289,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_280])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_61,plain,(
    ! [A_7,B_8] : k4_xboole_0(k4_xboole_0(A_7,B_8),A_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_45])).

tff(c_24,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_188,plain,(
    ! [A_34,B_35] :
      ( k3_xboole_0(A_34,B_35) = A_34
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_206,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_24,c_188])).

tff(c_396,plain,(
    ! [A_47,B_48,C_49] : k4_xboole_0(k3_xboole_0(A_47,B_48),C_49) = k3_xboole_0(A_47,k4_xboole_0(B_48,C_49)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_844,plain,(
    ! [C_62] : k3_xboole_0('#skF_1',k4_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_62)) = k4_xboole_0('#skF_1',C_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_396])).

tff(c_882,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_844])).

tff(c_898,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_882])).

tff(c_900,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_898])).

tff(c_901,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_1061,plain,(
    k4_xboole_0('#skF_1','#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_1053,c_901])).

tff(c_902,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_1067,plain,(
    ! [A_76,B_77] :
      ( k3_xboole_0(A_76,B_77) = A_76
      | ~ r1_tarski(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1088,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_902,c_1067])).

tff(c_1328,plain,(
    ! [A_90,B_91,C_92] : k4_xboole_0(k3_xboole_0(A_90,B_91),C_92) = k3_xboole_0(A_90,k4_xboole_0(B_91,C_92)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1771,plain,(
    ! [C_104] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_104)) = k4_xboole_0('#skF_1',C_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_1088,c_1328])).

tff(c_1089,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_24,c_1067])).

tff(c_1793,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1771,c_1089])).

tff(c_1825,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1061,c_1793])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:52:55 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.41  
% 2.68/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.41  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.68/1.41  
% 2.68/1.41  %Foreground sorts:
% 2.68/1.41  
% 2.68/1.41  
% 2.68/1.41  %Background operators:
% 2.68/1.41  
% 2.68/1.41  
% 2.68/1.41  %Foreground operators:
% 2.68/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.68/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.68/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.68/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.68/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.68/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.68/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.68/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.68/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.68/1.41  
% 2.68/1.42  tff(f_47, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.68/1.42  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.68/1.42  tff(f_54, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.68/1.42  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.68/1.42  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.68/1.42  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.68/1.42  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.68/1.42  tff(f_43, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.68/1.42  tff(c_1053, plain, (![A_72, B_73]: (r1_xboole_0(A_72, B_73) | k4_xboole_0(A_72, B_73)!=A_72)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.68/1.42  tff(c_40, plain, (![A_21, B_22]: (r1_tarski(A_21, B_22) | k4_xboole_0(A_21, B_22)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.68/1.42  tff(c_22, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.68/1.42  tff(c_39, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_22])).
% 2.68/1.42  tff(c_44, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_39])).
% 2.68/1.42  tff(c_12, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.68/1.42  tff(c_34, plain, (![A_18, B_19]: (r1_tarski(k4_xboole_0(A_18, B_19), A_18))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.68/1.42  tff(c_37, plain, (![A_9]: (r1_tarski(A_9, A_9))), inference(superposition, [status(thm), theory('equality')], [c_12, c_34])).
% 2.68/1.42  tff(c_45, plain, (![A_23, B_24]: (k4_xboole_0(A_23, B_24)=k1_xboole_0 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.68/1.42  tff(c_60, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_37, c_45])).
% 2.68/1.42  tff(c_239, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k4_xboole_0(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.68/1.42  tff(c_280, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_239])).
% 2.68/1.42  tff(c_289, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_280])).
% 2.68/1.42  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.68/1.42  tff(c_61, plain, (![A_7, B_8]: (k4_xboole_0(k4_xboole_0(A_7, B_8), A_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_45])).
% 2.68/1.42  tff(c_24, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.68/1.42  tff(c_188, plain, (![A_34, B_35]: (k3_xboole_0(A_34, B_35)=A_34 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.68/1.42  tff(c_206, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_24, c_188])).
% 2.68/1.42  tff(c_396, plain, (![A_47, B_48, C_49]: (k4_xboole_0(k3_xboole_0(A_47, B_48), C_49)=k3_xboole_0(A_47, k4_xboole_0(B_48, C_49)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.68/1.42  tff(c_844, plain, (![C_62]: (k3_xboole_0('#skF_1', k4_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_62))=k4_xboole_0('#skF_1', C_62))), inference(superposition, [status(thm), theory('equality')], [c_206, c_396])).
% 2.68/1.42  tff(c_882, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_61, c_844])).
% 2.68/1.42  tff(c_898, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_289, c_882])).
% 2.68/1.42  tff(c_900, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_898])).
% 2.68/1.42  tff(c_901, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_22])).
% 2.68/1.42  tff(c_1061, plain, (k4_xboole_0('#skF_1', '#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_1053, c_901])).
% 2.68/1.42  tff(c_902, plain, (r1_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_22])).
% 2.68/1.42  tff(c_1067, plain, (![A_76, B_77]: (k3_xboole_0(A_76, B_77)=A_76 | ~r1_tarski(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.68/1.42  tff(c_1088, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_902, c_1067])).
% 2.68/1.42  tff(c_1328, plain, (![A_90, B_91, C_92]: (k4_xboole_0(k3_xboole_0(A_90, B_91), C_92)=k3_xboole_0(A_90, k4_xboole_0(B_91, C_92)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.68/1.42  tff(c_1771, plain, (![C_104]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_104))=k4_xboole_0('#skF_1', C_104))), inference(superposition, [status(thm), theory('equality')], [c_1088, c_1328])).
% 2.68/1.42  tff(c_1089, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_24, c_1067])).
% 2.68/1.42  tff(c_1793, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1771, c_1089])).
% 2.68/1.42  tff(c_1825, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1061, c_1793])).
% 2.68/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.42  
% 2.68/1.42  Inference rules
% 2.68/1.42  ----------------------
% 2.68/1.42  #Ref     : 0
% 2.68/1.42  #Sup     : 448
% 2.68/1.42  #Fact    : 0
% 2.68/1.42  #Define  : 0
% 2.68/1.42  #Split   : 1
% 2.68/1.42  #Chain   : 0
% 2.68/1.42  #Close   : 0
% 2.68/1.42  
% 2.68/1.42  Ordering : KBO
% 2.68/1.42  
% 2.68/1.42  Simplification rules
% 2.68/1.42  ----------------------
% 2.68/1.42  #Subsume      : 0
% 2.68/1.42  #Demod        : 254
% 2.68/1.42  #Tautology    : 322
% 2.68/1.42  #SimpNegUnit  : 2
% 2.68/1.42  #BackRed      : 0
% 2.68/1.42  
% 2.68/1.42  #Partial instantiations: 0
% 2.68/1.42  #Strategies tried      : 1
% 2.68/1.42  
% 2.68/1.42  Timing (in seconds)
% 2.68/1.42  ----------------------
% 2.68/1.42  Preprocessing        : 0.26
% 2.68/1.42  Parsing              : 0.14
% 2.68/1.42  CNF conversion       : 0.02
% 2.68/1.42  Main loop            : 0.39
% 2.68/1.43  Inferencing          : 0.15
% 2.68/1.43  Reduction            : 0.14
% 2.68/1.43  Demodulation         : 0.10
% 2.68/1.43  BG Simplification    : 0.02
% 2.68/1.43  Subsumption          : 0.06
% 2.68/1.43  Abstraction          : 0.02
% 2.68/1.43  MUC search           : 0.00
% 2.68/1.43  Cooper               : 0.00
% 2.68/1.43  Total                : 0.68
% 2.68/1.43  Index Insertion      : 0.00
% 2.68/1.43  Index Deletion       : 0.00
% 2.68/1.43  Index Matching       : 0.00
% 2.68/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
