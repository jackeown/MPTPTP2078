%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:28 EST 2020

% Result     : Theorem 4.50s
% Output     : CNFRefutation 4.50s
% Verified   : 
% Statistics : Number of formulae       :   48 (  65 expanded)
%              Number of leaves         :   18 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   51 (  81 expanded)
%              Number of equality atoms :   26 (  38 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_xboole_0(A,C)
          & r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(c_122,plain,(
    ! [A_27,B_28] :
      ( r1_xboole_0(A_27,B_28)
      | k3_xboole_0(A_27,B_28) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_133,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_122,c_24])).

tff(c_10,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k4_xboole_0(A_6,B_7)) = k3_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_34,plain,(
    ! [A_16,B_17] : r1_xboole_0(k4_xboole_0(A_16,B_17),B_17) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_48,plain,(
    ! [A_20] : r1_xboole_0(A_20,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_34])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_51,plain,(
    ! [A_20] : r1_xboole_0(k1_xboole_0,A_20) ),
    inference(resolution,[status(thm)],[c_48,c_6])).

tff(c_207,plain,(
    ! [A_36,B_37] :
      ( k4_xboole_0(A_36,B_37) = A_36
      | ~ r1_xboole_0(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_242,plain,(
    ! [A_20] : k4_xboole_0(k1_xboole_0,A_20) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_51,c_207])).

tff(c_22,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_38,plain,(
    ! [B_18,A_19] :
      ( r1_xboole_0(B_18,A_19)
      | ~ r1_xboole_0(A_19,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_47,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_38])).

tff(c_74,plain,(
    ! [A_24,B_25] :
      ( k3_xboole_0(A_24,B_25) = k1_xboole_0
      | ~ r1_xboole_0(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_102,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_47,c_74])).

tff(c_634,plain,(
    ! [A_47,B_48,C_49] : k4_xboole_0(k3_xboole_0(A_47,B_48),C_49) = k3_xboole_0(A_47,k4_xboole_0(B_48,C_49)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_710,plain,(
    ! [C_49] : k3_xboole_0('#skF_3',k4_xboole_0('#skF_1',C_49)) = k4_xboole_0(k1_xboole_0,C_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_634])).

tff(c_735,plain,(
    ! [C_50] : k3_xboole_0('#skF_3',k4_xboole_0('#skF_1',C_50)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_710])).

tff(c_763,plain,(
    ! [B_7] : k3_xboole_0('#skF_3',k3_xboole_0('#skF_1',B_7)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_735])).

tff(c_1100,plain,(
    ! [B_60,A_61] :
      ( r1_xboole_0(B_60,A_61)
      | k3_xboole_0(A_61,B_60) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_122,c_6])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3543,plain,(
    ! [B_115,A_116] :
      ( k3_xboole_0(B_115,A_116) = k1_xboole_0
      | k3_xboole_0(A_116,B_115) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1100,c_2])).

tff(c_3593,plain,(
    ! [B_7] : k3_xboole_0(k3_xboole_0('#skF_1',B_7),'#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_763,c_3543])).

tff(c_20,plain,(
    r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_105,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_74])).

tff(c_4637,plain,(
    ! [A_126,B_127,C_128] : k4_xboole_0(k3_xboole_0(A_126,B_127),k3_xboole_0(A_126,k4_xboole_0(B_127,C_128))) = k3_xboole_0(k3_xboole_0(A_126,B_127),C_128) ),
    inference(superposition,[status(thm),theory(equality)],[c_634,c_10])).

tff(c_4859,plain,(
    k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k1_xboole_0) = k3_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_4637])).

tff(c_4926,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3593,c_8,c_4859])).

tff(c_4928,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_4926])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:42:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.50/1.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.50/1.86  
% 4.50/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.50/1.86  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.50/1.86  
% 4.50/1.86  %Foreground sorts:
% 4.50/1.86  
% 4.50/1.86  
% 4.50/1.86  %Background operators:
% 4.50/1.86  
% 4.50/1.86  
% 4.50/1.86  %Foreground operators:
% 4.50/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.50/1.86  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.50/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.50/1.86  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.50/1.86  tff('#skF_2', type, '#skF_2': $i).
% 4.50/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.50/1.86  tff('#skF_1', type, '#skF_1': $i).
% 4.50/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.50/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.50/1.86  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.50/1.86  
% 4.50/1.87  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.50/1.87  tff(f_54, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_xboole_1)).
% 4.50/1.87  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.50/1.87  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.50/1.87  tff(f_41, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.50/1.87  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.50/1.87  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.50/1.87  tff(f_39, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 4.50/1.87  tff(c_122, plain, (![A_27, B_28]: (r1_xboole_0(A_27, B_28) | k3_xboole_0(A_27, B_28)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.50/1.87  tff(c_24, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.50/1.87  tff(c_133, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_122, c_24])).
% 4.50/1.87  tff(c_10, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k4_xboole_0(A_6, B_7))=k3_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.50/1.87  tff(c_8, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.50/1.87  tff(c_34, plain, (![A_16, B_17]: (r1_xboole_0(k4_xboole_0(A_16, B_17), B_17))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.50/1.87  tff(c_48, plain, (![A_20]: (r1_xboole_0(A_20, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_34])).
% 4.50/1.87  tff(c_6, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.50/1.87  tff(c_51, plain, (![A_20]: (r1_xboole_0(k1_xboole_0, A_20))), inference(resolution, [status(thm)], [c_48, c_6])).
% 4.50/1.87  tff(c_207, plain, (![A_36, B_37]: (k4_xboole_0(A_36, B_37)=A_36 | ~r1_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.50/1.87  tff(c_242, plain, (![A_20]: (k4_xboole_0(k1_xboole_0, A_20)=k1_xboole_0)), inference(resolution, [status(thm)], [c_51, c_207])).
% 4.50/1.87  tff(c_22, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.50/1.87  tff(c_38, plain, (![B_18, A_19]: (r1_xboole_0(B_18, A_19) | ~r1_xboole_0(A_19, B_18))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.50/1.87  tff(c_47, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_22, c_38])).
% 4.50/1.87  tff(c_74, plain, (![A_24, B_25]: (k3_xboole_0(A_24, B_25)=k1_xboole_0 | ~r1_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.50/1.87  tff(c_102, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_47, c_74])).
% 4.50/1.87  tff(c_634, plain, (![A_47, B_48, C_49]: (k4_xboole_0(k3_xboole_0(A_47, B_48), C_49)=k3_xboole_0(A_47, k4_xboole_0(B_48, C_49)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.50/1.87  tff(c_710, plain, (![C_49]: (k3_xboole_0('#skF_3', k4_xboole_0('#skF_1', C_49))=k4_xboole_0(k1_xboole_0, C_49))), inference(superposition, [status(thm), theory('equality')], [c_102, c_634])).
% 4.50/1.87  tff(c_735, plain, (![C_50]: (k3_xboole_0('#skF_3', k4_xboole_0('#skF_1', C_50))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_242, c_710])).
% 4.50/1.87  tff(c_763, plain, (![B_7]: (k3_xboole_0('#skF_3', k3_xboole_0('#skF_1', B_7))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_735])).
% 4.50/1.87  tff(c_1100, plain, (![B_60, A_61]: (r1_xboole_0(B_60, A_61) | k3_xboole_0(A_61, B_60)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_122, c_6])).
% 4.50/1.87  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.50/1.87  tff(c_3543, plain, (![B_115, A_116]: (k3_xboole_0(B_115, A_116)=k1_xboole_0 | k3_xboole_0(A_116, B_115)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_1100, c_2])).
% 4.50/1.87  tff(c_3593, plain, (![B_7]: (k3_xboole_0(k3_xboole_0('#skF_1', B_7), '#skF_3')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_763, c_3543])).
% 4.50/1.87  tff(c_20, plain, (r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.50/1.87  tff(c_105, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_74])).
% 4.50/1.87  tff(c_4637, plain, (![A_126, B_127, C_128]: (k4_xboole_0(k3_xboole_0(A_126, B_127), k3_xboole_0(A_126, k4_xboole_0(B_127, C_128)))=k3_xboole_0(k3_xboole_0(A_126, B_127), C_128))), inference(superposition, [status(thm), theory('equality')], [c_634, c_10])).
% 4.50/1.87  tff(c_4859, plain, (k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k1_xboole_0)=k3_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_105, c_4637])).
% 4.50/1.87  tff(c_4926, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3593, c_8, c_4859])).
% 4.50/1.87  tff(c_4928, plain, $false, inference(negUnitSimplification, [status(thm)], [c_133, c_4926])).
% 4.50/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.50/1.87  
% 4.50/1.87  Inference rules
% 4.50/1.87  ----------------------
% 4.50/1.87  #Ref     : 0
% 4.50/1.87  #Sup     : 1250
% 4.50/1.87  #Fact    : 0
% 4.50/1.87  #Define  : 0
% 4.50/1.87  #Split   : 0
% 4.50/1.87  #Chain   : 0
% 4.50/1.87  #Close   : 0
% 4.50/1.87  
% 4.50/1.87  Ordering : KBO
% 4.50/1.87  
% 4.50/1.87  Simplification rules
% 4.50/1.87  ----------------------
% 4.50/1.87  #Subsume      : 23
% 4.50/1.87  #Demod        : 1068
% 4.50/1.87  #Tautology    : 932
% 4.50/1.87  #SimpNegUnit  : 9
% 4.50/1.87  #BackRed      : 0
% 4.50/1.87  
% 4.50/1.87  #Partial instantiations: 0
% 4.50/1.87  #Strategies tried      : 1
% 4.50/1.87  
% 4.50/1.87  Timing (in seconds)
% 4.50/1.87  ----------------------
% 4.50/1.88  Preprocessing        : 0.28
% 4.50/1.88  Parsing              : 0.15
% 4.50/1.88  CNF conversion       : 0.02
% 4.50/1.88  Main loop            : 0.84
% 4.50/1.88  Inferencing          : 0.27
% 4.50/1.88  Reduction            : 0.35
% 4.50/1.88  Demodulation         : 0.28
% 4.50/1.88  BG Simplification    : 0.02
% 4.50/1.88  Subsumption          : 0.13
% 4.50/1.88  Abstraction          : 0.05
% 4.50/1.88  MUC search           : 0.00
% 4.50/1.88  Cooper               : 0.00
% 4.50/1.88  Total                : 1.14
% 4.50/1.88  Index Insertion      : 0.00
% 4.50/1.88  Index Deletion       : 0.00
% 4.86/1.88  Index Matching       : 0.00
% 4.86/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
