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
% DateTime   : Thu Dec  3 09:44:32 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   47 (  55 expanded)
%              Number of leaves         :   19 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   51 (  68 expanded)
%              Number of equality atoms :   30 (  36 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(A,C) )
       => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_22,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_51,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,B_24) = A_23
      | ~ r1_xboole_0(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_63,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22,c_51])).

tff(c_10,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_80,plain,(
    ! [A_25,B_26] :
      ( k4_xboole_0(A_25,B_26) = k1_xboole_0
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_92,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_80])).

tff(c_238,plain,(
    ! [A_36,B_37] : k4_xboole_0(A_36,k4_xboole_0(A_36,B_37)) = k3_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_276,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_238])).

tff(c_291,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_276])).

tff(c_299,plain,(
    ! [A_38,B_39,C_40] : k4_xboole_0(k3_xboole_0(A_38,B_39),C_40) = k3_xboole_0(A_38,k4_xboole_0(B_39,C_40)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_329,plain,(
    ! [C_40] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_40)) = k4_xboole_0('#skF_1',C_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_299])).

tff(c_8,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_91,plain,(
    ! [A_5,B_6] : k4_xboole_0(k4_xboole_0(A_5,B_6),A_5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_80])).

tff(c_12,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_47,plain,(
    ! [A_21,B_22] :
      ( r1_xboole_0(A_21,B_22)
      | k4_xboole_0(A_21,B_22) != A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_230,plain,(
    ! [B_34,A_35] :
      ( r1_xboole_0(B_34,A_35)
      | k4_xboole_0(A_35,B_34) != A_35 ) ),
    inference(resolution,[status(thm)],[c_47,c_2])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = A_13
      | ~ r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_990,plain,(
    ! [B_60,A_61] :
      ( k4_xboole_0(B_60,A_61) = B_60
      | k4_xboole_0(A_61,B_60) != A_61 ) ),
    inference(resolution,[status(thm)],[c_230,c_16])).

tff(c_998,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(k4_xboole_0(A_8,B_9),A_8) = k4_xboole_0(A_8,B_9)
      | k3_xboole_0(A_8,B_9) != A_8 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_990])).

tff(c_1400,plain,(
    ! [A_70,B_71] :
      ( k4_xboole_0(A_70,B_71) = k1_xboole_0
      | k3_xboole_0(A_70,B_71) != A_70 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_998])).

tff(c_104,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(A_27,B_28)
      | k4_xboole_0(A_27,B_28) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ~ r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_112,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_104,c_20])).

tff(c_1545,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1400,c_112])).

tff(c_1582,plain,(
    k4_xboole_0('#skF_1','#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_1545])).

tff(c_1585,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_1582])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:45:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.39  
% 2.63/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.40  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.92/1.40  
% 2.92/1.40  %Foreground sorts:
% 2.92/1.40  
% 2.92/1.40  
% 2.92/1.40  %Background operators:
% 2.92/1.40  
% 2.92/1.40  
% 2.92/1.40  %Foreground operators:
% 2.92/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.92/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.92/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.92/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.92/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.92/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.92/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.92/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.92/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.92/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.92/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.92/1.40  
% 2.92/1.41  tff(f_52, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 2.92/1.41  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.92/1.41  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.92/1.41  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.92/1.41  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.92/1.41  tff(f_41, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.92/1.41  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.92/1.41  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.92/1.41  tff(c_22, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.92/1.41  tff(c_51, plain, (![A_23, B_24]: (k4_xboole_0(A_23, B_24)=A_23 | ~r1_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.92/1.41  tff(c_63, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_22, c_51])).
% 2.92/1.41  tff(c_10, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.92/1.41  tff(c_24, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.92/1.41  tff(c_80, plain, (![A_25, B_26]: (k4_xboole_0(A_25, B_26)=k1_xboole_0 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.92/1.41  tff(c_92, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_80])).
% 2.92/1.41  tff(c_238, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k4_xboole_0(A_36, B_37))=k3_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.92/1.41  tff(c_276, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_92, c_238])).
% 2.92/1.41  tff(c_291, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_276])).
% 2.92/1.41  tff(c_299, plain, (![A_38, B_39, C_40]: (k4_xboole_0(k3_xboole_0(A_38, B_39), C_40)=k3_xboole_0(A_38, k4_xboole_0(B_39, C_40)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.92/1.41  tff(c_329, plain, (![C_40]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_40))=k4_xboole_0('#skF_1', C_40))), inference(superposition, [status(thm), theory('equality')], [c_291, c_299])).
% 2.92/1.41  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.92/1.41  tff(c_91, plain, (![A_5, B_6]: (k4_xboole_0(k4_xboole_0(A_5, B_6), A_5)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_80])).
% 2.92/1.41  tff(c_12, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.92/1.41  tff(c_47, plain, (![A_21, B_22]: (r1_xboole_0(A_21, B_22) | k4_xboole_0(A_21, B_22)!=A_21)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.92/1.41  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.92/1.41  tff(c_230, plain, (![B_34, A_35]: (r1_xboole_0(B_34, A_35) | k4_xboole_0(A_35, B_34)!=A_35)), inference(resolution, [status(thm)], [c_47, c_2])).
% 2.92/1.41  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=A_13 | ~r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.92/1.41  tff(c_990, plain, (![B_60, A_61]: (k4_xboole_0(B_60, A_61)=B_60 | k4_xboole_0(A_61, B_60)!=A_61)), inference(resolution, [status(thm)], [c_230, c_16])).
% 2.92/1.41  tff(c_998, plain, (![A_8, B_9]: (k4_xboole_0(k4_xboole_0(A_8, B_9), A_8)=k4_xboole_0(A_8, B_9) | k3_xboole_0(A_8, B_9)!=A_8)), inference(superposition, [status(thm), theory('equality')], [c_12, c_990])).
% 2.92/1.41  tff(c_1400, plain, (![A_70, B_71]: (k4_xboole_0(A_70, B_71)=k1_xboole_0 | k3_xboole_0(A_70, B_71)!=A_70)), inference(demodulation, [status(thm), theory('equality')], [c_91, c_998])).
% 2.92/1.41  tff(c_104, plain, (![A_27, B_28]: (r1_tarski(A_27, B_28) | k4_xboole_0(A_27, B_28)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.92/1.41  tff(c_20, plain, (~r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.92/1.41  tff(c_112, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_104, c_20])).
% 2.92/1.41  tff(c_1545, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1400, c_112])).
% 2.92/1.41  tff(c_1582, plain, (k4_xboole_0('#skF_1', '#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_329, c_1545])).
% 2.92/1.41  tff(c_1585, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_1582])).
% 2.92/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.41  
% 2.92/1.41  Inference rules
% 2.92/1.41  ----------------------
% 2.92/1.41  #Ref     : 0
% 2.92/1.41  #Sup     : 388
% 2.92/1.41  #Fact    : 0
% 2.92/1.41  #Define  : 0
% 2.92/1.41  #Split   : 2
% 2.92/1.41  #Chain   : 0
% 2.92/1.41  #Close   : 0
% 2.92/1.41  
% 2.92/1.41  Ordering : KBO
% 2.92/1.41  
% 2.92/1.41  Simplification rules
% 2.92/1.41  ----------------------
% 2.92/1.41  #Subsume      : 7
% 2.92/1.41  #Demod        : 333
% 2.92/1.41  #Tautology    : 291
% 2.92/1.41  #SimpNegUnit  : 3
% 2.92/1.41  #BackRed      : 2
% 2.92/1.41  
% 2.92/1.41  #Partial instantiations: 0
% 2.92/1.41  #Strategies tried      : 1
% 2.92/1.41  
% 2.92/1.41  Timing (in seconds)
% 2.92/1.41  ----------------------
% 2.92/1.41  Preprocessing        : 0.27
% 2.92/1.41  Parsing              : 0.14
% 2.92/1.41  CNF conversion       : 0.01
% 2.92/1.41  Main loop            : 0.39
% 2.92/1.41  Inferencing          : 0.14
% 2.92/1.41  Reduction            : 0.15
% 2.92/1.41  Demodulation         : 0.11
% 2.92/1.41  BG Simplification    : 0.02
% 2.92/1.41  Subsumption          : 0.06
% 2.92/1.41  Abstraction          : 0.02
% 2.92/1.41  MUC search           : 0.00
% 2.92/1.41  Cooper               : 0.00
% 2.92/1.41  Total                : 0.68
% 2.92/1.41  Index Insertion      : 0.00
% 2.92/1.41  Index Deletion       : 0.00
% 2.92/1.41  Index Matching       : 0.00
% 2.92/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
