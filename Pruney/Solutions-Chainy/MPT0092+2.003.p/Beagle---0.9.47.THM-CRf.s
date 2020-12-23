%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:29 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :   43 (  50 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   36 (  44 expanded)
%              Number of equality atoms :   27 (  33 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_14,plain,(
    ! [A_10,B_11] : k2_xboole_0(k3_xboole_0(A_10,B_11),k4_xboole_0(A_10,B_11)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_112,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k4_xboole_0(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_121,plain,(
    ! [A_30,B_31] : k2_xboole_0(k4_xboole_0(A_30,B_31),k3_xboole_0(A_30,B_31)) = k2_xboole_0(k4_xboole_0(A_30,B_31),A_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_8])).

tff(c_902,plain,(
    ! [A_54,B_55] : k2_xboole_0(k4_xboole_0(A_54,B_55),k3_xboole_0(A_54,B_55)) = k2_xboole_0(A_54,k4_xboole_0(A_54,B_55)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_121])).

tff(c_911,plain,(
    ! [A_54,B_55] : k2_xboole_0(k3_xboole_0(A_54,B_55),k4_xboole_0(A_54,B_55)) = k2_xboole_0(A_54,k4_xboole_0(A_54,B_55)) ),
    inference(superposition,[status(thm),theory(equality)],[c_902,c_2])).

tff(c_972,plain,(
    ! [A_54,B_55] : k2_xboole_0(A_54,k4_xboole_0(A_54,B_55)) = A_54 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_911])).

tff(c_10,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_78,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(A_26,B_27) = k1_xboole_0
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_86,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_78])).

tff(c_130,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_112])).

tff(c_137,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_130])).

tff(c_251,plain,(
    ! [A_37,B_38,C_39] : k2_xboole_0(k4_xboole_0(A_37,B_38),k3_xboole_0(A_37,C_39)) = k4_xboole_0(A_37,k4_xboole_0(B_38,C_39)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1217,plain,(
    ! [A_61,C_62,B_63] : k2_xboole_0(k3_xboole_0(A_61,C_62),k4_xboole_0(A_61,B_63)) = k4_xboole_0(A_61,k4_xboole_0(B_63,C_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_251])).

tff(c_1273,plain,(
    ! [B_63] : k4_xboole_0('#skF_1',k4_xboole_0(B_63,'#skF_2')) = k2_xboole_0('#skF_1',k4_xboole_0('#skF_1',B_63)) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_1217])).

tff(c_1307,plain,(
    ! [B_63] : k4_xboole_0('#skF_1',k4_xboole_0(B_63,'#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_972,c_1273])).

tff(c_69,plain,(
    ! [A_24,B_25] :
      ( r1_xboole_0(A_24,B_25)
      | k4_xboole_0(A_24,B_25) != A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ~ r1_xboole_0('#skF_1',k4_xboole_0('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_77,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_3','#skF_2')) != '#skF_1' ),
    inference(resolution,[status(thm)],[c_69,c_22])).

tff(c_1751,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1307,c_77])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:57:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.33/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.53  
% 3.33/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.53  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.33/1.53  
% 3.33/1.53  %Foreground sorts:
% 3.33/1.53  
% 3.33/1.53  
% 3.33/1.53  %Background operators:
% 3.33/1.53  
% 3.33/1.53  
% 3.33/1.53  %Foreground operators:
% 3.33/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.33/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.33/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.33/1.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.33/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.33/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.33/1.53  tff('#skF_1', type, '#skF_1': $i).
% 3.33/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.33/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.33/1.53  
% 3.33/1.54  tff(f_39, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.33/1.54  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.33/1.54  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.33/1.54  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.33/1.54  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.33/1.54  tff(f_50, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 3.33/1.54  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.33/1.54  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 3.33/1.54  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.33/1.54  tff(c_14, plain, (![A_10, B_11]: (k2_xboole_0(k3_xboole_0(A_10, B_11), k4_xboole_0(A_10, B_11))=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.33/1.54  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.33/1.54  tff(c_112, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k4_xboole_0(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.33/1.54  tff(c_8, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.33/1.54  tff(c_121, plain, (![A_30, B_31]: (k2_xboole_0(k4_xboole_0(A_30, B_31), k3_xboole_0(A_30, B_31))=k2_xboole_0(k4_xboole_0(A_30, B_31), A_30))), inference(superposition, [status(thm), theory('equality')], [c_112, c_8])).
% 3.33/1.54  tff(c_902, plain, (![A_54, B_55]: (k2_xboole_0(k4_xboole_0(A_54, B_55), k3_xboole_0(A_54, B_55))=k2_xboole_0(A_54, k4_xboole_0(A_54, B_55)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_121])).
% 3.33/1.54  tff(c_911, plain, (![A_54, B_55]: (k2_xboole_0(k3_xboole_0(A_54, B_55), k4_xboole_0(A_54, B_55))=k2_xboole_0(A_54, k4_xboole_0(A_54, B_55)))), inference(superposition, [status(thm), theory('equality')], [c_902, c_2])).
% 3.33/1.54  tff(c_972, plain, (![A_54, B_55]: (k2_xboole_0(A_54, k4_xboole_0(A_54, B_55))=A_54)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_911])).
% 3.33/1.54  tff(c_10, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.33/1.54  tff(c_24, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.33/1.54  tff(c_78, plain, (![A_26, B_27]: (k4_xboole_0(A_26, B_27)=k1_xboole_0 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.33/1.54  tff(c_86, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_78])).
% 3.33/1.54  tff(c_130, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_86, c_112])).
% 3.33/1.54  tff(c_137, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_130])).
% 3.33/1.54  tff(c_251, plain, (![A_37, B_38, C_39]: (k2_xboole_0(k4_xboole_0(A_37, B_38), k3_xboole_0(A_37, C_39))=k4_xboole_0(A_37, k4_xboole_0(B_38, C_39)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.33/1.54  tff(c_1217, plain, (![A_61, C_62, B_63]: (k2_xboole_0(k3_xboole_0(A_61, C_62), k4_xboole_0(A_61, B_63))=k4_xboole_0(A_61, k4_xboole_0(B_63, C_62)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_251])).
% 3.33/1.54  tff(c_1273, plain, (![B_63]: (k4_xboole_0('#skF_1', k4_xboole_0(B_63, '#skF_2'))=k2_xboole_0('#skF_1', k4_xboole_0('#skF_1', B_63)))), inference(superposition, [status(thm), theory('equality')], [c_137, c_1217])).
% 3.33/1.54  tff(c_1307, plain, (![B_63]: (k4_xboole_0('#skF_1', k4_xboole_0(B_63, '#skF_2'))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_972, c_1273])).
% 3.33/1.54  tff(c_69, plain, (![A_24, B_25]: (r1_xboole_0(A_24, B_25) | k4_xboole_0(A_24, B_25)!=A_24)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.33/1.54  tff(c_22, plain, (~r1_xboole_0('#skF_1', k4_xboole_0('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.33/1.54  tff(c_77, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_3', '#skF_2'))!='#skF_1'), inference(resolution, [status(thm)], [c_69, c_22])).
% 3.33/1.54  tff(c_1751, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1307, c_77])).
% 3.33/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.54  
% 3.33/1.54  Inference rules
% 3.33/1.54  ----------------------
% 3.33/1.54  #Ref     : 0
% 3.33/1.54  #Sup     : 427
% 3.33/1.54  #Fact    : 0
% 3.33/1.54  #Define  : 0
% 3.33/1.54  #Split   : 0
% 3.33/1.54  #Chain   : 0
% 3.33/1.54  #Close   : 0
% 3.33/1.54  
% 3.33/1.54  Ordering : KBO
% 3.33/1.54  
% 3.33/1.54  Simplification rules
% 3.33/1.54  ----------------------
% 3.33/1.54  #Subsume      : 0
% 3.33/1.54  #Demod        : 430
% 3.33/1.54  #Tautology    : 290
% 3.33/1.54  #SimpNegUnit  : 0
% 3.33/1.54  #BackRed      : 12
% 3.33/1.54  
% 3.33/1.54  #Partial instantiations: 0
% 3.33/1.54  #Strategies tried      : 1
% 3.33/1.54  
% 3.33/1.54  Timing (in seconds)
% 3.33/1.54  ----------------------
% 3.48/1.54  Preprocessing        : 0.28
% 3.48/1.54  Parsing              : 0.15
% 3.48/1.55  CNF conversion       : 0.02
% 3.48/1.55  Main loop            : 0.52
% 3.48/1.55  Inferencing          : 0.17
% 3.48/1.55  Reduction            : 0.22
% 3.48/1.55  Demodulation         : 0.18
% 3.48/1.55  BG Simplification    : 0.02
% 3.48/1.55  Subsumption          : 0.08
% 3.48/1.55  Abstraction          : 0.02
% 3.48/1.55  MUC search           : 0.00
% 3.48/1.55  Cooper               : 0.00
% 3.48/1.55  Total                : 0.82
% 3.48/1.55  Index Insertion      : 0.00
% 3.48/1.55  Index Deletion       : 0.00
% 3.48/1.55  Index Matching       : 0.00
% 3.48/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
