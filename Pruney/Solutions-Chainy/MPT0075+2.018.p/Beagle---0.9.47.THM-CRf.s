%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:32 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   48 (  59 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :   55 (  82 expanded)
%              Number of equality atoms :   22 (  28 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ~ ( r1_tarski(C,A)
            & r1_tarski(C,B)
            & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).

tff(f_38,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_36,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_30,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_24,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_82,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k4_xboole_0(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_97,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_82])).

tff(c_114,plain,(
    ! [A_27] : k4_xboole_0(A_27,A_27) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_97])).

tff(c_14,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_119,plain,(
    ! [A_27] : k4_xboole_0(A_27,k1_xboole_0) = k3_xboole_0(A_27,A_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_14])).

tff(c_131,plain,(
    ! [A_27] : k3_xboole_0(A_27,A_27) = A_27 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_119])).

tff(c_22,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_101,plain,(
    ! [A_24,C_25,B_26] :
      ( r1_xboole_0(A_24,C_25)
      | ~ r1_xboole_0(B_26,C_25)
      | ~ r1_tarski(A_24,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_154,plain,(
    ! [A_29] :
      ( r1_xboole_0(A_29,'#skF_2')
      | ~ r1_tarski(A_29,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_18,c_101])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_176,plain,(
    ! [A_31] :
      ( r1_xboole_0('#skF_2',A_31)
      | ~ r1_tarski(A_31,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_154,c_8])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_344,plain,(
    ! [A_46] :
      ( k3_xboole_0('#skF_2',A_46) = k1_xboole_0
      | ~ r1_tarski(A_46,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_176,c_2])).

tff(c_348,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_344])).

tff(c_20,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_285,plain,(
    ! [A_39,B_40,A_41] :
      ( r1_xboole_0(A_39,B_40)
      | ~ r1_tarski(A_39,A_41)
      | k3_xboole_0(A_41,B_40) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_101])).

tff(c_300,plain,(
    ! [B_42] :
      ( r1_xboole_0('#skF_3',B_42)
      | k3_xboole_0('#skF_2',B_42) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_285])).

tff(c_430,plain,(
    ! [B_50] :
      ( k3_xboole_0('#skF_3',B_50) = k1_xboole_0
      | k3_xboole_0('#skF_2',B_50) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_300,c_2])).

tff(c_436,plain,(
    k3_xboole_0('#skF_3','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_430])).

tff(c_452,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_436])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_481,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_6])).

tff(c_483,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_481])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:39:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.42  
% 2.33/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.42  %$ r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.33/1.42  
% 2.33/1.42  %Foreground sorts:
% 2.33/1.42  
% 2.33/1.42  
% 2.33/1.42  %Background operators:
% 2.33/1.42  
% 2.33/1.42  
% 2.33/1.42  %Foreground operators:
% 2.33/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.33/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.33/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.33/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.33/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.33/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.33/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.33/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.33/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.33/1.42  
% 2.33/1.43  tff(f_57, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => ~((r1_tarski(C, A) & r1_tarski(C, B)) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_xboole_1)).
% 2.33/1.43  tff(f_38, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.33/1.43  tff(f_36, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.33/1.43  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.33/1.43  tff(f_46, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.33/1.43  tff(f_34, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.33/1.43  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.33/1.43  tff(f_30, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.33/1.43  tff(c_24, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.33/1.43  tff(c_12, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.33/1.43  tff(c_10, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.33/1.43  tff(c_82, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k4_xboole_0(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.33/1.43  tff(c_97, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_82])).
% 2.33/1.43  tff(c_114, plain, (![A_27]: (k4_xboole_0(A_27, A_27)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_97])).
% 2.33/1.43  tff(c_14, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.33/1.43  tff(c_119, plain, (![A_27]: (k4_xboole_0(A_27, k1_xboole_0)=k3_xboole_0(A_27, A_27))), inference(superposition, [status(thm), theory('equality')], [c_114, c_14])).
% 2.33/1.43  tff(c_131, plain, (![A_27]: (k3_xboole_0(A_27, A_27)=A_27)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_119])).
% 2.33/1.43  tff(c_22, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.33/1.43  tff(c_18, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.33/1.43  tff(c_101, plain, (![A_24, C_25, B_26]: (r1_xboole_0(A_24, C_25) | ~r1_xboole_0(B_26, C_25) | ~r1_tarski(A_24, B_26))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.33/1.43  tff(c_154, plain, (![A_29]: (r1_xboole_0(A_29, '#skF_2') | ~r1_tarski(A_29, '#skF_1'))), inference(resolution, [status(thm)], [c_18, c_101])).
% 2.33/1.43  tff(c_8, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.33/1.43  tff(c_176, plain, (![A_31]: (r1_xboole_0('#skF_2', A_31) | ~r1_tarski(A_31, '#skF_1'))), inference(resolution, [status(thm)], [c_154, c_8])).
% 2.33/1.43  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.33/1.43  tff(c_344, plain, (![A_46]: (k3_xboole_0('#skF_2', A_46)=k1_xboole_0 | ~r1_tarski(A_46, '#skF_1'))), inference(resolution, [status(thm)], [c_176, c_2])).
% 2.33/1.43  tff(c_348, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_344])).
% 2.33/1.43  tff(c_20, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.33/1.43  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.33/1.43  tff(c_285, plain, (![A_39, B_40, A_41]: (r1_xboole_0(A_39, B_40) | ~r1_tarski(A_39, A_41) | k3_xboole_0(A_41, B_40)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_101])).
% 2.33/1.43  tff(c_300, plain, (![B_42]: (r1_xboole_0('#skF_3', B_42) | k3_xboole_0('#skF_2', B_42)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_285])).
% 2.33/1.43  tff(c_430, plain, (![B_50]: (k3_xboole_0('#skF_3', B_50)=k1_xboole_0 | k3_xboole_0('#skF_2', B_50)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_300, c_2])).
% 2.33/1.43  tff(c_436, plain, (k3_xboole_0('#skF_3', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_348, c_430])).
% 2.33/1.43  tff(c_452, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_131, c_436])).
% 2.33/1.43  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.33/1.43  tff(c_481, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_452, c_6])).
% 2.33/1.43  tff(c_483, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_481])).
% 2.33/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.43  
% 2.33/1.43  Inference rules
% 2.33/1.43  ----------------------
% 2.33/1.43  #Ref     : 0
% 2.33/1.43  #Sup     : 123
% 2.33/1.43  #Fact    : 0
% 2.33/1.43  #Define  : 0
% 2.33/1.43  #Split   : 2
% 2.33/1.43  #Chain   : 0
% 2.33/1.43  #Close   : 0
% 2.33/1.43  
% 2.33/1.43  Ordering : KBO
% 2.33/1.43  
% 2.33/1.43  Simplification rules
% 2.33/1.43  ----------------------
% 2.33/1.43  #Subsume      : 5
% 2.33/1.43  #Demod        : 78
% 2.33/1.43  #Tautology    : 61
% 2.33/1.43  #SimpNegUnit  : 1
% 2.33/1.43  #BackRed      : 24
% 2.33/1.43  
% 2.33/1.43  #Partial instantiations: 0
% 2.33/1.43  #Strategies tried      : 1
% 2.33/1.43  
% 2.33/1.43  Timing (in seconds)
% 2.33/1.43  ----------------------
% 2.33/1.44  Preprocessing        : 0.27
% 2.33/1.44  Parsing              : 0.15
% 2.33/1.44  CNF conversion       : 0.02
% 2.33/1.44  Main loop            : 0.30
% 2.33/1.44  Inferencing          : 0.11
% 2.33/1.44  Reduction            : 0.09
% 2.33/1.44  Demodulation         : 0.06
% 2.33/1.44  BG Simplification    : 0.01
% 2.33/1.44  Subsumption          : 0.07
% 2.33/1.44  Abstraction          : 0.01
% 2.33/1.44  MUC search           : 0.00
% 2.33/1.44  Cooper               : 0.00
% 2.33/1.44  Total                : 0.60
% 2.33/1.44  Index Insertion      : 0.00
% 2.33/1.44  Index Deletion       : 0.00
% 2.33/1.44  Index Matching       : 0.00
% 2.33/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
