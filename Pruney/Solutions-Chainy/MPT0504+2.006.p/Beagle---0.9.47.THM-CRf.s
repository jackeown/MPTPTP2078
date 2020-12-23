%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:49 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   45 (  62 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   49 (  79 expanded)
%              Number of equality atoms :   30 (  46 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_12,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_126,plain,(
    ! [B_26,A_27] :
      ( B_26 = A_27
      | ~ r1_tarski(B_26,A_27)
      | ~ r1_tarski(A_27,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_446,plain,(
    ! [A_41,B_42] :
      ( k4_xboole_0(A_41,B_42) = A_41
      | ~ r1_tarski(A_41,k4_xboole_0(A_41,B_42)) ) ),
    inference(resolution,[status(thm)],[c_14,c_126])).

tff(c_462,plain,(
    ! [A_3,B_42] :
      ( k4_xboole_0(A_3,B_42) = A_3
      | k4_xboole_0(A_3,k4_xboole_0(A_3,B_42)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_446])).

tff(c_598,plain,(
    ! [A_46,B_47] :
      ( k4_xboole_0(A_46,B_47) = A_46
      | k3_xboole_0(A_46,B_47) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_462])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_35,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = k1_xboole_0
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_46,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_35])).

tff(c_146,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k4_xboole_0(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_184,plain,(
    ! [B_2] : k4_xboole_0(B_2,k1_xboole_0) = k3_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_146])).

tff(c_628,plain,(
    ! [A_46] :
      ( k3_xboole_0(A_46,A_46) = A_46
      | k3_xboole_0(A_46,k1_xboole_0) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_598,c_184])).

tff(c_698,plain,(
    ! [A_46] : k3_xboole_0(A_46,A_46) = A_46 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_628])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_47,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_35])).

tff(c_181,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_146])).

tff(c_290,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k3_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_181])).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_270,plain,(
    ! [C_34,A_35,B_36] :
      ( k7_relat_1(k7_relat_1(C_34,A_35),B_36) = k7_relat_1(C_34,k3_xboole_0(A_35,B_36))
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') != k7_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_279,plain,
    ( k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k7_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_20])).

tff(c_288,plain,(
    k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k7_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_279])).

tff(c_374,plain,(
    k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_1')) != k7_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_288])).

tff(c_719,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_698,c_374])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:41:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.30  
% 2.07/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.30  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.07/1.30  
% 2.07/1.30  %Foreground sorts:
% 2.07/1.30  
% 2.07/1.30  
% 2.07/1.30  %Background operators:
% 2.07/1.30  
% 2.07/1.30  
% 2.07/1.30  %Foreground operators:
% 2.07/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.07/1.30  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.07/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.07/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.07/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.07/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.07/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.07/1.30  
% 2.07/1.31  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.07/1.31  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.07/1.31  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.07/1.31  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.07/1.31  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.07/1.31  tff(f_52, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_relat_1)).
% 2.07/1.31  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 2.07/1.31  tff(c_12, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.07/1.31  tff(c_16, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.07/1.31  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.07/1.31  tff(c_14, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.07/1.31  tff(c_126, plain, (![B_26, A_27]: (B_26=A_27 | ~r1_tarski(B_26, A_27) | ~r1_tarski(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.07/1.31  tff(c_446, plain, (![A_41, B_42]: (k4_xboole_0(A_41, B_42)=A_41 | ~r1_tarski(A_41, k4_xboole_0(A_41, B_42)))), inference(resolution, [status(thm)], [c_14, c_126])).
% 2.07/1.31  tff(c_462, plain, (![A_3, B_42]: (k4_xboole_0(A_3, B_42)=A_3 | k4_xboole_0(A_3, k4_xboole_0(A_3, B_42))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_446])).
% 2.07/1.31  tff(c_598, plain, (![A_46, B_47]: (k4_xboole_0(A_46, B_47)=A_46 | k3_xboole_0(A_46, B_47)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_462])).
% 2.07/1.31  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.07/1.31  tff(c_35, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=k1_xboole_0 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.07/1.31  tff(c_46, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_35])).
% 2.07/1.31  tff(c_146, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k4_xboole_0(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.07/1.31  tff(c_184, plain, (![B_2]: (k4_xboole_0(B_2, k1_xboole_0)=k3_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_46, c_146])).
% 2.07/1.31  tff(c_628, plain, (![A_46]: (k3_xboole_0(A_46, A_46)=A_46 | k3_xboole_0(A_46, k1_xboole_0)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_598, c_184])).
% 2.07/1.31  tff(c_698, plain, (![A_46]: (k3_xboole_0(A_46, A_46)=A_46)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_628])).
% 2.07/1.31  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.07/1.31  tff(c_47, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_35])).
% 2.07/1.31  tff(c_181, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_47, c_146])).
% 2.07/1.31  tff(c_290, plain, (k3_xboole_0('#skF_1', '#skF_2')=k3_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_184, c_181])).
% 2.07/1.31  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.07/1.31  tff(c_270, plain, (![C_34, A_35, B_36]: (k7_relat_1(k7_relat_1(C_34, A_35), B_36)=k7_relat_1(C_34, k3_xboole_0(A_35, B_36)) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.07/1.31  tff(c_20, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')!=k7_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.07/1.31  tff(c_279, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k7_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_270, c_20])).
% 2.07/1.31  tff(c_288, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k7_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_279])).
% 2.07/1.31  tff(c_374, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_1'))!=k7_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_290, c_288])).
% 2.07/1.31  tff(c_719, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_698, c_374])).
% 2.07/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.31  
% 2.07/1.31  Inference rules
% 2.07/1.31  ----------------------
% 2.07/1.31  #Ref     : 0
% 2.07/1.31  #Sup     : 166
% 2.07/1.31  #Fact    : 0
% 2.07/1.31  #Define  : 0
% 2.07/1.31  #Split   : 1
% 2.07/1.31  #Chain   : 0
% 2.07/1.31  #Close   : 0
% 2.07/1.31  
% 2.07/1.31  Ordering : KBO
% 2.07/1.31  
% 2.07/1.31  Simplification rules
% 2.07/1.31  ----------------------
% 2.07/1.31  #Subsume      : 12
% 2.07/1.31  #Demod        : 91
% 2.07/1.31  #Tautology    : 110
% 2.07/1.31  #SimpNegUnit  : 0
% 2.07/1.31  #BackRed      : 6
% 2.07/1.31  
% 2.07/1.31  #Partial instantiations: 0
% 2.07/1.31  #Strategies tried      : 1
% 2.07/1.31  
% 2.07/1.31  Timing (in seconds)
% 2.07/1.31  ----------------------
% 2.07/1.32  Preprocessing        : 0.26
% 2.07/1.32  Parsing              : 0.15
% 2.07/1.32  CNF conversion       : 0.02
% 2.07/1.32  Main loop            : 0.27
% 2.07/1.32  Inferencing          : 0.10
% 2.07/1.32  Reduction            : 0.09
% 2.07/1.32  Demodulation         : 0.07
% 2.07/1.32  BG Simplification    : 0.01
% 2.07/1.32  Subsumption          : 0.05
% 2.07/1.32  Abstraction          : 0.01
% 2.07/1.32  MUC search           : 0.00
% 2.07/1.32  Cooper               : 0.00
% 2.07/1.32  Total                : 0.56
% 2.07/1.32  Index Insertion      : 0.00
% 2.07/1.32  Index Deletion       : 0.00
% 2.07/1.32  Index Matching       : 0.00
% 2.07/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
