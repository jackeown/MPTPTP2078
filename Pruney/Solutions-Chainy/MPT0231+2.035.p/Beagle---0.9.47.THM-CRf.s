%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:19 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   47 (  55 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :   42 (  55 expanded)
%              Number of equality atoms :   20 (  27 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_24,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_20,plain,(
    ! [A_19,B_20] : r1_tarski(k1_tarski(A_19),k2_tarski(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_64,plain,(
    ! [A_32,B_33] :
      ( k2_xboole_0(A_32,B_33) = B_33
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_77,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_64])).

tff(c_6,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_36,plain,(
    ! [A_24,B_25] : r1_tarski(A_24,k2_xboole_0(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_39,plain,(
    ! [A_6] : r1_tarski(A_6,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_36])).

tff(c_79,plain,(
    ! [A_6] : k2_xboole_0(A_6,A_6) = A_6 ),
    inference(resolution,[status(thm)],[c_39,c_64])).

tff(c_12,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_475,plain,(
    ! [A_57,B_58] : k2_xboole_0(A_57,k2_xboole_0(A_57,B_58)) = k2_xboole_0(A_57,B_58) ),
    inference(resolution,[status(thm)],[c_12,c_64])).

tff(c_8,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_132,plain,(
    ! [A_39,B_40] : k4_xboole_0(k2_xboole_0(A_39,B_40),B_40) = k4_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_138,plain,(
    ! [B_40,A_39] : k2_xboole_0(B_40,k4_xboole_0(A_39,B_40)) = k2_xboole_0(B_40,k2_xboole_0(A_39,B_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_8])).

tff(c_155,plain,(
    ! [B_40,A_39] : k2_xboole_0(B_40,k2_xboole_0(A_39,B_40)) = k2_xboole_0(B_40,A_39) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_138])).

tff(c_484,plain,(
    ! [A_57,B_58] : k2_xboole_0(k2_xboole_0(A_57,B_58),k2_xboole_0(A_57,B_58)) = k2_xboole_0(k2_xboole_0(A_57,B_58),A_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_475,c_155])).

tff(c_589,plain,(
    ! [A_59,B_60] : k2_xboole_0(k2_xboole_0(A_59,B_60),A_59) = k2_xboole_0(A_59,B_60) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_484])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,k2_xboole_0(C_3,B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_676,plain,(
    ! [A_61,A_62,B_63] :
      ( r1_tarski(A_61,k2_xboole_0(A_62,B_63))
      | ~ r1_tarski(A_61,A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_2])).

tff(c_935,plain,(
    ! [A_72] :
      ( r1_tarski(A_72,k1_tarski('#skF_3'))
      | ~ r1_tarski(A_72,k2_tarski('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_676])).

tff(c_961,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_935])).

tff(c_22,plain,(
    ! [B_22,A_21] :
      ( B_22 = A_21
      | ~ r1_tarski(k1_tarski(A_21),k1_tarski(B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_966,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_961,c_22])).

tff(c_973,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_966])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:54:31 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.40  
% 2.40/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.40  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.40/1.40  
% 2.40/1.40  %Foreground sorts:
% 2.40/1.40  
% 2.40/1.40  
% 2.40/1.40  %Background operators:
% 2.40/1.40  
% 2.40/1.40  
% 2.40/1.40  %Foreground operators:
% 2.40/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.40/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.40/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.40/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.40/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.40/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.40/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.40/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.40/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.40/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.40/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.40/1.40  
% 2.40/1.41  tff(f_58, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 2.40/1.41  tff(f_49, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 2.40/1.41  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.40/1.41  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.40/1.41  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.40/1.41  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.40/1.41  tff(f_39, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.40/1.41  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.40/1.41  tff(f_53, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.40/1.41  tff(c_24, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.40/1.41  tff(c_20, plain, (![A_19, B_20]: (r1_tarski(k1_tarski(A_19), k2_tarski(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.40/1.41  tff(c_26, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.40/1.41  tff(c_64, plain, (![A_32, B_33]: (k2_xboole_0(A_32, B_33)=B_33 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.40/1.41  tff(c_77, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_26, c_64])).
% 2.40/1.41  tff(c_6, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.40/1.41  tff(c_36, plain, (![A_24, B_25]: (r1_tarski(A_24, k2_xboole_0(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.40/1.41  tff(c_39, plain, (![A_6]: (r1_tarski(A_6, A_6))), inference(superposition, [status(thm), theory('equality')], [c_6, c_36])).
% 2.40/1.41  tff(c_79, plain, (![A_6]: (k2_xboole_0(A_6, A_6)=A_6)), inference(resolution, [status(thm)], [c_39, c_64])).
% 2.40/1.41  tff(c_12, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.40/1.41  tff(c_475, plain, (![A_57, B_58]: (k2_xboole_0(A_57, k2_xboole_0(A_57, B_58))=k2_xboole_0(A_57, B_58))), inference(resolution, [status(thm)], [c_12, c_64])).
% 2.40/1.41  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.40/1.41  tff(c_132, plain, (![A_39, B_40]: (k4_xboole_0(k2_xboole_0(A_39, B_40), B_40)=k4_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.40/1.41  tff(c_138, plain, (![B_40, A_39]: (k2_xboole_0(B_40, k4_xboole_0(A_39, B_40))=k2_xboole_0(B_40, k2_xboole_0(A_39, B_40)))), inference(superposition, [status(thm), theory('equality')], [c_132, c_8])).
% 2.40/1.41  tff(c_155, plain, (![B_40, A_39]: (k2_xboole_0(B_40, k2_xboole_0(A_39, B_40))=k2_xboole_0(B_40, A_39))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_138])).
% 2.40/1.41  tff(c_484, plain, (![A_57, B_58]: (k2_xboole_0(k2_xboole_0(A_57, B_58), k2_xboole_0(A_57, B_58))=k2_xboole_0(k2_xboole_0(A_57, B_58), A_57))), inference(superposition, [status(thm), theory('equality')], [c_475, c_155])).
% 2.40/1.41  tff(c_589, plain, (![A_59, B_60]: (k2_xboole_0(k2_xboole_0(A_59, B_60), A_59)=k2_xboole_0(A_59, B_60))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_484])).
% 2.40/1.41  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, k2_xboole_0(C_3, B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.40/1.41  tff(c_676, plain, (![A_61, A_62, B_63]: (r1_tarski(A_61, k2_xboole_0(A_62, B_63)) | ~r1_tarski(A_61, A_62))), inference(superposition, [status(thm), theory('equality')], [c_589, c_2])).
% 2.40/1.41  tff(c_935, plain, (![A_72]: (r1_tarski(A_72, k1_tarski('#skF_3')) | ~r1_tarski(A_72, k2_tarski('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_77, c_676])).
% 2.40/1.41  tff(c_961, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_935])).
% 2.40/1.41  tff(c_22, plain, (![B_22, A_21]: (B_22=A_21 | ~r1_tarski(k1_tarski(A_21), k1_tarski(B_22)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.40/1.41  tff(c_966, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_961, c_22])).
% 2.40/1.41  tff(c_973, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_966])).
% 2.40/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.41  
% 2.40/1.41  Inference rules
% 2.40/1.41  ----------------------
% 2.40/1.41  #Ref     : 0
% 2.40/1.41  #Sup     : 228
% 2.40/1.41  #Fact    : 0
% 2.40/1.41  #Define  : 0
% 2.40/1.41  #Split   : 0
% 2.40/1.41  #Chain   : 0
% 2.40/1.41  #Close   : 0
% 2.40/1.41  
% 2.40/1.41  Ordering : KBO
% 2.40/1.41  
% 2.40/1.41  Simplification rules
% 2.40/1.41  ----------------------
% 2.40/1.41  #Subsume      : 6
% 2.40/1.41  #Demod        : 162
% 2.40/1.41  #Tautology    : 171
% 2.40/1.41  #SimpNegUnit  : 1
% 2.40/1.41  #BackRed      : 1
% 2.40/1.41  
% 2.40/1.41  #Partial instantiations: 0
% 2.40/1.41  #Strategies tried      : 1
% 2.40/1.41  
% 2.40/1.41  Timing (in seconds)
% 2.40/1.41  ----------------------
% 2.40/1.42  Preprocessing        : 0.29
% 2.40/1.42  Parsing              : 0.16
% 2.40/1.42  CNF conversion       : 0.02
% 2.40/1.42  Main loop            : 0.30
% 2.40/1.42  Inferencing          : 0.12
% 2.40/1.42  Reduction            : 0.11
% 2.40/1.42  Demodulation         : 0.09
% 2.40/1.42  BG Simplification    : 0.01
% 2.40/1.42  Subsumption          : 0.04
% 2.40/1.42  Abstraction          : 0.02
% 2.40/1.42  MUC search           : 0.00
% 2.40/1.42  Cooper               : 0.00
% 2.40/1.42  Total                : 0.62
% 2.40/1.42  Index Insertion      : 0.00
% 2.40/1.42  Index Deletion       : 0.00
% 2.40/1.42  Index Matching       : 0.00
% 2.40/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
