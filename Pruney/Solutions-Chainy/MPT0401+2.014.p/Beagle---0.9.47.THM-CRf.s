%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:40 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   47 (  57 expanded)
%              Number of leaves         :   25 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :   50 (  64 expanded)
%              Number of equality atoms :   12 (  20 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_setfam_1(B,k1_tarski(A))
       => ! [C] :
            ( r2_hidden(C,B)
           => r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_49,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : k3_tarski(k2_xboole_0(A,B)) = k2_xboole_0(k3_tarski(A),k3_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_setfam_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_24,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_26,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_52,plain,(
    ! [A_32,B_33] : k3_tarski(k2_tarski(A_32,B_33)) = k2_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_61,plain,(
    ! [A_8] : k3_tarski(k1_tarski(A_8)) = k2_xboole_0(A_8,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_52])).

tff(c_64,plain,(
    ! [A_8] : k3_tarski(k1_tarski(A_8)) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_61])).

tff(c_28,plain,(
    r1_setfam_1('#skF_2',k1_tarski('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_16,plain,(
    ! [A_18,B_19] :
      ( k2_xboole_0(k1_tarski(A_18),B_19) = B_19
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_163,plain,(
    ! [A_55,B_56] : k2_xboole_0(k3_tarski(A_55),k3_tarski(B_56)) = k3_tarski(k2_xboole_0(A_55,B_56)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_172,plain,(
    ! [A_55,B_56] : r1_tarski(k3_tarski(A_55),k3_tarski(k2_xboole_0(A_55,B_56))) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_6])).

tff(c_22,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(k3_tarski(A_24),k3_tarski(B_25))
      | ~ r1_setfam_1(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_133,plain,(
    ! [A_47,C_48,B_49] :
      ( r1_tarski(A_47,C_48)
      | ~ r1_tarski(B_49,C_48)
      | ~ r1_tarski(A_47,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_646,plain,(
    ! [A_104,B_105,A_106] :
      ( r1_tarski(A_104,k3_tarski(B_105))
      | ~ r1_tarski(A_104,k3_tarski(A_106))
      | ~ r1_setfam_1(A_106,B_105) ) ),
    inference(resolution,[status(thm)],[c_22,c_133])).

tff(c_700,plain,(
    ! [A_107,B_108,B_109] :
      ( r1_tarski(k3_tarski(A_107),k3_tarski(B_108))
      | ~ r1_setfam_1(k2_xboole_0(A_107,B_109),B_108) ) ),
    inference(resolution,[status(thm)],[c_172,c_646])).

tff(c_706,plain,(
    ! [A_18,B_108,B_19] :
      ( r1_tarski(k3_tarski(k1_tarski(A_18)),k3_tarski(B_108))
      | ~ r1_setfam_1(B_19,B_108)
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_700])).

tff(c_716,plain,(
    ! [A_113,B_114,B_115] :
      ( r1_tarski(A_113,k3_tarski(B_114))
      | ~ r1_setfam_1(B_115,B_114)
      | ~ r2_hidden(A_113,B_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_706])).

tff(c_718,plain,(
    ! [A_113] :
      ( r1_tarski(A_113,k3_tarski(k1_tarski('#skF_1')))
      | ~ r2_hidden(A_113,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_716])).

tff(c_721,plain,(
    ! [A_116] :
      ( r1_tarski(A_116,'#skF_1')
      | ~ r2_hidden(A_116,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_718])).

tff(c_724,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_721])).

tff(c_728,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_724])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:04:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.36  
% 2.55/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.36  %$ r2_hidden > r1_tarski > r1_setfam_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.55/1.36  
% 2.55/1.36  %Foreground sorts:
% 2.55/1.36  
% 2.55/1.36  
% 2.55/1.36  %Background operators:
% 2.55/1.36  
% 2.55/1.36  
% 2.55/1.36  %Foreground operators:
% 2.55/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.36  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.55/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.55/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.55/1.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.55/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.55/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.55/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.55/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.55/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.55/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.55/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.55/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.36  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.55/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.55/1.36  
% 2.71/1.37  tff(f_63, negated_conjecture, ~(![A, B]: (r1_setfam_1(B, k1_tarski(A)) => (![C]: (r2_hidden(C, B) => r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_setfam_1)).
% 2.71/1.37  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.71/1.37  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.71/1.37  tff(f_49, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.71/1.37  tff(f_47, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 2.71/1.37  tff(f_51, axiom, (![A, B]: (k3_tarski(k2_xboole_0(A, B)) = k2_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_zfmisc_1)).
% 2.71/1.37  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.71/1.37  tff(f_55, axiom, (![A, B]: (r1_setfam_1(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_setfam_1)).
% 2.71/1.37  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.71/1.37  tff(c_24, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.71/1.37  tff(c_26, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.71/1.37  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.71/1.37  tff(c_8, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.71/1.37  tff(c_52, plain, (![A_32, B_33]: (k3_tarski(k2_tarski(A_32, B_33))=k2_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.71/1.37  tff(c_61, plain, (![A_8]: (k3_tarski(k1_tarski(A_8))=k2_xboole_0(A_8, A_8))), inference(superposition, [status(thm), theory('equality')], [c_8, c_52])).
% 2.71/1.37  tff(c_64, plain, (![A_8]: (k3_tarski(k1_tarski(A_8))=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_61])).
% 2.71/1.37  tff(c_28, plain, (r1_setfam_1('#skF_2', k1_tarski('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.71/1.37  tff(c_16, plain, (![A_18, B_19]: (k2_xboole_0(k1_tarski(A_18), B_19)=B_19 | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.71/1.37  tff(c_163, plain, (![A_55, B_56]: (k2_xboole_0(k3_tarski(A_55), k3_tarski(B_56))=k3_tarski(k2_xboole_0(A_55, B_56)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.71/1.37  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.71/1.37  tff(c_172, plain, (![A_55, B_56]: (r1_tarski(k3_tarski(A_55), k3_tarski(k2_xboole_0(A_55, B_56))))), inference(superposition, [status(thm), theory('equality')], [c_163, c_6])).
% 2.71/1.37  tff(c_22, plain, (![A_24, B_25]: (r1_tarski(k3_tarski(A_24), k3_tarski(B_25)) | ~r1_setfam_1(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.71/1.37  tff(c_133, plain, (![A_47, C_48, B_49]: (r1_tarski(A_47, C_48) | ~r1_tarski(B_49, C_48) | ~r1_tarski(A_47, B_49))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.71/1.37  tff(c_646, plain, (![A_104, B_105, A_106]: (r1_tarski(A_104, k3_tarski(B_105)) | ~r1_tarski(A_104, k3_tarski(A_106)) | ~r1_setfam_1(A_106, B_105))), inference(resolution, [status(thm)], [c_22, c_133])).
% 2.71/1.37  tff(c_700, plain, (![A_107, B_108, B_109]: (r1_tarski(k3_tarski(A_107), k3_tarski(B_108)) | ~r1_setfam_1(k2_xboole_0(A_107, B_109), B_108))), inference(resolution, [status(thm)], [c_172, c_646])).
% 2.71/1.37  tff(c_706, plain, (![A_18, B_108, B_19]: (r1_tarski(k3_tarski(k1_tarski(A_18)), k3_tarski(B_108)) | ~r1_setfam_1(B_19, B_108) | ~r2_hidden(A_18, B_19))), inference(superposition, [status(thm), theory('equality')], [c_16, c_700])).
% 2.71/1.37  tff(c_716, plain, (![A_113, B_114, B_115]: (r1_tarski(A_113, k3_tarski(B_114)) | ~r1_setfam_1(B_115, B_114) | ~r2_hidden(A_113, B_115))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_706])).
% 2.71/1.37  tff(c_718, plain, (![A_113]: (r1_tarski(A_113, k3_tarski(k1_tarski('#skF_1'))) | ~r2_hidden(A_113, '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_716])).
% 2.71/1.37  tff(c_721, plain, (![A_116]: (r1_tarski(A_116, '#skF_1') | ~r2_hidden(A_116, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_718])).
% 2.71/1.37  tff(c_724, plain, (r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_26, c_721])).
% 2.71/1.37  tff(c_728, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_724])).
% 2.71/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.37  
% 2.71/1.37  Inference rules
% 2.71/1.37  ----------------------
% 2.71/1.37  #Ref     : 0
% 2.71/1.37  #Sup     : 191
% 2.71/1.37  #Fact    : 0
% 2.71/1.37  #Define  : 0
% 2.71/1.37  #Split   : 0
% 2.71/1.37  #Chain   : 0
% 2.71/1.37  #Close   : 0
% 2.71/1.37  
% 2.71/1.37  Ordering : KBO
% 2.71/1.37  
% 2.71/1.37  Simplification rules
% 2.71/1.37  ----------------------
% 2.71/1.37  #Subsume      : 16
% 2.71/1.37  #Demod        : 52
% 2.71/1.37  #Tautology    : 52
% 2.71/1.37  #SimpNegUnit  : 1
% 2.71/1.37  #BackRed      : 1
% 2.71/1.37  
% 2.71/1.37  #Partial instantiations: 0
% 2.71/1.37  #Strategies tried      : 1
% 2.71/1.37  
% 2.71/1.37  Timing (in seconds)
% 2.71/1.37  ----------------------
% 2.71/1.37  Preprocessing        : 0.29
% 2.71/1.38  Parsing              : 0.16
% 2.71/1.38  CNF conversion       : 0.02
% 2.71/1.38  Main loop            : 0.32
% 2.71/1.38  Inferencing          : 0.12
% 2.71/1.38  Reduction            : 0.10
% 2.71/1.38  Demodulation         : 0.07
% 2.71/1.38  BG Simplification    : 0.02
% 2.71/1.38  Subsumption          : 0.06
% 2.71/1.38  Abstraction          : 0.02
% 2.71/1.38  MUC search           : 0.00
% 2.71/1.38  Cooper               : 0.00
% 2.71/1.38  Total                : 0.64
% 2.71/1.38  Index Insertion      : 0.00
% 2.71/1.38  Index Deletion       : 0.00
% 2.71/1.38  Index Matching       : 0.00
% 2.71/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
