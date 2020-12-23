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
% DateTime   : Thu Dec  3 09:44:45 EST 2020

% Result     : Theorem 8.79s
% Output     : CNFRefutation 8.79s
% Verified   : 
% Statistics : Number of formulae       :   46 (  48 expanded)
%              Number of leaves         :   25 (  27 expanded)
%              Depth                    :    5
%              Number of atoms          :   33 (  36 expanded)
%              Number of equality atoms :   24 (  26 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_88,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_112,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_110,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_76,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_117,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k4_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_xboole_1)).

tff(c_170,plain,(
    ! [B_84,A_85] : k5_xboole_0(B_84,A_85) = k5_xboole_0(A_85,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_50,plain,(
    ! [A_48] : k5_xboole_0(A_48,k1_xboole_0) = A_48 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_186,plain,(
    ! [A_85] : k5_xboole_0(k1_xboole_0,A_85) = A_85 ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_50])).

tff(c_66,plain,(
    ! [A_63] : k5_xboole_0(A_63,A_63) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1542,plain,(
    ! [A_155,B_156,C_157] : k5_xboole_0(k5_xboole_0(A_155,B_156),C_157) = k5_xboole_0(A_155,k5_xboole_0(B_156,C_157)) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1588,plain,(
    ! [A_63,C_157] : k5_xboole_0(A_63,k5_xboole_0(A_63,C_157)) = k5_xboole_0(k1_xboole_0,C_157) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_1542])).

tff(c_1606,plain,(
    ! [A_63,C_157] : k5_xboole_0(A_63,k5_xboole_0(A_63,C_157)) = C_157 ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_1588])).

tff(c_2278,plain,(
    ! [A_176,B_177] : k4_xboole_0(k2_xboole_0(A_176,B_177),k3_xboole_0(A_176,B_177)) = k5_xboole_0(A_176,B_177) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_28,plain,(
    ! [A_27,B_28] : r1_tarski(k4_xboole_0(A_27,B_28),A_27) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_355,plain,(
    ! [A_98,B_99] :
      ( k4_xboole_0(A_98,B_99) = k1_xboole_0
      | ~ r1_tarski(A_98,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_371,plain,(
    ! [A_27,B_28] : k4_xboole_0(k4_xboole_0(A_27,B_28),A_27) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_355])).

tff(c_14784,plain,(
    ! [A_509,B_510] : k4_xboole_0(k5_xboole_0(A_509,B_510),k2_xboole_0(A_509,B_510)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2278,c_371])).

tff(c_14998,plain,(
    ! [C_157,A_63] : k4_xboole_0(C_157,k2_xboole_0(A_63,k5_xboole_0(A_63,C_157))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1606,c_14784])).

tff(c_38,plain,(
    ! [A_34,B_35,C_36] : k4_xboole_0(k4_xboole_0(A_34,B_35),C_36) = k4_xboole_0(A_34,k2_xboole_0(B_35,C_36)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_555,plain,(
    ! [A_108,B_109] :
      ( r1_tarski(A_108,B_109)
      | k4_xboole_0(A_108,B_109) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_70,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_3','#skF_4'),k5_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_72,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_3','#skF_4'),k5_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_70])).

tff(c_563,plain,(
    k4_xboole_0(k4_xboole_0('#skF_3','#skF_4'),k5_xboole_0('#skF_4','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_555,c_72])).

tff(c_1310,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_4',k5_xboole_0('#skF_4','#skF_3'))) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_563])).

tff(c_17666,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14998,c_1310])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:12:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.79/3.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.79/3.31  
% 8.79/3.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.79/3.31  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 8.79/3.31  
% 8.79/3.31  %Foreground sorts:
% 8.79/3.31  
% 8.79/3.31  
% 8.79/3.31  %Background operators:
% 8.79/3.31  
% 8.79/3.31  
% 8.79/3.31  %Foreground operators:
% 8.79/3.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.79/3.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.79/3.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.79/3.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.79/3.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.79/3.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.79/3.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.79/3.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.79/3.31  tff('#skF_3', type, '#skF_3': $i).
% 8.79/3.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.79/3.31  tff('#skF_4', type, '#skF_4': $i).
% 8.79/3.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.79/3.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.79/3.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.79/3.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.79/3.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.79/3.31  
% 8.79/3.32  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 8.79/3.32  tff(f_88, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 8.79/3.32  tff(f_112, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 8.79/3.32  tff(f_110, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 8.79/3.32  tff(f_58, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l98_xboole_1)).
% 8.79/3.32  tff(f_66, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.79/3.32  tff(f_70, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 8.79/3.32  tff(f_76, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 8.79/3.32  tff(f_117, negated_conjecture, ~(![A, B]: r1_tarski(k4_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_xboole_1)).
% 8.79/3.32  tff(c_170, plain, (![B_84, A_85]: (k5_xboole_0(B_84, A_85)=k5_xboole_0(A_85, B_84))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.79/3.32  tff(c_50, plain, (![A_48]: (k5_xboole_0(A_48, k1_xboole_0)=A_48)), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.79/3.32  tff(c_186, plain, (![A_85]: (k5_xboole_0(k1_xboole_0, A_85)=A_85)), inference(superposition, [status(thm), theory('equality')], [c_170, c_50])).
% 8.79/3.32  tff(c_66, plain, (![A_63]: (k5_xboole_0(A_63, A_63)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.79/3.32  tff(c_1542, plain, (![A_155, B_156, C_157]: (k5_xboole_0(k5_xboole_0(A_155, B_156), C_157)=k5_xboole_0(A_155, k5_xboole_0(B_156, C_157)))), inference(cnfTransformation, [status(thm)], [f_110])).
% 8.79/3.32  tff(c_1588, plain, (![A_63, C_157]: (k5_xboole_0(A_63, k5_xboole_0(A_63, C_157))=k5_xboole_0(k1_xboole_0, C_157))), inference(superposition, [status(thm), theory('equality')], [c_66, c_1542])).
% 8.79/3.32  tff(c_1606, plain, (![A_63, C_157]: (k5_xboole_0(A_63, k5_xboole_0(A_63, C_157))=C_157)), inference(demodulation, [status(thm), theory('equality')], [c_186, c_1588])).
% 8.79/3.32  tff(c_2278, plain, (![A_176, B_177]: (k4_xboole_0(k2_xboole_0(A_176, B_177), k3_xboole_0(A_176, B_177))=k5_xboole_0(A_176, B_177))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.79/3.32  tff(c_28, plain, (![A_27, B_28]: (r1_tarski(k4_xboole_0(A_27, B_28), A_27))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.79/3.32  tff(c_355, plain, (![A_98, B_99]: (k4_xboole_0(A_98, B_99)=k1_xboole_0 | ~r1_tarski(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.79/3.32  tff(c_371, plain, (![A_27, B_28]: (k4_xboole_0(k4_xboole_0(A_27, B_28), A_27)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_355])).
% 8.79/3.32  tff(c_14784, plain, (![A_509, B_510]: (k4_xboole_0(k5_xboole_0(A_509, B_510), k2_xboole_0(A_509, B_510))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2278, c_371])).
% 8.79/3.32  tff(c_14998, plain, (![C_157, A_63]: (k4_xboole_0(C_157, k2_xboole_0(A_63, k5_xboole_0(A_63, C_157)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1606, c_14784])).
% 8.79/3.32  tff(c_38, plain, (![A_34, B_35, C_36]: (k4_xboole_0(k4_xboole_0(A_34, B_35), C_36)=k4_xboole_0(A_34, k2_xboole_0(B_35, C_36)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.79/3.32  tff(c_555, plain, (![A_108, B_109]: (r1_tarski(A_108, B_109) | k4_xboole_0(A_108, B_109)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.79/3.32  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.79/3.32  tff(c_70, plain, (~r1_tarski(k4_xboole_0('#skF_3', '#skF_4'), k5_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.79/3.32  tff(c_72, plain, (~r1_tarski(k4_xboole_0('#skF_3', '#skF_4'), k5_xboole_0('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_70])).
% 8.79/3.32  tff(c_563, plain, (k4_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), k5_xboole_0('#skF_4', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_555, c_72])).
% 8.79/3.32  tff(c_1310, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', k5_xboole_0('#skF_4', '#skF_3')))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_563])).
% 8.79/3.32  tff(c_17666, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14998, c_1310])).
% 8.79/3.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.79/3.32  
% 8.79/3.32  Inference rules
% 8.79/3.32  ----------------------
% 8.79/3.32  #Ref     : 1
% 8.79/3.32  #Sup     : 4584
% 8.79/3.32  #Fact    : 0
% 8.79/3.32  #Define  : 0
% 8.79/3.32  #Split   : 2
% 8.79/3.32  #Chain   : 0
% 8.79/3.32  #Close   : 0
% 8.79/3.32  
% 8.79/3.32  Ordering : KBO
% 8.79/3.32  
% 8.79/3.32  Simplification rules
% 8.79/3.32  ----------------------
% 8.79/3.32  #Subsume      : 747
% 8.79/3.32  #Demod        : 3182
% 8.79/3.32  #Tautology    : 2289
% 8.79/3.32  #SimpNegUnit  : 7
% 8.79/3.32  #BackRed      : 3
% 8.79/3.32  
% 8.79/3.32  #Partial instantiations: 0
% 8.79/3.32  #Strategies tried      : 1
% 8.79/3.32  
% 8.79/3.32  Timing (in seconds)
% 8.79/3.32  ----------------------
% 8.79/3.33  Preprocessing        : 0.32
% 8.79/3.33  Parsing              : 0.17
% 8.79/3.33  CNF conversion       : 0.02
% 8.79/3.33  Main loop            : 2.23
% 8.79/3.33  Inferencing          : 0.50
% 8.79/3.33  Reduction            : 1.12
% 8.79/3.33  Demodulation         : 0.93
% 8.79/3.33  BG Simplification    : 0.06
% 8.79/3.33  Subsumption          : 0.40
% 8.79/3.33  Abstraction          : 0.08
% 8.79/3.33  MUC search           : 0.00
% 8.79/3.33  Cooper               : 0.00
% 8.79/3.33  Total                : 2.58
% 8.79/3.33  Index Insertion      : 0.00
% 8.79/3.33  Index Deletion       : 0.00
% 8.79/3.33  Index Matching       : 0.00
% 8.79/3.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
