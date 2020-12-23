%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:31 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   40 (  45 expanded)
%              Number of leaves         :   24 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   41 (  50 expanded)
%              Number of equality atoms :   17 (  21 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > #nlpp > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k4_yellow_0,type,(
    k4_yellow_0: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_46,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_48,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_57,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k3_tarski(A),A)
       => k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_60,negated_conjecture,(
    ~ ! [A] : k4_yellow_0(k3_yellow_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_yellow_1)).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    ! [A_12] : k3_tarski(k1_zfmisc_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_26,plain,(
    ! [A_13] : k9_setfam_1(A_13) = k1_zfmisc_1(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_30,plain,(
    ! [A_15] : k2_yellow_1(k9_setfam_1(A_15)) = k3_yellow_1(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_33,plain,(
    ! [A_15] : k2_yellow_1(k1_zfmisc_1(A_15)) = k3_yellow_1(A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_30])).

tff(c_14,plain,(
    ! [C_11,A_7] :
      ( r2_hidden(C_11,k1_zfmisc_1(A_7))
      | ~ r1_tarski(C_11,A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_96,plain,(
    ! [A_32] :
      ( k4_yellow_0(k2_yellow_1(A_32)) = k3_tarski(A_32)
      | ~ r2_hidden(k3_tarski(A_32),A_32)
      | v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_100,plain,(
    ! [A_7] :
      ( k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_7))) = k3_tarski(k1_zfmisc_1(A_7))
      | v1_xboole_0(k1_zfmisc_1(A_7))
      | ~ r1_tarski(k3_tarski(k1_zfmisc_1(A_7)),A_7) ) ),
    inference(resolution,[status(thm)],[c_14,c_96])).

tff(c_108,plain,(
    ! [A_33] :
      ( k4_yellow_0(k3_yellow_1(A_33)) = A_33
      | v1_xboole_0(k1_zfmisc_1(A_33)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_24,c_33,c_24,c_100])).

tff(c_75,plain,(
    ! [C_25,A_26] :
      ( r2_hidden(C_25,k1_zfmisc_1(A_26))
      | ~ r1_tarski(C_25,A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_83,plain,(
    ! [A_26,C_25] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_26))
      | ~ r1_tarski(C_25,A_26) ) ),
    inference(resolution,[status(thm)],[c_75,c_2])).

tff(c_112,plain,(
    ! [C_34,A_35] :
      ( ~ r1_tarski(C_34,A_35)
      | k4_yellow_0(k3_yellow_1(A_35)) = A_35 ) ),
    inference(resolution,[status(thm)],[c_108,c_83])).

tff(c_118,plain,(
    ! [B_6] : k4_yellow_0(k3_yellow_1(B_6)) = B_6 ),
    inference(resolution,[status(thm)],[c_10,c_112])).

tff(c_32,plain,(
    k4_yellow_0(k3_yellow_1('#skF_4')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 20:03:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.14  
% 1.63/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.14  %$ r2_hidden > r1_tarski > v1_xboole_0 > #nlpp > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.63/1.14  
% 1.63/1.14  %Foreground sorts:
% 1.63/1.14  
% 1.63/1.14  
% 1.63/1.14  %Background operators:
% 1.63/1.14  
% 1.63/1.14  
% 1.63/1.14  %Foreground operators:
% 1.63/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.63/1.14  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 1.63/1.14  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.63/1.14  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 1.63/1.14  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.63/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.63/1.14  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 1.63/1.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.63/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.14  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.63/1.14  tff(k4_yellow_0, type, k4_yellow_0: $i > $i).
% 1.63/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.63/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.14  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.63/1.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.63/1.14  
% 1.63/1.15  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.63/1.15  tff(f_46, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 1.63/1.15  tff(f_48, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 1.63/1.15  tff(f_57, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_yellow_1)).
% 1.63/1.15  tff(f_44, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.63/1.15  tff(f_55, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k3_tarski(A), A) => (k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow_1)).
% 1.63/1.15  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.63/1.15  tff(f_60, negated_conjecture, ~(![A]: (k4_yellow_0(k3_yellow_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_yellow_1)).
% 1.63/1.15  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.63/1.15  tff(c_24, plain, (![A_12]: (k3_tarski(k1_zfmisc_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.63/1.15  tff(c_26, plain, (![A_13]: (k9_setfam_1(A_13)=k1_zfmisc_1(A_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.63/1.15  tff(c_30, plain, (![A_15]: (k2_yellow_1(k9_setfam_1(A_15))=k3_yellow_1(A_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.63/1.15  tff(c_33, plain, (![A_15]: (k2_yellow_1(k1_zfmisc_1(A_15))=k3_yellow_1(A_15))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_30])).
% 1.63/1.15  tff(c_14, plain, (![C_11, A_7]: (r2_hidden(C_11, k1_zfmisc_1(A_7)) | ~r1_tarski(C_11, A_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.63/1.15  tff(c_96, plain, (![A_32]: (k4_yellow_0(k2_yellow_1(A_32))=k3_tarski(A_32) | ~r2_hidden(k3_tarski(A_32), A_32) | v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.63/1.15  tff(c_100, plain, (![A_7]: (k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_7)))=k3_tarski(k1_zfmisc_1(A_7)) | v1_xboole_0(k1_zfmisc_1(A_7)) | ~r1_tarski(k3_tarski(k1_zfmisc_1(A_7)), A_7))), inference(resolution, [status(thm)], [c_14, c_96])).
% 1.63/1.15  tff(c_108, plain, (![A_33]: (k4_yellow_0(k3_yellow_1(A_33))=A_33 | v1_xboole_0(k1_zfmisc_1(A_33)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_24, c_33, c_24, c_100])).
% 1.63/1.15  tff(c_75, plain, (![C_25, A_26]: (r2_hidden(C_25, k1_zfmisc_1(A_26)) | ~r1_tarski(C_25, A_26))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.63/1.15  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.63/1.15  tff(c_83, plain, (![A_26, C_25]: (~v1_xboole_0(k1_zfmisc_1(A_26)) | ~r1_tarski(C_25, A_26))), inference(resolution, [status(thm)], [c_75, c_2])).
% 1.63/1.15  tff(c_112, plain, (![C_34, A_35]: (~r1_tarski(C_34, A_35) | k4_yellow_0(k3_yellow_1(A_35))=A_35)), inference(resolution, [status(thm)], [c_108, c_83])).
% 1.63/1.15  tff(c_118, plain, (![B_6]: (k4_yellow_0(k3_yellow_1(B_6))=B_6)), inference(resolution, [status(thm)], [c_10, c_112])).
% 1.63/1.15  tff(c_32, plain, (k4_yellow_0(k3_yellow_1('#skF_4'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.63/1.15  tff(c_128, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_32])).
% 1.63/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.15  
% 1.63/1.15  Inference rules
% 1.63/1.15  ----------------------
% 1.63/1.15  #Ref     : 0
% 1.63/1.15  #Sup     : 18
% 1.63/1.15  #Fact    : 0
% 1.63/1.15  #Define  : 0
% 1.63/1.15  #Split   : 0
% 1.63/1.15  #Chain   : 0
% 1.63/1.15  #Close   : 0
% 1.63/1.15  
% 1.63/1.15  Ordering : KBO
% 1.63/1.15  
% 1.63/1.15  Simplification rules
% 1.63/1.15  ----------------------
% 1.63/1.15  #Subsume      : 1
% 1.63/1.15  #Demod        : 12
% 1.63/1.15  #Tautology    : 12
% 1.63/1.15  #SimpNegUnit  : 0
% 1.63/1.15  #BackRed      : 1
% 1.63/1.15  
% 1.63/1.15  #Partial instantiations: 0
% 1.63/1.15  #Strategies tried      : 1
% 1.63/1.15  
% 1.63/1.15  Timing (in seconds)
% 1.63/1.15  ----------------------
% 1.63/1.15  Preprocessing        : 0.28
% 1.63/1.15  Parsing              : 0.14
% 1.63/1.15  CNF conversion       : 0.02
% 1.63/1.15  Main loop            : 0.11
% 1.63/1.15  Inferencing          : 0.04
% 1.63/1.15  Reduction            : 0.04
% 1.63/1.15  Demodulation         : 0.03
% 1.63/1.15  BG Simplification    : 0.01
% 1.63/1.15  Subsumption          : 0.02
% 1.63/1.15  Abstraction          : 0.01
% 1.63/1.15  MUC search           : 0.00
% 1.63/1.15  Cooper               : 0.00
% 1.63/1.15  Total                : 0.41
% 1.63/1.15  Index Insertion      : 0.00
% 1.63/1.15  Index Deletion       : 0.00
% 1.63/1.15  Index Matching       : 0.00
% 1.63/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
