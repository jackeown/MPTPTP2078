%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:31 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   38 (  41 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   40 (  45 expanded)
%              Number of equality atoms :   15 (  16 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > #nlpp > k9_setfam_1 > k3_yellow_1 > k3_yellow_0 > k2_yellow_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_50,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_48,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k1_xboole_0,A)
       => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_53,negated_conjecture,(
    ~ ! [A] : k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow_1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [C_8,A_4] :
      ( r2_hidden(C_8,k1_zfmisc_1(A_4))
      | ~ r1_tarski(C_8,A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_9] : k9_setfam_1(A_9) = k1_zfmisc_1(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [A_11] : k2_yellow_1(k9_setfam_1(A_11)) = k3_yellow_1(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_25,plain,(
    ! [A_11] : k2_yellow_1(k1_zfmisc_1(A_11)) = k3_yellow_1(A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_22])).

tff(c_57,plain,(
    ! [A_23] :
      ( k3_yellow_0(k2_yellow_1(A_23)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,A_23)
      | v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_79,plain,(
    ! [A_26] :
      ( k3_yellow_0(k3_yellow_1(A_26)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(A_26))
      | v1_xboole_0(k1_zfmisc_1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25,c_57])).

tff(c_83,plain,(
    ! [A_4] :
      ( k3_yellow_0(k3_yellow_1(A_4)) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_4))
      | ~ r1_tarski(k1_xboole_0,A_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_79])).

tff(c_87,plain,(
    ! [A_27] :
      ( k3_yellow_0(k3_yellow_1(A_27)) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_27)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_83])).

tff(c_46,plain,(
    ! [C_17,A_18] :
      ( r2_hidden(C_17,k1_zfmisc_1(A_18))
      | ~ r1_tarski(C_17,A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( ~ v1_xboole_0(B_3)
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,(
    ! [A_18,C_17] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_18))
      | ~ r1_tarski(C_17,A_18) ) ),
    inference(resolution,[status(thm)],[c_46,c_4])).

tff(c_91,plain,(
    ! [C_28,A_29] :
      ( ~ r1_tarski(C_28,A_29)
      | k3_yellow_0(k3_yellow_1(A_29)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_87,c_50])).

tff(c_94,plain,(
    ! [A_1] : k3_yellow_0(k3_yellow_1(A_1)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_91])).

tff(c_24,plain,(
    k3_yellow_0(k3_yellow_1('#skF_3')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_99,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:19:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.14  
% 1.79/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.14  %$ r2_hidden > r1_tarski > v1_xboole_0 > #nlpp > k9_setfam_1 > k3_yellow_1 > k3_yellow_0 > k2_yellow_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 1.79/1.14  
% 1.79/1.14  %Foreground sorts:
% 1.79/1.14  
% 1.79/1.14  
% 1.79/1.14  %Background operators:
% 1.79/1.14  
% 1.79/1.14  
% 1.79/1.14  %Foreground operators:
% 1.79/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.79/1.14  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 1.79/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.79/1.14  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 1.79/1.14  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 1.79/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.79/1.14  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 1.79/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.79/1.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.79/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.14  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.79/1.14  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.79/1.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.79/1.14  
% 1.79/1.15  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.79/1.15  tff(f_39, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.79/1.15  tff(f_41, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 1.79/1.15  tff(f_50, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_1)).
% 1.79/1.15  tff(f_48, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow_1)).
% 1.79/1.15  tff(f_32, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_boole)).
% 1.79/1.15  tff(f_53, negated_conjecture, ~(![A]: (k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_yellow_1)).
% 1.79/1.15  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.79/1.15  tff(c_8, plain, (![C_8, A_4]: (r2_hidden(C_8, k1_zfmisc_1(A_4)) | ~r1_tarski(C_8, A_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.79/1.15  tff(c_18, plain, (![A_9]: (k9_setfam_1(A_9)=k1_zfmisc_1(A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.79/1.15  tff(c_22, plain, (![A_11]: (k2_yellow_1(k9_setfam_1(A_11))=k3_yellow_1(A_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.79/1.15  tff(c_25, plain, (![A_11]: (k2_yellow_1(k1_zfmisc_1(A_11))=k3_yellow_1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_22])).
% 1.79/1.15  tff(c_57, plain, (![A_23]: (k3_yellow_0(k2_yellow_1(A_23))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, A_23) | v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.79/1.15  tff(c_79, plain, (![A_26]: (k3_yellow_0(k3_yellow_1(A_26))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, k1_zfmisc_1(A_26)) | v1_xboole_0(k1_zfmisc_1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_25, c_57])).
% 1.79/1.15  tff(c_83, plain, (![A_4]: (k3_yellow_0(k3_yellow_1(A_4))=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_4)) | ~r1_tarski(k1_xboole_0, A_4))), inference(resolution, [status(thm)], [c_8, c_79])).
% 1.79/1.15  tff(c_87, plain, (![A_27]: (k3_yellow_0(k3_yellow_1(A_27))=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_27)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_83])).
% 1.79/1.15  tff(c_46, plain, (![C_17, A_18]: (r2_hidden(C_17, k1_zfmisc_1(A_18)) | ~r1_tarski(C_17, A_18))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.79/1.15  tff(c_4, plain, (![B_3, A_2]: (~v1_xboole_0(B_3) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.79/1.15  tff(c_50, plain, (![A_18, C_17]: (~v1_xboole_0(k1_zfmisc_1(A_18)) | ~r1_tarski(C_17, A_18))), inference(resolution, [status(thm)], [c_46, c_4])).
% 1.79/1.15  tff(c_91, plain, (![C_28, A_29]: (~r1_tarski(C_28, A_29) | k3_yellow_0(k3_yellow_1(A_29))=k1_xboole_0)), inference(resolution, [status(thm)], [c_87, c_50])).
% 1.79/1.15  tff(c_94, plain, (![A_1]: (k3_yellow_0(k3_yellow_1(A_1))=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_91])).
% 1.79/1.15  tff(c_24, plain, (k3_yellow_0(k3_yellow_1('#skF_3'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.79/1.15  tff(c_99, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_24])).
% 1.79/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.15  
% 1.79/1.15  Inference rules
% 1.79/1.15  ----------------------
% 1.79/1.15  #Ref     : 0
% 1.79/1.15  #Sup     : 14
% 1.79/1.15  #Fact    : 0
% 1.79/1.15  #Define  : 0
% 1.79/1.15  #Split   : 0
% 1.79/1.15  #Chain   : 0
% 1.79/1.15  #Close   : 0
% 1.79/1.15  
% 1.79/1.15  Ordering : KBO
% 1.79/1.15  
% 1.79/1.15  Simplification rules
% 1.79/1.15  ----------------------
% 1.79/1.15  #Subsume      : 2
% 1.79/1.15  #Demod        : 5
% 1.79/1.15  #Tautology    : 9
% 1.79/1.15  #SimpNegUnit  : 0
% 1.79/1.15  #BackRed      : 1
% 1.79/1.15  
% 1.79/1.15  #Partial instantiations: 0
% 1.79/1.15  #Strategies tried      : 1
% 1.79/1.15  
% 1.79/1.15  Timing (in seconds)
% 1.79/1.15  ----------------------
% 1.79/1.15  Preprocessing        : 0.29
% 1.79/1.15  Parsing              : 0.16
% 1.79/1.15  CNF conversion       : 0.02
% 1.79/1.15  Main loop            : 0.11
% 1.79/1.15  Inferencing          : 0.04
% 1.79/1.15  Reduction            : 0.03
% 1.79/1.15  Demodulation         : 0.02
% 1.79/1.15  BG Simplification    : 0.01
% 1.79/1.15  Subsumption          : 0.02
% 1.79/1.15  Abstraction          : 0.01
% 1.79/1.15  MUC search           : 0.00
% 1.79/1.15  Cooper               : 0.00
% 1.79/1.15  Total                : 0.43
% 1.79/1.15  Index Insertion      : 0.00
% 1.79/1.15  Index Deletion       : 0.00
% 1.79/1.15  Index Matching       : 0.00
% 1.79/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
