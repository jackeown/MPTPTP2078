%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:32 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   36 (  38 expanded)
%              Number of leaves         :   23 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   33 (  35 expanded)
%              Number of equality atoms :   16 (  18 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > #nlpp > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k4_yellow_0,type,(
    k4_yellow_0: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_43,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_40,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_54,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_52,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k3_tarski(A),A)
       => k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

tff(f_57,negated_conjecture,(
    ~ ! [A] : k4_yellow_0(k3_yellow_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_yellow_1)).

tff(c_22,plain,(
    ! [A_9] : ~ v1_xboole_0(k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_8] : k3_tarski(k1_zfmisc_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_24,plain,(
    ! [A_10] : k9_setfam_1(A_10) = k1_zfmisc_1(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28,plain,(
    ! [A_12] : k2_yellow_1(k9_setfam_1(A_12)) = k3_yellow_1(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_31,plain,(
    ! [A_12] : k2_yellow_1(k1_zfmisc_1(A_12)) = k3_yellow_1(A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28])).

tff(c_10,plain,(
    ! [C_7,A_3] :
      ( r2_hidden(C_7,k1_zfmisc_1(A_3))
      | ~ r1_tarski(C_7,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_75,plain,(
    ! [A_24] :
      ( k4_yellow_0(k2_yellow_1(A_24)) = k3_tarski(A_24)
      | ~ r2_hidden(k3_tarski(A_24),A_24)
      | v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_79,plain,(
    ! [A_3] :
      ( k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_3))) = k3_tarski(k1_zfmisc_1(A_3))
      | v1_xboole_0(k1_zfmisc_1(A_3))
      | ~ r1_tarski(k3_tarski(k1_zfmisc_1(A_3)),A_3) ) ),
    inference(resolution,[status(thm)],[c_10,c_75])).

tff(c_85,plain,(
    ! [A_3] :
      ( k4_yellow_0(k3_yellow_1(A_3)) = A_3
      | v1_xboole_0(k1_zfmisc_1(A_3)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_20,c_31,c_20,c_79])).

tff(c_86,plain,(
    ! [A_3] : k4_yellow_0(k3_yellow_1(A_3)) = A_3 ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_85])).

tff(c_30,plain,(
    k4_yellow_0(k3_yellow_1('#skF_3')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_91,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:40:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.15  
% 1.64/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.15  %$ r2_hidden > r1_tarski > v1_xboole_0 > #nlpp > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > #skF_3 > #skF_2 > #skF_1
% 1.64/1.15  
% 1.64/1.15  %Foreground sorts:
% 1.64/1.15  
% 1.64/1.15  
% 1.64/1.15  %Background operators:
% 1.64/1.15  
% 1.64/1.15  
% 1.64/1.15  %Foreground operators:
% 1.64/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.64/1.15  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 1.64/1.15  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 1.64/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.15  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 1.64/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.64/1.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.64/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.15  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.64/1.15  tff(k4_yellow_0, type, k4_yellow_0: $i > $i).
% 1.64/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.15  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.64/1.15  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.64/1.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.64/1.15  
% 1.78/1.16  tff(f_43, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.78/1.16  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.78/1.16  tff(f_40, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 1.78/1.16  tff(f_45, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 1.78/1.16  tff(f_54, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_1)).
% 1.78/1.16  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.78/1.16  tff(f_52, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k3_tarski(A), A) => (k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow_1)).
% 1.78/1.16  tff(f_57, negated_conjecture, ~(![A]: (k4_yellow_0(k3_yellow_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_yellow_1)).
% 1.78/1.16  tff(c_22, plain, (![A_9]: (~v1_xboole_0(k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.78/1.16  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.78/1.16  tff(c_20, plain, (![A_8]: (k3_tarski(k1_zfmisc_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.78/1.16  tff(c_24, plain, (![A_10]: (k9_setfam_1(A_10)=k1_zfmisc_1(A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.78/1.16  tff(c_28, plain, (![A_12]: (k2_yellow_1(k9_setfam_1(A_12))=k3_yellow_1(A_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.78/1.16  tff(c_31, plain, (![A_12]: (k2_yellow_1(k1_zfmisc_1(A_12))=k3_yellow_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28])).
% 1.78/1.16  tff(c_10, plain, (![C_7, A_3]: (r2_hidden(C_7, k1_zfmisc_1(A_3)) | ~r1_tarski(C_7, A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.78/1.16  tff(c_75, plain, (![A_24]: (k4_yellow_0(k2_yellow_1(A_24))=k3_tarski(A_24) | ~r2_hidden(k3_tarski(A_24), A_24) | v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.78/1.16  tff(c_79, plain, (![A_3]: (k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_3)))=k3_tarski(k1_zfmisc_1(A_3)) | v1_xboole_0(k1_zfmisc_1(A_3)) | ~r1_tarski(k3_tarski(k1_zfmisc_1(A_3)), A_3))), inference(resolution, [status(thm)], [c_10, c_75])).
% 1.78/1.16  tff(c_85, plain, (![A_3]: (k4_yellow_0(k3_yellow_1(A_3))=A_3 | v1_xboole_0(k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_20, c_31, c_20, c_79])).
% 1.78/1.16  tff(c_86, plain, (![A_3]: (k4_yellow_0(k3_yellow_1(A_3))=A_3)), inference(negUnitSimplification, [status(thm)], [c_22, c_85])).
% 1.78/1.16  tff(c_30, plain, (k4_yellow_0(k3_yellow_1('#skF_3'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.78/1.16  tff(c_91, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_30])).
% 1.78/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.16  
% 1.78/1.16  Inference rules
% 1.78/1.16  ----------------------
% 1.78/1.16  #Ref     : 0
% 1.78/1.16  #Sup     : 10
% 1.78/1.16  #Fact    : 0
% 1.78/1.16  #Define  : 0
% 1.78/1.16  #Split   : 0
% 1.78/1.16  #Chain   : 0
% 1.78/1.16  #Close   : 0
% 1.78/1.16  
% 1.78/1.16  Ordering : KBO
% 1.78/1.16  
% 1.78/1.16  Simplification rules
% 1.78/1.16  ----------------------
% 1.78/1.16  #Subsume      : 0
% 1.78/1.16  #Demod        : 10
% 1.78/1.16  #Tautology    : 9
% 1.78/1.16  #SimpNegUnit  : 2
% 1.78/1.16  #BackRed      : 1
% 1.78/1.16  
% 1.78/1.16  #Partial instantiations: 0
% 1.78/1.16  #Strategies tried      : 1
% 1.78/1.16  
% 1.78/1.16  Timing (in seconds)
% 1.78/1.16  ----------------------
% 1.78/1.16  Preprocessing        : 0.30
% 1.78/1.16  Parsing              : 0.15
% 1.78/1.16  CNF conversion       : 0.02
% 1.78/1.16  Main loop            : 0.09
% 1.78/1.16  Inferencing          : 0.03
% 1.78/1.16  Reduction            : 0.03
% 1.78/1.16  Demodulation         : 0.03
% 1.78/1.16  BG Simplification    : 0.01
% 1.78/1.16  Subsumption          : 0.01
% 1.78/1.16  Abstraction          : 0.01
% 1.78/1.16  MUC search           : 0.00
% 1.78/1.16  Cooper               : 0.00
% 1.78/1.16  Total                : 0.42
% 1.78/1.16  Index Insertion      : 0.00
% 1.78/1.16  Index Deletion       : 0.00
% 1.78/1.16  Index Matching       : 0.00
% 1.78/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
