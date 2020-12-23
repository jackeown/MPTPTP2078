%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:32 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   42 (  46 expanded)
%              Number of leaves         :   24 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   51 (  55 expanded)
%              Number of equality atoms :   19 (  21 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > #skF_1 > #skF_2

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_55,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_61,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_70,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_39,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k3_tarski(A),A)
       => k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

tff(f_73,negated_conjecture,(
    ~ ! [A] : k4_yellow_0(k3_yellow_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_yellow_1)).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_22,plain,(
    ! [A_10] : ~ v1_xboole_0(k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( r2_hidden(B_9,A_8)
      | ~ m1_subset_1(B_9,A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_28,plain,(
    ! [A_13] : k9_setfam_1(A_13) = k1_zfmisc_1(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_32,plain,(
    ! [A_15] : k2_yellow_1(k9_setfam_1(A_15)) = k3_yellow_1(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_35,plain,(
    ! [A_15] : k2_yellow_1(k1_zfmisc_1(A_15)) = k3_yellow_1(A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32])).

tff(c_12,plain,(
    ! [A_7] : k3_tarski(k1_zfmisc_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_131,plain,(
    ! [A_41] :
      ( k4_yellow_0(k2_yellow_1(A_41)) = k3_tarski(A_41)
      | ~ r2_hidden(k3_tarski(A_41),A_41)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_138,plain,(
    ! [A_7] :
      ( k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_7))) = k3_tarski(k1_zfmisc_1(A_7))
      | ~ r2_hidden(A_7,k1_zfmisc_1(A_7))
      | v1_xboole_0(k1_zfmisc_1(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_131])).

tff(c_140,plain,(
    ! [A_7] :
      ( k4_yellow_0(k3_yellow_1(A_7)) = A_7
      | ~ r2_hidden(A_7,k1_zfmisc_1(A_7))
      | v1_xboole_0(k1_zfmisc_1(A_7)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_12,c_138])).

tff(c_142,plain,(
    ! [A_42] :
      ( k4_yellow_0(k3_yellow_1(A_42)) = A_42
      | ~ r2_hidden(A_42,k1_zfmisc_1(A_42)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_140])).

tff(c_146,plain,(
    ! [B_9] :
      ( k4_yellow_0(k3_yellow_1(B_9)) = B_9
      | ~ m1_subset_1(B_9,k1_zfmisc_1(B_9))
      | v1_xboole_0(k1_zfmisc_1(B_9)) ) ),
    inference(resolution,[status(thm)],[c_16,c_142])).

tff(c_150,plain,(
    ! [B_43] :
      ( k4_yellow_0(k3_yellow_1(B_43)) = B_43
      | ~ m1_subset_1(B_43,k1_zfmisc_1(B_43)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_146])).

tff(c_158,plain,(
    ! [B_12] :
      ( k4_yellow_0(k3_yellow_1(B_12)) = B_12
      | ~ r1_tarski(B_12,B_12) ) ),
    inference(resolution,[status(thm)],[c_26,c_150])).

tff(c_162,plain,(
    ! [B_12] : k4_yellow_0(k3_yellow_1(B_12)) = B_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_158])).

tff(c_34,plain,(
    k4_yellow_0(k3_yellow_1('#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:39:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.22  
% 1.99/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.23  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > #skF_1 > #skF_2
% 1.99/1.23  
% 1.99/1.23  %Foreground sorts:
% 1.99/1.23  
% 1.99/1.23  
% 1.99/1.23  %Background operators:
% 1.99/1.23  
% 1.99/1.23  
% 1.99/1.23  %Foreground operators:
% 1.99/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.23  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 1.99/1.23  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.99/1.23  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 1.99/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.99/1.23  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 1.99/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.99/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.23  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.99/1.23  tff(k4_yellow_0, type, k4_yellow_0: $i > $i).
% 1.99/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.99/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.99/1.23  
% 1.99/1.24  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.99/1.24  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.99/1.24  tff(f_55, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.99/1.24  tff(f_52, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 1.99/1.24  tff(f_61, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 1.99/1.24  tff(f_70, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_1)).
% 1.99/1.24  tff(f_39, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 1.99/1.24  tff(f_68, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k3_tarski(A), A) => (k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow_1)).
% 1.99/1.24  tff(f_73, negated_conjecture, ~(![A]: (k4_yellow_0(k3_yellow_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_yellow_1)).
% 1.99/1.24  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.99/1.24  tff(c_26, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.99/1.24  tff(c_22, plain, (![A_10]: (~v1_xboole_0(k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.99/1.24  tff(c_16, plain, (![B_9, A_8]: (r2_hidden(B_9, A_8) | ~m1_subset_1(B_9, A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.99/1.24  tff(c_28, plain, (![A_13]: (k9_setfam_1(A_13)=k1_zfmisc_1(A_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.99/1.24  tff(c_32, plain, (![A_15]: (k2_yellow_1(k9_setfam_1(A_15))=k3_yellow_1(A_15))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.99/1.24  tff(c_35, plain, (![A_15]: (k2_yellow_1(k1_zfmisc_1(A_15))=k3_yellow_1(A_15))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32])).
% 1.99/1.24  tff(c_12, plain, (![A_7]: (k3_tarski(k1_zfmisc_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.99/1.24  tff(c_131, plain, (![A_41]: (k4_yellow_0(k2_yellow_1(A_41))=k3_tarski(A_41) | ~r2_hidden(k3_tarski(A_41), A_41) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.99/1.24  tff(c_138, plain, (![A_7]: (k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_7)))=k3_tarski(k1_zfmisc_1(A_7)) | ~r2_hidden(A_7, k1_zfmisc_1(A_7)) | v1_xboole_0(k1_zfmisc_1(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_131])).
% 1.99/1.24  tff(c_140, plain, (![A_7]: (k4_yellow_0(k3_yellow_1(A_7))=A_7 | ~r2_hidden(A_7, k1_zfmisc_1(A_7)) | v1_xboole_0(k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_12, c_138])).
% 1.99/1.24  tff(c_142, plain, (![A_42]: (k4_yellow_0(k3_yellow_1(A_42))=A_42 | ~r2_hidden(A_42, k1_zfmisc_1(A_42)))), inference(negUnitSimplification, [status(thm)], [c_22, c_140])).
% 1.99/1.24  tff(c_146, plain, (![B_9]: (k4_yellow_0(k3_yellow_1(B_9))=B_9 | ~m1_subset_1(B_9, k1_zfmisc_1(B_9)) | v1_xboole_0(k1_zfmisc_1(B_9)))), inference(resolution, [status(thm)], [c_16, c_142])).
% 1.99/1.24  tff(c_150, plain, (![B_43]: (k4_yellow_0(k3_yellow_1(B_43))=B_43 | ~m1_subset_1(B_43, k1_zfmisc_1(B_43)))), inference(negUnitSimplification, [status(thm)], [c_22, c_146])).
% 1.99/1.24  tff(c_158, plain, (![B_12]: (k4_yellow_0(k3_yellow_1(B_12))=B_12 | ~r1_tarski(B_12, B_12))), inference(resolution, [status(thm)], [c_26, c_150])).
% 1.99/1.24  tff(c_162, plain, (![B_12]: (k4_yellow_0(k3_yellow_1(B_12))=B_12)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_158])).
% 1.99/1.24  tff(c_34, plain, (k4_yellow_0(k3_yellow_1('#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.99/1.24  tff(c_167, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_162, c_34])).
% 1.99/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.24  
% 1.99/1.24  Inference rules
% 1.99/1.24  ----------------------
% 1.99/1.24  #Ref     : 0
% 1.99/1.24  #Sup     : 23
% 1.99/1.24  #Fact    : 0
% 1.99/1.24  #Define  : 0
% 1.99/1.24  #Split   : 0
% 1.99/1.24  #Chain   : 0
% 1.99/1.24  #Close   : 0
% 1.99/1.24  
% 1.99/1.24  Ordering : KBO
% 1.99/1.24  
% 1.99/1.24  Simplification rules
% 1.99/1.24  ----------------------
% 1.99/1.24  #Subsume      : 3
% 1.99/1.24  #Demod        : 9
% 1.99/1.24  #Tautology    : 16
% 1.99/1.24  #SimpNegUnit  : 3
% 1.99/1.24  #BackRed      : 1
% 1.99/1.24  
% 1.99/1.24  #Partial instantiations: 0
% 1.99/1.24  #Strategies tried      : 1
% 1.99/1.24  
% 1.99/1.24  Timing (in seconds)
% 1.99/1.24  ----------------------
% 1.99/1.24  Preprocessing        : 0.31
% 1.99/1.24  Parsing              : 0.17
% 1.99/1.24  CNF conversion       : 0.02
% 1.99/1.24  Main loop            : 0.13
% 1.99/1.24  Inferencing          : 0.05
% 1.99/1.24  Reduction            : 0.04
% 1.99/1.24  Demodulation         : 0.03
% 1.99/1.24  BG Simplification    : 0.01
% 1.99/1.24  Subsumption          : 0.02
% 1.99/1.24  Abstraction          : 0.01
% 1.99/1.24  MUC search           : 0.00
% 1.99/1.24  Cooper               : 0.00
% 1.99/1.24  Total                : 0.46
% 1.99/1.24  Index Insertion      : 0.00
% 1.99/1.24  Index Deletion       : 0.00
% 1.99/1.24  Index Matching       : 0.00
% 1.99/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
