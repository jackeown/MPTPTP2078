%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:34 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   43 (  45 expanded)
%              Number of leaves         :   27 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   34 (  36 expanded)
%              Number of equality atoms :   16 (  18 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k6_subset_1 > k4_xboole_0 > #nlpp > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k3_lattice3 > k2_yellow_1 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_lattice3,type,(
    k3_lattice3: $i > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_lattice3,type,(
    k1_lattice3: $i > $i )).

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

tff(f_42,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_33,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_46,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_57,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_39,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k3_tarski(A),A)
       => k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A] : k4_yellow_0(k3_yellow_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_yellow_1)).

tff(c_14,plain,(
    ! [A_8] : ~ v1_xboole_0(k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [A_4] : k3_tarski(k1_tarski(A_4)) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_3] : r1_tarski(A_3,k1_zfmisc_1(k3_tarski(A_3))) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    ! [A_28,B_29] :
      ( r2_hidden(A_28,B_29)
      | ~ r1_tarski(k1_tarski(A_28),B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_103,plain,(
    ! [A_28] : r2_hidden(A_28,k1_zfmisc_1(k3_tarski(k1_tarski(A_28)))) ),
    inference(resolution,[status(thm)],[c_4,c_93])).

tff(c_107,plain,(
    ! [A_28] : r2_hidden(A_28,k1_zfmisc_1(A_28)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_103])).

tff(c_18,plain,(
    ! [A_11] : k9_setfam_1(A_11) = k1_zfmisc_1(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_24,plain,(
    ! [A_14] : k2_yellow_1(k9_setfam_1(A_14)) = k3_yellow_1(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_27,plain,(
    ! [A_14] : k2_yellow_1(k1_zfmisc_1(A_14)) = k3_yellow_1(A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_24])).

tff(c_12,plain,(
    ! [A_7] : k3_tarski(k1_zfmisc_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_115,plain,(
    ! [A_33] :
      ( k4_yellow_0(k2_yellow_1(A_33)) = k3_tarski(A_33)
      | ~ r2_hidden(k3_tarski(A_33),A_33)
      | v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_121,plain,(
    ! [A_7] :
      ( k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_7))) = k3_tarski(k1_zfmisc_1(A_7))
      | ~ r2_hidden(A_7,k1_zfmisc_1(A_7))
      | v1_xboole_0(k1_zfmisc_1(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_115])).

tff(c_124,plain,(
    ! [A_7] :
      ( k4_yellow_0(k3_yellow_1(A_7)) = A_7
      | v1_xboole_0(k1_zfmisc_1(A_7)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_27,c_12,c_121])).

tff(c_125,plain,(
    ! [A_7] : k4_yellow_0(k3_yellow_1(A_7)) = A_7 ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_124])).

tff(c_26,plain,(
    k4_yellow_0(k3_yellow_1('#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:39:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.18  
% 1.72/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.18  %$ r2_hidden > r1_tarski > v1_xboole_0 > k6_subset_1 > k4_xboole_0 > #nlpp > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k3_lattice3 > k2_yellow_1 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > #skF_1
% 1.72/1.18  
% 1.72/1.18  %Foreground sorts:
% 1.72/1.18  
% 1.72/1.18  
% 1.72/1.18  %Background operators:
% 1.72/1.18  
% 1.72/1.18  
% 1.72/1.18  %Foreground operators:
% 1.72/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.18  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 1.72/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.72/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.72/1.18  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 1.72/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.72/1.18  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 1.72/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.72/1.18  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 1.72/1.18  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.72/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.72/1.18  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 1.72/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.72/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.18  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.72/1.18  tff(k4_yellow_0, type, k4_yellow_0: $i > $i).
% 1.72/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.72/1.18  
% 1.72/1.19  tff(f_42, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.72/1.19  tff(f_33, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 1.72/1.19  tff(f_31, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 1.72/1.19  tff(f_37, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 1.72/1.19  tff(f_46, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 1.72/1.19  tff(f_57, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_1)).
% 1.72/1.19  tff(f_39, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 1.72/1.19  tff(f_55, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k3_tarski(A), A) => (k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow_1)).
% 1.72/1.19  tff(f_60, negated_conjecture, ~(![A]: (k4_yellow_0(k3_yellow_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_yellow_1)).
% 1.72/1.19  tff(c_14, plain, (![A_8]: (~v1_xboole_0(k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.72/1.19  tff(c_6, plain, (![A_4]: (k3_tarski(k1_tarski(A_4))=A_4)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.72/1.19  tff(c_4, plain, (![A_3]: (r1_tarski(A_3, k1_zfmisc_1(k3_tarski(A_3))))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.72/1.19  tff(c_93, plain, (![A_28, B_29]: (r2_hidden(A_28, B_29) | ~r1_tarski(k1_tarski(A_28), B_29))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.72/1.19  tff(c_103, plain, (![A_28]: (r2_hidden(A_28, k1_zfmisc_1(k3_tarski(k1_tarski(A_28)))))), inference(resolution, [status(thm)], [c_4, c_93])).
% 1.72/1.19  tff(c_107, plain, (![A_28]: (r2_hidden(A_28, k1_zfmisc_1(A_28)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_103])).
% 1.72/1.19  tff(c_18, plain, (![A_11]: (k9_setfam_1(A_11)=k1_zfmisc_1(A_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.72/1.19  tff(c_24, plain, (![A_14]: (k2_yellow_1(k9_setfam_1(A_14))=k3_yellow_1(A_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.72/1.19  tff(c_27, plain, (![A_14]: (k2_yellow_1(k1_zfmisc_1(A_14))=k3_yellow_1(A_14))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_24])).
% 1.72/1.19  tff(c_12, plain, (![A_7]: (k3_tarski(k1_zfmisc_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.72/1.19  tff(c_115, plain, (![A_33]: (k4_yellow_0(k2_yellow_1(A_33))=k3_tarski(A_33) | ~r2_hidden(k3_tarski(A_33), A_33) | v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.72/1.19  tff(c_121, plain, (![A_7]: (k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_7)))=k3_tarski(k1_zfmisc_1(A_7)) | ~r2_hidden(A_7, k1_zfmisc_1(A_7)) | v1_xboole_0(k1_zfmisc_1(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_115])).
% 1.72/1.19  tff(c_124, plain, (![A_7]: (k4_yellow_0(k3_yellow_1(A_7))=A_7 | v1_xboole_0(k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_27, c_12, c_121])).
% 1.72/1.19  tff(c_125, plain, (![A_7]: (k4_yellow_0(k3_yellow_1(A_7))=A_7)), inference(negUnitSimplification, [status(thm)], [c_14, c_124])).
% 1.72/1.19  tff(c_26, plain, (k4_yellow_0(k3_yellow_1('#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.72/1.19  tff(c_128, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_26])).
% 1.72/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.19  
% 1.72/1.19  Inference rules
% 1.72/1.19  ----------------------
% 1.72/1.19  #Ref     : 1
% 1.72/1.19  #Sup     : 19
% 1.72/1.19  #Fact    : 0
% 1.72/1.19  #Define  : 0
% 1.72/1.19  #Split   : 0
% 1.72/1.19  #Chain   : 0
% 1.72/1.19  #Close   : 0
% 1.72/1.19  
% 1.72/1.19  Ordering : KBO
% 1.72/1.19  
% 1.72/1.19  Simplification rules
% 1.72/1.19  ----------------------
% 1.72/1.19  #Subsume      : 0
% 1.72/1.19  #Demod        : 8
% 1.72/1.19  #Tautology    : 15
% 1.72/1.19  #SimpNegUnit  : 1
% 1.72/1.19  #BackRed      : 1
% 1.72/1.19  
% 1.72/1.19  #Partial instantiations: 0
% 1.72/1.19  #Strategies tried      : 1
% 1.72/1.19  
% 1.72/1.19  Timing (in seconds)
% 1.72/1.19  ----------------------
% 1.72/1.19  Preprocessing        : 0.28
% 1.72/1.19  Parsing              : 0.14
% 1.72/1.19  CNF conversion       : 0.01
% 1.72/1.19  Main loop            : 0.10
% 1.72/1.19  Inferencing          : 0.04
% 1.72/1.19  Reduction            : 0.03
% 1.72/1.19  Demodulation         : 0.02
% 1.72/1.19  BG Simplification    : 0.01
% 1.72/1.19  Subsumption          : 0.01
% 1.72/1.19  Abstraction          : 0.01
% 1.72/1.19  MUC search           : 0.00
% 1.72/1.20  Cooper               : 0.00
% 1.72/1.20  Total                : 0.40
% 1.72/1.20  Index Insertion      : 0.00
% 1.72/1.20  Index Deletion       : 0.00
% 1.72/1.20  Index Matching       : 0.00
% 1.72/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
