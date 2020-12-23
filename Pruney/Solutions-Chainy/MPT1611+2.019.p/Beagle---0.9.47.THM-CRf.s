%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:34 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   43 (  45 expanded)
%              Number of leaves         :   28 (  29 expanded)
%              Depth                    :    5
%              Number of atoms          :   34 (  36 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k3_xboole_0 > #nlpp > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k3_lattice3 > k2_yellow_1 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > #skF_3 > #skF_2 > #skF_1

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

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_45,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_42,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_58,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k3_tarski(A),A)
       => k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

tff(f_61,negated_conjecture,(
    ~ ! [A] : k4_yellow_0(k3_yellow_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_yellow_1)).

tff(c_22,plain,(
    ! [A_13] : ~ v1_xboole_0(k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_62,plain,(
    ! [A_22,B_23] : r1_tarski(k3_xboole_0(A_22,B_23),A_22) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_65,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_62])).

tff(c_20,plain,(
    ! [A_12] : k3_tarski(k1_zfmisc_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_24,plain,(
    ! [A_14] : k9_setfam_1(A_14) = k1_zfmisc_1(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_30,plain,(
    ! [A_17] : k2_yellow_1(k9_setfam_1(A_17)) = k3_yellow_1(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_33,plain,(
    ! [A_17] : k2_yellow_1(k1_zfmisc_1(A_17)) = k3_yellow_1(A_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_30])).

tff(c_8,plain,(
    ! [C_9,A_5] :
      ( r2_hidden(C_9,k1_zfmisc_1(A_5))
      | ~ r1_tarski(C_9,A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_98,plain,(
    ! [A_33] :
      ( k4_yellow_0(k2_yellow_1(A_33)) = k3_tarski(A_33)
      | ~ r2_hidden(k3_tarski(A_33),A_33)
      | v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_102,plain,(
    ! [A_5] :
      ( k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_5))) = k3_tarski(k1_zfmisc_1(A_5))
      | v1_xboole_0(k1_zfmisc_1(A_5))
      | ~ r1_tarski(k3_tarski(k1_zfmisc_1(A_5)),A_5) ) ),
    inference(resolution,[status(thm)],[c_8,c_98])).

tff(c_108,plain,(
    ! [A_5] :
      ( k4_yellow_0(k3_yellow_1(A_5)) = A_5
      | v1_xboole_0(k1_zfmisc_1(A_5)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_20,c_33,c_20,c_102])).

tff(c_109,plain,(
    ! [A_5] : k4_yellow_0(k3_yellow_1(A_5)) = A_5 ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_108])).

tff(c_32,plain,(
    k4_yellow_0(k3_yellow_1('#skF_3')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_114,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:50:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.44  
% 2.02/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.44  %$ r2_hidden > r1_tarski > v1_xboole_0 > k3_xboole_0 > #nlpp > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k3_lattice3 > k2_yellow_1 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > #skF_3 > #skF_2 > #skF_1
% 2.02/1.44  
% 2.02/1.44  %Foreground sorts:
% 2.02/1.44  
% 2.02/1.44  
% 2.02/1.44  %Background operators:
% 2.02/1.44  
% 2.02/1.44  
% 2.02/1.44  %Foreground operators:
% 2.02/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.44  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 2.02/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.02/1.44  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.02/1.44  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.02/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.44  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 2.02/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.44  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 2.02/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.02/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.44  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.02/1.44  tff(k4_yellow_0, type, k4_yellow_0: $i > $i).
% 2.02/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.02/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.02/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.02/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.02/1.44  
% 2.17/1.46  tff(f_45, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.17/1.46  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.17/1.46  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.17/1.46  tff(f_42, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.17/1.46  tff(f_47, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 2.17/1.46  tff(f_58, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_1)).
% 2.17/1.46  tff(f_36, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.17/1.46  tff(f_56, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k3_tarski(A), A) => (k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow_1)).
% 2.17/1.46  tff(f_61, negated_conjecture, ~(![A]: (k4_yellow_0(k3_yellow_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_yellow_1)).
% 2.17/1.46  tff(c_22, plain, (![A_13]: (~v1_xboole_0(k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.17/1.46  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.17/1.46  tff(c_62, plain, (![A_22, B_23]: (r1_tarski(k3_xboole_0(A_22, B_23), A_22))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.17/1.46  tff(c_65, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_62])).
% 2.17/1.46  tff(c_20, plain, (![A_12]: (k3_tarski(k1_zfmisc_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.17/1.46  tff(c_24, plain, (![A_14]: (k9_setfam_1(A_14)=k1_zfmisc_1(A_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.17/1.46  tff(c_30, plain, (![A_17]: (k2_yellow_1(k9_setfam_1(A_17))=k3_yellow_1(A_17))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.17/1.46  tff(c_33, plain, (![A_17]: (k2_yellow_1(k1_zfmisc_1(A_17))=k3_yellow_1(A_17))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_30])).
% 2.17/1.46  tff(c_8, plain, (![C_9, A_5]: (r2_hidden(C_9, k1_zfmisc_1(A_5)) | ~r1_tarski(C_9, A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.17/1.46  tff(c_98, plain, (![A_33]: (k4_yellow_0(k2_yellow_1(A_33))=k3_tarski(A_33) | ~r2_hidden(k3_tarski(A_33), A_33) | v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.17/1.46  tff(c_102, plain, (![A_5]: (k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_5)))=k3_tarski(k1_zfmisc_1(A_5)) | v1_xboole_0(k1_zfmisc_1(A_5)) | ~r1_tarski(k3_tarski(k1_zfmisc_1(A_5)), A_5))), inference(resolution, [status(thm)], [c_8, c_98])).
% 2.17/1.46  tff(c_108, plain, (![A_5]: (k4_yellow_0(k3_yellow_1(A_5))=A_5 | v1_xboole_0(k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_20, c_33, c_20, c_102])).
% 2.17/1.46  tff(c_109, plain, (![A_5]: (k4_yellow_0(k3_yellow_1(A_5))=A_5)), inference(negUnitSimplification, [status(thm)], [c_22, c_108])).
% 2.17/1.46  tff(c_32, plain, (k4_yellow_0(k3_yellow_1('#skF_3'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.17/1.46  tff(c_114, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_109, c_32])).
% 2.17/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.46  
% 2.17/1.46  Inference rules
% 2.17/1.46  ----------------------
% 2.17/1.46  #Ref     : 0
% 2.17/1.46  #Sup     : 15
% 2.17/1.46  #Fact    : 0
% 2.17/1.46  #Define  : 0
% 2.17/1.46  #Split   : 0
% 2.17/1.46  #Chain   : 0
% 2.17/1.46  #Close   : 0
% 2.17/1.46  
% 2.17/1.46  Ordering : KBO
% 2.17/1.46  
% 2.17/1.46  Simplification rules
% 2.17/1.46  ----------------------
% 2.17/1.46  #Subsume      : 0
% 2.17/1.46  #Demod        : 8
% 2.17/1.46  #Tautology    : 12
% 2.17/1.46  #SimpNegUnit  : 2
% 2.17/1.46  #BackRed      : 1
% 2.17/1.46  
% 2.17/1.46  #Partial instantiations: 0
% 2.17/1.46  #Strategies tried      : 1
% 2.17/1.46  
% 2.17/1.46  Timing (in seconds)
% 2.17/1.46  ----------------------
% 2.17/1.46  Preprocessing        : 0.48
% 2.17/1.46  Parsing              : 0.24
% 2.17/1.46  CNF conversion       : 0.03
% 2.17/1.46  Main loop            : 0.16
% 2.17/1.46  Inferencing          : 0.06
% 2.17/1.46  Reduction            : 0.05
% 2.17/1.46  Demodulation         : 0.04
% 2.17/1.46  BG Simplification    : 0.02
% 2.17/1.46  Subsumption          : 0.02
% 2.17/1.46  Abstraction          : 0.01
% 2.17/1.46  MUC search           : 0.00
% 2.17/1.46  Cooper               : 0.00
% 2.17/1.46  Total                : 0.67
% 2.17/1.46  Index Insertion      : 0.00
% 2.17/1.46  Index Deletion       : 0.00
% 2.17/1.46  Index Matching       : 0.00
% 2.17/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
