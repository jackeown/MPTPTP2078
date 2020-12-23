%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:32 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   37 (  42 expanded)
%              Number of leaves         :   23 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   30 (  36 expanded)
%              Number of equality atoms :    9 (  14 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > r1_setfam_1 > v1_relat_1 > k4_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k3_tarski > k1_setfam_1 > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_setfam_1(A,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r1_setfam_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_setfam_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_8,B_9] : k3_tarski(k2_tarski(A_8,B_9)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_10] : r1_setfam_1(A_10,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_58,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(k3_tarski(A_27),k3_tarski(B_28))
      | ~ r1_setfam_1(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_75,plain,(
    ! [A_34,A_35,B_36] :
      ( r1_tarski(k3_tarski(A_34),k2_xboole_0(A_35,B_36))
      | ~ r1_setfam_1(A_34,k2_tarski(A_35,B_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_58])).

tff(c_89,plain,(
    ! [A_40,A_41,B_42] :
      ( r1_tarski(k3_tarski(A_40),A_41)
      | ~ r1_setfam_1(A_40,k2_tarski(A_41,k3_xboole_0(A_41,B_42))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_75])).

tff(c_93,plain,(
    ! [A_41,B_42] : r1_tarski(k3_tarski(k2_tarski(A_41,k3_xboole_0(A_41,B_42))),A_41) ),
    inference(resolution,[status(thm)],[c_10,c_89])).

tff(c_96,plain,(
    ! [A_43] : r1_tarski(A_43,A_43) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8,c_93])).

tff(c_16,plain,(
    ! [A_16,B_17] :
      ( k5_relat_1(k6_relat_1(A_16),B_17) = B_17
      | ~ r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_102,plain,(
    ! [B_44] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(B_44)),B_44) = B_44
      | ~ v1_relat_1(B_44) ) ),
    inference(resolution,[status(thm)],[c_96,c_16])).

tff(c_18,plain,(
    k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')),'#skF_1') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_108,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_18])).

tff(c_116,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:50:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.22  
% 1.77/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.22  %$ r1_tarski > r1_setfam_1 > v1_relat_1 > k4_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k3_tarski > k1_setfam_1 > k1_relat_1 > #skF_1
% 1.77/1.22  
% 1.77/1.22  %Foreground sorts:
% 1.77/1.22  
% 1.77/1.22  
% 1.77/1.22  %Background operators:
% 1.77/1.22  
% 1.77/1.22  
% 1.77/1.22  %Foreground operators:
% 1.77/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.22  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.77/1.22  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.77/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.77/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.77/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.77/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.77/1.22  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.77/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.22  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.77/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.77/1.22  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.77/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.77/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.77/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.77/1.22  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.77/1.22  
% 1.92/1.23  tff(f_52, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 1.92/1.23  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 1.92/1.23  tff(f_33, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.92/1.23  tff(f_35, axiom, (![A, B]: r1_setfam_1(A, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r1_setfam_1)).
% 1.92/1.23  tff(f_41, axiom, (![A, B]: (r1_setfam_1(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_setfam_1)).
% 1.92/1.23  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 1.92/1.23  tff(c_20, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.92/1.23  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k3_xboole_0(A_1, B_2))=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.92/1.23  tff(c_8, plain, (![A_8, B_9]: (k3_tarski(k2_tarski(A_8, B_9))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.92/1.23  tff(c_10, plain, (![A_10]: (r1_setfam_1(A_10, A_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.92/1.23  tff(c_58, plain, (![A_27, B_28]: (r1_tarski(k3_tarski(A_27), k3_tarski(B_28)) | ~r1_setfam_1(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.92/1.23  tff(c_75, plain, (![A_34, A_35, B_36]: (r1_tarski(k3_tarski(A_34), k2_xboole_0(A_35, B_36)) | ~r1_setfam_1(A_34, k2_tarski(A_35, B_36)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_58])).
% 1.92/1.23  tff(c_89, plain, (![A_40, A_41, B_42]: (r1_tarski(k3_tarski(A_40), A_41) | ~r1_setfam_1(A_40, k2_tarski(A_41, k3_xboole_0(A_41, B_42))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_75])).
% 1.92/1.23  tff(c_93, plain, (![A_41, B_42]: (r1_tarski(k3_tarski(k2_tarski(A_41, k3_xboole_0(A_41, B_42))), A_41))), inference(resolution, [status(thm)], [c_10, c_89])).
% 1.92/1.23  tff(c_96, plain, (![A_43]: (r1_tarski(A_43, A_43))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8, c_93])).
% 1.92/1.23  tff(c_16, plain, (![A_16, B_17]: (k5_relat_1(k6_relat_1(A_16), B_17)=B_17 | ~r1_tarski(k1_relat_1(B_17), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.92/1.23  tff(c_102, plain, (![B_44]: (k5_relat_1(k6_relat_1(k1_relat_1(B_44)), B_44)=B_44 | ~v1_relat_1(B_44))), inference(resolution, [status(thm)], [c_96, c_16])).
% 1.92/1.23  tff(c_18, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')), '#skF_1')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.92/1.23  tff(c_108, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_102, c_18])).
% 1.92/1.23  tff(c_116, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_108])).
% 1.92/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.23  
% 1.92/1.23  Inference rules
% 1.92/1.23  ----------------------
% 1.92/1.23  #Ref     : 0
% 1.92/1.23  #Sup     : 21
% 1.92/1.23  #Fact    : 0
% 1.92/1.23  #Define  : 0
% 1.92/1.23  #Split   : 0
% 1.92/1.23  #Chain   : 0
% 1.92/1.23  #Close   : 0
% 1.92/1.23  
% 1.92/1.23  Ordering : KBO
% 1.92/1.23  
% 1.92/1.23  Simplification rules
% 1.92/1.23  ----------------------
% 1.92/1.23  #Subsume      : 0
% 1.92/1.23  #Demod        : 3
% 1.92/1.23  #Tautology    : 11
% 1.92/1.23  #SimpNegUnit  : 0
% 1.92/1.23  #BackRed      : 0
% 1.92/1.23  
% 1.92/1.23  #Partial instantiations: 0
% 1.92/1.23  #Strategies tried      : 1
% 1.92/1.23  
% 1.92/1.23  Timing (in seconds)
% 1.92/1.23  ----------------------
% 1.92/1.23  Preprocessing        : 0.31
% 1.92/1.23  Parsing              : 0.17
% 1.92/1.23  CNF conversion       : 0.02
% 1.92/1.23  Main loop            : 0.11
% 1.92/1.23  Inferencing          : 0.05
% 1.92/1.23  Reduction            : 0.03
% 1.92/1.23  Demodulation         : 0.02
% 1.92/1.23  BG Simplification    : 0.01
% 1.92/1.23  Subsumption          : 0.01
% 1.92/1.23  Abstraction          : 0.01
% 1.92/1.23  MUC search           : 0.00
% 1.92/1.23  Cooper               : 0.00
% 1.92/1.23  Total                : 0.44
% 1.92/1.23  Index Insertion      : 0.00
% 1.92/1.23  Index Deletion       : 0.00
% 1.92/1.23  Index Matching       : 0.00
% 1.92/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
