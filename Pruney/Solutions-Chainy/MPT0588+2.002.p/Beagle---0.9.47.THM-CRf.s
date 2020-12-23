%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:03 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   37 (  47 expanded)
%              Number of leaves         :   21 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  47 expanded)
%              Number of equality atoms :   18 (  28 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_71,plain,(
    ! [A_29,B_30] : k1_setfam_1(k2_tarski(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_133,plain,(
    ! [B_34,A_35] : k1_setfam_1(k2_tarski(B_34,A_35)) = k3_xboole_0(A_35,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_71])).

tff(c_18,plain,(
    ! [A_17,B_18] : k1_setfam_1(k2_tarski(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_139,plain,(
    ! [B_34,A_35] : k3_xboole_0(B_34,A_35) = k3_xboole_0(A_35,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_18])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_245,plain,(
    ! [B_45,A_46] :
      ( k7_relat_1(B_45,A_46) = B_45
      | ~ r1_tarski(k1_relat_1(B_45),A_46)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_250,plain,(
    ! [B_45] :
      ( k7_relat_1(B_45,k1_relat_1(B_45)) = B_45
      | ~ v1_relat_1(B_45) ) ),
    inference(resolution,[status(thm)],[c_6,c_245])).

tff(c_269,plain,(
    ! [C_52,A_53,B_54] :
      ( k7_relat_1(k7_relat_1(C_52,A_53),B_54) = k7_relat_1(C_52,k3_xboole_0(A_53,B_54))
      | ~ v1_relat_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_295,plain,(
    ! [B_55,B_56] :
      ( k7_relat_1(B_55,k3_xboole_0(k1_relat_1(B_55),B_56)) = k7_relat_1(B_55,B_56)
      | ~ v1_relat_1(B_55)
      | ~ v1_relat_1(B_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_269])).

tff(c_323,plain,(
    ! [B_57,B_58] :
      ( k7_relat_1(B_57,k3_xboole_0(B_58,k1_relat_1(B_57))) = k7_relat_1(B_57,B_58)
      | ~ v1_relat_1(B_57)
      | ~ v1_relat_1(B_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_295])).

tff(c_24,plain,(
    k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_189,plain,(
    k7_relat_1('#skF_2',k3_xboole_0('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_24])).

tff(c_340,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_189])).

tff(c_365,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_340])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:28:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.16  
% 1.78/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.16  %$ r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.78/1.16  
% 1.78/1.16  %Foreground sorts:
% 1.78/1.16  
% 1.78/1.16  
% 1.78/1.16  %Background operators:
% 1.78/1.16  
% 1.78/1.16  
% 1.78/1.16  %Foreground operators:
% 1.78/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.16  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.78/1.16  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.78/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.78/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.78/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.78/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.78/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.78/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.78/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.78/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.78/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.78/1.16  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.78/1.16  
% 1.78/1.17  tff(f_58, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 1.78/1.17  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.78/1.17  tff(f_43, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.78/1.17  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.78/1.17  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 1.78/1.17  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 1.78/1.17  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.78/1.17  tff(c_8, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.78/1.17  tff(c_71, plain, (![A_29, B_30]: (k1_setfam_1(k2_tarski(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.78/1.17  tff(c_133, plain, (![B_34, A_35]: (k1_setfam_1(k2_tarski(B_34, A_35))=k3_xboole_0(A_35, B_34))), inference(superposition, [status(thm), theory('equality')], [c_8, c_71])).
% 1.78/1.17  tff(c_18, plain, (![A_17, B_18]: (k1_setfam_1(k2_tarski(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.78/1.17  tff(c_139, plain, (![B_34, A_35]: (k3_xboole_0(B_34, A_35)=k3_xboole_0(A_35, B_34))), inference(superposition, [status(thm), theory('equality')], [c_133, c_18])).
% 1.78/1.17  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.78/1.17  tff(c_245, plain, (![B_45, A_46]: (k7_relat_1(B_45, A_46)=B_45 | ~r1_tarski(k1_relat_1(B_45), A_46) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.78/1.17  tff(c_250, plain, (![B_45]: (k7_relat_1(B_45, k1_relat_1(B_45))=B_45 | ~v1_relat_1(B_45))), inference(resolution, [status(thm)], [c_6, c_245])).
% 1.78/1.17  tff(c_269, plain, (![C_52, A_53, B_54]: (k7_relat_1(k7_relat_1(C_52, A_53), B_54)=k7_relat_1(C_52, k3_xboole_0(A_53, B_54)) | ~v1_relat_1(C_52))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.78/1.17  tff(c_295, plain, (![B_55, B_56]: (k7_relat_1(B_55, k3_xboole_0(k1_relat_1(B_55), B_56))=k7_relat_1(B_55, B_56) | ~v1_relat_1(B_55) | ~v1_relat_1(B_55))), inference(superposition, [status(thm), theory('equality')], [c_250, c_269])).
% 1.78/1.17  tff(c_323, plain, (![B_57, B_58]: (k7_relat_1(B_57, k3_xboole_0(B_58, k1_relat_1(B_57)))=k7_relat_1(B_57, B_58) | ~v1_relat_1(B_57) | ~v1_relat_1(B_57))), inference(superposition, [status(thm), theory('equality')], [c_139, c_295])).
% 1.78/1.17  tff(c_24, plain, (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.78/1.17  tff(c_189, plain, (k7_relat_1('#skF_2', k3_xboole_0('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_24])).
% 1.78/1.17  tff(c_340, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_323, c_189])).
% 1.78/1.17  tff(c_365, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_340])).
% 1.78/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.17  
% 1.78/1.17  Inference rules
% 1.78/1.17  ----------------------
% 1.78/1.17  #Ref     : 0
% 1.78/1.17  #Sup     : 80
% 1.78/1.17  #Fact    : 0
% 1.78/1.17  #Define  : 0
% 1.78/1.17  #Split   : 0
% 1.78/1.17  #Chain   : 0
% 1.78/1.17  #Close   : 0
% 1.78/1.17  
% 1.78/1.17  Ordering : KBO
% 1.78/1.17  
% 1.78/1.17  Simplification rules
% 1.78/1.17  ----------------------
% 1.78/1.17  #Subsume      : 3
% 1.78/1.17  #Demod        : 14
% 1.78/1.17  #Tautology    : 56
% 1.78/1.17  #SimpNegUnit  : 0
% 1.78/1.17  #BackRed      : 0
% 1.78/1.17  
% 1.78/1.17  #Partial instantiations: 0
% 1.78/1.17  #Strategies tried      : 1
% 1.78/1.17  
% 1.78/1.17  Timing (in seconds)
% 1.78/1.17  ----------------------
% 1.78/1.17  Preprocessing        : 0.28
% 1.78/1.17  Parsing              : 0.15
% 1.78/1.17  CNF conversion       : 0.02
% 1.78/1.17  Main loop            : 0.18
% 1.78/1.17  Inferencing          : 0.07
% 1.78/1.17  Reduction            : 0.06
% 1.78/1.17  Demodulation         : 0.05
% 1.78/1.17  BG Simplification    : 0.01
% 1.78/1.17  Subsumption          : 0.03
% 1.78/1.17  Abstraction          : 0.01
% 1.78/1.17  MUC search           : 0.00
% 1.78/1.17  Cooper               : 0.00
% 1.78/1.17  Total                : 0.48
% 1.78/1.17  Index Insertion      : 0.00
% 1.78/1.18  Index Deletion       : 0.00
% 1.78/1.18  Index Matching       : 0.00
% 1.78/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
