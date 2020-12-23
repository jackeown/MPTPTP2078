%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:06 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   39 (  46 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   46 (  56 expanded)
%              Number of equality atoms :   16 (  21 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( v1_relat_1(k7_relat_1(A_10,B_11))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_16,A_15)),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_161,plain,(
    ! [C_39,B_40,A_41] :
      ( k7_relat_1(k7_relat_1(C_39,B_40),A_41) = k7_relat_1(C_39,A_41)
      | ~ r1_tarski(A_41,B_40)
      | ~ v1_relat_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [A_19] :
      ( k7_relat_1(A_19,k1_relat_1(A_19)) = A_19
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_321,plain,(
    ! [C_46,B_47] :
      ( k7_relat_1(C_46,k1_relat_1(k7_relat_1(C_46,B_47))) = k7_relat_1(C_46,B_47)
      | ~ v1_relat_1(k7_relat_1(C_46,B_47))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_46,B_47)),B_47)
      | ~ v1_relat_1(C_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_18])).

tff(c_337,plain,(
    ! [B_48,A_49] :
      ( k7_relat_1(B_48,k1_relat_1(k7_relat_1(B_48,A_49))) = k7_relat_1(B_48,A_49)
      | ~ v1_relat_1(k7_relat_1(B_48,A_49))
      | ~ v1_relat_1(B_48) ) ),
    inference(resolution,[status(thm)],[c_14,c_321])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_101,plain,(
    ! [B_34,A_35] :
      ( k3_xboole_0(k1_relat_1(B_34),A_35) = k1_relat_1(k7_relat_1(B_34,A_35))
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_125,plain,(
    ! [A_37,B_38] :
      ( k3_xboole_0(A_37,k1_relat_1(B_38)) = k1_relat_1(k7_relat_1(B_38,A_37))
      | ~ v1_relat_1(B_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_101])).

tff(c_20,plain,(
    k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_23,plain,(
    k7_relat_1('#skF_2',k3_xboole_0('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_135,plain,
    ( k7_relat_1('#skF_2',k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k7_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_23])).

tff(c_159,plain,(
    k7_relat_1('#skF_2',k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_135])).

tff(c_356,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_159])).

tff(c_389,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_356])).

tff(c_395,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_389])).

tff(c_399,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_395])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:39:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.23  
% 2.20/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.23  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.20/1.23  
% 2.20/1.23  %Foreground sorts:
% 2.20/1.23  
% 2.20/1.23  
% 2.20/1.23  %Background operators:
% 2.20/1.23  
% 2.20/1.23  
% 2.20/1.23  %Foreground operators:
% 2.20/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.23  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.20/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.20/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.20/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.20/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.20/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.20/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.20/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.20/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.20/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.20/1.23  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.20/1.23  
% 2.20/1.24  tff(f_60, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 2.20/1.24  tff(f_37, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.20/1.24  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.20/1.24  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_relat_1)).
% 2.20/1.24  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 2.20/1.24  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.20/1.24  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.20/1.24  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.20/1.24  tff(c_10, plain, (![A_10, B_11]: (v1_relat_1(k7_relat_1(A_10, B_11)) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.20/1.24  tff(c_14, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(k7_relat_1(B_16, A_15)), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.20/1.24  tff(c_161, plain, (![C_39, B_40, A_41]: (k7_relat_1(k7_relat_1(C_39, B_40), A_41)=k7_relat_1(C_39, A_41) | ~r1_tarski(A_41, B_40) | ~v1_relat_1(C_39))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.20/1.24  tff(c_18, plain, (![A_19]: (k7_relat_1(A_19, k1_relat_1(A_19))=A_19 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.20/1.24  tff(c_321, plain, (![C_46, B_47]: (k7_relat_1(C_46, k1_relat_1(k7_relat_1(C_46, B_47)))=k7_relat_1(C_46, B_47) | ~v1_relat_1(k7_relat_1(C_46, B_47)) | ~r1_tarski(k1_relat_1(k7_relat_1(C_46, B_47)), B_47) | ~v1_relat_1(C_46))), inference(superposition, [status(thm), theory('equality')], [c_161, c_18])).
% 2.20/1.24  tff(c_337, plain, (![B_48, A_49]: (k7_relat_1(B_48, k1_relat_1(k7_relat_1(B_48, A_49)))=k7_relat_1(B_48, A_49) | ~v1_relat_1(k7_relat_1(B_48, A_49)) | ~v1_relat_1(B_48))), inference(resolution, [status(thm)], [c_14, c_321])).
% 2.20/1.24  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.20/1.24  tff(c_101, plain, (![B_34, A_35]: (k3_xboole_0(k1_relat_1(B_34), A_35)=k1_relat_1(k7_relat_1(B_34, A_35)) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.20/1.24  tff(c_125, plain, (![A_37, B_38]: (k3_xboole_0(A_37, k1_relat_1(B_38))=k1_relat_1(k7_relat_1(B_38, A_37)) | ~v1_relat_1(B_38))), inference(superposition, [status(thm), theory('equality')], [c_2, c_101])).
% 2.20/1.24  tff(c_20, plain, (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.20/1.24  tff(c_23, plain, (k7_relat_1('#skF_2', k3_xboole_0('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20])).
% 2.20/1.24  tff(c_135, plain, (k7_relat_1('#skF_2', k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k7_relat_1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_125, c_23])).
% 2.20/1.24  tff(c_159, plain, (k7_relat_1('#skF_2', k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_135])).
% 2.20/1.24  tff(c_356, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_337, c_159])).
% 2.20/1.24  tff(c_389, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_356])).
% 2.20/1.24  tff(c_395, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10, c_389])).
% 2.20/1.24  tff(c_399, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_395])).
% 2.20/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.24  
% 2.20/1.24  Inference rules
% 2.20/1.24  ----------------------
% 2.20/1.24  #Ref     : 0
% 2.20/1.24  #Sup     : 102
% 2.20/1.24  #Fact    : 0
% 2.20/1.24  #Define  : 0
% 2.20/1.24  #Split   : 0
% 2.20/1.24  #Chain   : 0
% 2.20/1.24  #Close   : 0
% 2.20/1.24  
% 2.20/1.24  Ordering : KBO
% 2.20/1.24  
% 2.20/1.24  Simplification rules
% 2.20/1.24  ----------------------
% 2.20/1.24  #Subsume      : 16
% 2.20/1.24  #Demod        : 4
% 2.20/1.24  #Tautology    : 37
% 2.20/1.24  #SimpNegUnit  : 0
% 2.20/1.24  #BackRed      : 0
% 2.20/1.24  
% 2.20/1.24  #Partial instantiations: 0
% 2.20/1.24  #Strategies tried      : 1
% 2.20/1.24  
% 2.20/1.24  Timing (in seconds)
% 2.20/1.24  ----------------------
% 2.20/1.25  Preprocessing        : 0.27
% 2.20/1.25  Parsing              : 0.14
% 2.20/1.25  CNF conversion       : 0.01
% 2.20/1.25  Main loop            : 0.22
% 2.20/1.25  Inferencing          : 0.09
% 2.20/1.25  Reduction            : 0.06
% 2.20/1.25  Demodulation         : 0.05
% 2.20/1.25  BG Simplification    : 0.02
% 2.20/1.25  Subsumption          : 0.04
% 2.20/1.25  Abstraction          : 0.02
% 2.20/1.25  MUC search           : 0.00
% 2.20/1.25  Cooper               : 0.00
% 2.20/1.25  Total                : 0.52
% 2.20/1.25  Index Insertion      : 0.00
% 2.20/1.25  Index Deletion       : 0.00
% 2.20/1.25  Index Matching       : 0.00
% 2.20/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
