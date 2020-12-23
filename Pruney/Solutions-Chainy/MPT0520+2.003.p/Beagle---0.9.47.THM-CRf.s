%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:07 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   32 (  35 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   38 (  50 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k2_relat_1(B))
         => k2_relat_1(k8_relat_1(A,B)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & ! [D] :
            ( ( r1_tarski(D,B)
              & r1_tarski(D,C) )
           => r1_tarski(D,A) ) )
     => A = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

tff(c_24,plain,(
    k2_relat_1(k8_relat_1('#skF_2','#skF_3')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_26,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_289,plain,(
    ! [A_43,B_44,C_45] :
      ( r1_tarski('#skF_1'(A_43,B_44,C_45),C_45)
      | k3_xboole_0(B_44,C_45) = A_43
      | ~ r1_tarski(A_43,C_45)
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r1_tarski('#skF_1'(A_3,B_4,C_5),A_3)
      | k3_xboole_0(B_4,C_5) = A_3
      | ~ r1_tarski(A_3,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_293,plain,(
    ! [B_44,C_45] :
      ( k3_xboole_0(B_44,C_45) = C_45
      | ~ r1_tarski(C_45,C_45)
      | ~ r1_tarski(C_45,B_44) ) ),
    inference(resolution,[status(thm)],[c_289,c_8])).

tff(c_300,plain,(
    ! [B_46,C_47] :
      ( k3_xboole_0(B_46,C_47) = C_47
      | ~ r1_tarski(C_47,B_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_293])).

tff(c_311,plain,(
    k3_xboole_0(k2_relat_1('#skF_3'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_26,c_300])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( k3_xboole_0(k2_relat_1(B_17),A_16) = k2_relat_1(k8_relat_1(A_16,B_17))
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_356,plain,
    ( k2_relat_1(k8_relat_1('#skF_2','#skF_3')) = '#skF_2'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_22])).

tff(c_375,plain,(
    k2_relat_1(k8_relat_1('#skF_2','#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_356])).

tff(c_377,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_375])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:39:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.28  
% 1.98/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.28  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_1 > #skF_2 > #skF_3
% 1.98/1.28  
% 1.98/1.28  %Foreground sorts:
% 1.98/1.28  
% 1.98/1.28  
% 1.98/1.28  %Background operators:
% 1.98/1.28  
% 1.98/1.28  
% 1.98/1.28  %Foreground operators:
% 1.98/1.28  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.98/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.98/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.98/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.98/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.98/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.98/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.98/1.28  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.28  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.98/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.98/1.28  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.98/1.28  
% 1.98/1.29  tff(f_63, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k2_relat_1(B)) => (k2_relat_1(k8_relat_1(A, B)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_relat_1)).
% 1.98/1.29  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.98/1.29  tff(f_44, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & (![D]: ((r1_tarski(D, B) & r1_tarski(D, C)) => r1_tarski(D, A)))) => (A = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_xboole_1)).
% 1.98/1.29  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_relat_1)).
% 1.98/1.29  tff(c_24, plain, (k2_relat_1(k8_relat_1('#skF_2', '#skF_3'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.98/1.29  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.98/1.29  tff(c_26, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.98/1.29  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.98/1.29  tff(c_289, plain, (![A_43, B_44, C_45]: (r1_tarski('#skF_1'(A_43, B_44, C_45), C_45) | k3_xboole_0(B_44, C_45)=A_43 | ~r1_tarski(A_43, C_45) | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.98/1.29  tff(c_8, plain, (![A_3, B_4, C_5]: (~r1_tarski('#skF_1'(A_3, B_4, C_5), A_3) | k3_xboole_0(B_4, C_5)=A_3 | ~r1_tarski(A_3, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.98/1.29  tff(c_293, plain, (![B_44, C_45]: (k3_xboole_0(B_44, C_45)=C_45 | ~r1_tarski(C_45, C_45) | ~r1_tarski(C_45, B_44))), inference(resolution, [status(thm)], [c_289, c_8])).
% 1.98/1.29  tff(c_300, plain, (![B_46, C_47]: (k3_xboole_0(B_46, C_47)=C_47 | ~r1_tarski(C_47, B_46))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_293])).
% 1.98/1.29  tff(c_311, plain, (k3_xboole_0(k2_relat_1('#skF_3'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_26, c_300])).
% 1.98/1.29  tff(c_22, plain, (![B_17, A_16]: (k3_xboole_0(k2_relat_1(B_17), A_16)=k2_relat_1(k8_relat_1(A_16, B_17)) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.98/1.29  tff(c_356, plain, (k2_relat_1(k8_relat_1('#skF_2', '#skF_3'))='#skF_2' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_311, c_22])).
% 1.98/1.29  tff(c_375, plain, (k2_relat_1(k8_relat_1('#skF_2', '#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_356])).
% 1.98/1.29  tff(c_377, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_375])).
% 1.98/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.29  
% 1.98/1.29  Inference rules
% 1.98/1.29  ----------------------
% 1.98/1.29  #Ref     : 0
% 1.98/1.29  #Sup     : 88
% 1.98/1.29  #Fact    : 0
% 1.98/1.29  #Define  : 0
% 1.98/1.29  #Split   : 1
% 1.98/1.29  #Chain   : 0
% 1.98/1.29  #Close   : 0
% 1.98/1.29  
% 1.98/1.29  Ordering : KBO
% 1.98/1.29  
% 1.98/1.29  Simplification rules
% 1.98/1.29  ----------------------
% 1.98/1.29  #Subsume      : 9
% 1.98/1.29  #Demod        : 8
% 1.98/1.29  #Tautology    : 44
% 1.98/1.29  #SimpNegUnit  : 1
% 1.98/1.29  #BackRed      : 0
% 1.98/1.29  
% 1.98/1.29  #Partial instantiations: 0
% 1.98/1.29  #Strategies tried      : 1
% 1.98/1.29  
% 1.98/1.29  Timing (in seconds)
% 1.98/1.29  ----------------------
% 1.98/1.29  Preprocessing        : 0.30
% 1.98/1.29  Parsing              : 0.16
% 1.98/1.29  CNF conversion       : 0.02
% 1.98/1.29  Main loop            : 0.21
% 1.98/1.29  Inferencing          : 0.08
% 1.98/1.29  Reduction            : 0.06
% 1.98/1.29  Demodulation         : 0.05
% 1.98/1.29  BG Simplification    : 0.01
% 1.98/1.29  Subsumption          : 0.04
% 1.98/1.30  Abstraction          : 0.02
% 1.98/1.30  MUC search           : 0.00
% 1.98/1.30  Cooper               : 0.00
% 1.98/1.30  Total                : 0.53
% 1.98/1.30  Index Insertion      : 0.00
% 1.98/1.30  Index Deletion       : 0.00
% 1.98/1.30  Index Matching       : 0.00
% 1.98/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
