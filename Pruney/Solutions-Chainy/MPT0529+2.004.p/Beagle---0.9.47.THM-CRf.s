%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:12 EST 2020

% Result     : Theorem 15.67s
% Output     : CNFRefutation 15.67s
% Verified   : 
% Statistics : Number of formulae       :   44 (  47 expanded)
%              Number of leaves         :   27 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   30 (  37 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k1_enumset1 > k8_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).

tff(f_80,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_84,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(k3_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_relat_1)).

tff(c_68,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_56,plain,(
    ! [B_36,A_35] : k2_tarski(B_36,A_35) = k2_tarski(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_492,plain,(
    ! [A_70,B_71] : k1_setfam_1(k2_tarski(A_70,B_71)) = k3_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_907,plain,(
    ! [A_93,B_94] : k1_setfam_1(k2_tarski(A_93,B_94)) = k3_xboole_0(B_94,A_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_492])).

tff(c_60,plain,(
    ! [A_39,B_40] : k1_setfam_1(k2_tarski(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_930,plain,(
    ! [B_95,A_96] : k3_xboole_0(B_95,A_96) = k3_xboole_0(A_96,B_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_907,c_60])).

tff(c_66,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_212,plain,(
    ! [A_61,B_62] :
      ( k2_xboole_0(A_61,B_62) = B_62
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_236,plain,(
    k2_xboole_0('#skF_5','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_66,c_212])).

tff(c_42,plain,(
    ! [A_22,B_23] : k3_xboole_0(A_22,k2_xboole_0(A_22,B_23)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_322,plain,(
    k3_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_42])).

tff(c_945,plain,(
    k3_xboole_0('#skF_6','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_930,c_322])).

tff(c_2712,plain,(
    ! [A_149,B_150,C_151] :
      ( k8_relat_1(k3_xboole_0(A_149,B_150),C_151) = k8_relat_1(A_149,k8_relat_1(B_150,C_151))
      | ~ v1_relat_1(C_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_55447,plain,(
    ! [C_821] :
      ( k8_relat_1('#skF_6',k8_relat_1('#skF_5',C_821)) = k8_relat_1('#skF_5',C_821)
      | ~ v1_relat_1(C_821) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_945,c_2712])).

tff(c_64,plain,(
    k8_relat_1('#skF_6',k8_relat_1('#skF_5','#skF_7')) != k8_relat_1('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_55459,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_55447,c_64])).

tff(c_55480,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_55459])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n002.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 15:57:06 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.67/7.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.67/7.41  
% 15.67/7.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.67/7.41  %$ r2_hidden > r1_tarski > v1_relat_1 > k1_enumset1 > k8_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 15.67/7.41  
% 15.67/7.41  %Foreground sorts:
% 15.67/7.41  
% 15.67/7.41  
% 15.67/7.41  %Background operators:
% 15.67/7.41  
% 15.67/7.41  
% 15.67/7.41  %Foreground operators:
% 15.67/7.41  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 15.67/7.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 15.67/7.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.67/7.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.67/7.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.67/7.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.67/7.41  tff('#skF_7', type, '#skF_7': $i).
% 15.67/7.41  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 15.67/7.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.67/7.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 15.67/7.41  tff('#skF_5', type, '#skF_5': $i).
% 15.67/7.41  tff('#skF_6', type, '#skF_6': $i).
% 15.67/7.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 15.67/7.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 15.67/7.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.67/7.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.67/7.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.67/7.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.67/7.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 15.67/7.41  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 15.67/7.41  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 15.67/7.41  
% 15.67/7.42  tff(f_95, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_relat_1)).
% 15.67/7.42  tff(f_80, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 15.67/7.42  tff(f_84, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 15.67/7.42  tff(f_62, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 15.67/7.42  tff(f_64, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 15.67/7.42  tff(f_88, axiom, (![A, B, C]: (v1_relat_1(C) => (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(k3_xboole_0(A, B), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_relat_1)).
% 15.67/7.42  tff(c_68, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_95])).
% 15.67/7.42  tff(c_56, plain, (![B_36, A_35]: (k2_tarski(B_36, A_35)=k2_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_80])).
% 15.67/7.42  tff(c_492, plain, (![A_70, B_71]: (k1_setfam_1(k2_tarski(A_70, B_71))=k3_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_84])).
% 15.67/7.42  tff(c_907, plain, (![A_93, B_94]: (k1_setfam_1(k2_tarski(A_93, B_94))=k3_xboole_0(B_94, A_93))), inference(superposition, [status(thm), theory('equality')], [c_56, c_492])).
% 15.67/7.42  tff(c_60, plain, (![A_39, B_40]: (k1_setfam_1(k2_tarski(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_84])).
% 15.67/7.42  tff(c_930, plain, (![B_95, A_96]: (k3_xboole_0(B_95, A_96)=k3_xboole_0(A_96, B_95))), inference(superposition, [status(thm), theory('equality')], [c_907, c_60])).
% 15.67/7.42  tff(c_66, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_95])).
% 15.67/7.42  tff(c_212, plain, (![A_61, B_62]: (k2_xboole_0(A_61, B_62)=B_62 | ~r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_62])).
% 15.67/7.42  tff(c_236, plain, (k2_xboole_0('#skF_5', '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_66, c_212])).
% 15.67/7.42  tff(c_42, plain, (![A_22, B_23]: (k3_xboole_0(A_22, k2_xboole_0(A_22, B_23))=A_22)), inference(cnfTransformation, [status(thm)], [f_64])).
% 15.67/7.42  tff(c_322, plain, (k3_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_236, c_42])).
% 15.67/7.42  tff(c_945, plain, (k3_xboole_0('#skF_6', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_930, c_322])).
% 15.67/7.42  tff(c_2712, plain, (![A_149, B_150, C_151]: (k8_relat_1(k3_xboole_0(A_149, B_150), C_151)=k8_relat_1(A_149, k8_relat_1(B_150, C_151)) | ~v1_relat_1(C_151))), inference(cnfTransformation, [status(thm)], [f_88])).
% 15.67/7.42  tff(c_55447, plain, (![C_821]: (k8_relat_1('#skF_6', k8_relat_1('#skF_5', C_821))=k8_relat_1('#skF_5', C_821) | ~v1_relat_1(C_821))), inference(superposition, [status(thm), theory('equality')], [c_945, c_2712])).
% 15.67/7.42  tff(c_64, plain, (k8_relat_1('#skF_6', k8_relat_1('#skF_5', '#skF_7'))!=k8_relat_1('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_95])).
% 15.67/7.42  tff(c_55459, plain, (~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_55447, c_64])).
% 15.67/7.42  tff(c_55480, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_55459])).
% 15.67/7.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.67/7.42  
% 15.67/7.42  Inference rules
% 15.67/7.42  ----------------------
% 15.67/7.42  #Ref     : 0
% 15.67/7.42  #Sup     : 13783
% 15.67/7.42  #Fact    : 0
% 15.67/7.42  #Define  : 0
% 15.67/7.42  #Split   : 3
% 15.67/7.42  #Chain   : 0
% 15.67/7.42  #Close   : 0
% 15.67/7.42  
% 15.67/7.42  Ordering : KBO
% 15.67/7.42  
% 15.67/7.42  Simplification rules
% 15.67/7.42  ----------------------
% 15.67/7.42  #Subsume      : 1675
% 15.67/7.42  #Demod        : 14537
% 15.67/7.42  #Tautology    : 8276
% 15.67/7.42  #SimpNegUnit  : 0
% 15.67/7.42  #BackRed      : 75
% 15.67/7.42  
% 15.67/7.42  #Partial instantiations: 0
% 15.67/7.42  #Strategies tried      : 1
% 15.67/7.42  
% 15.67/7.42  Timing (in seconds)
% 15.67/7.42  ----------------------
% 15.67/7.42  Preprocessing        : 0.33
% 15.67/7.42  Parsing              : 0.17
% 15.67/7.42  CNF conversion       : 0.03
% 15.67/7.42  Main loop            : 6.35
% 15.67/7.42  Inferencing          : 1.08
% 15.67/7.43  Reduction            : 3.51
% 15.67/7.43  Demodulation         : 3.12
% 15.67/7.43  BG Simplification    : 0.12
% 15.67/7.43  Subsumption          : 1.30
% 15.67/7.43  Abstraction          : 0.19
% 15.67/7.43  MUC search           : 0.00
% 15.67/7.43  Cooper               : 0.00
% 15.67/7.43  Total                : 6.71
% 15.67/7.43  Index Insertion      : 0.00
% 15.67/7.43  Index Deletion       : 0.00
% 15.67/7.43  Index Matching       : 0.00
% 15.67/7.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
