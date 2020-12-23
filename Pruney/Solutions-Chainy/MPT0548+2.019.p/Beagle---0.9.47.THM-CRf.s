%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:37 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   48 (  50 expanded)
%              Number of leaves         :   35 (  36 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  38 expanded)
%              Number of equality atoms :   15 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_6 > #skF_2 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_44,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_77,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_70,axiom,(
    ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_48,plain,(
    ! [A_33] :
      ( r2_hidden('#skF_3'(A_33),A_33)
      | v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_28,plain,(
    ! [A_13] : k4_xboole_0(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_269,plain,(
    ! [D_75,B_76,A_77] :
      ( ~ r2_hidden(D_75,B_76)
      | ~ r2_hidden(D_75,k4_xboole_0(A_77,B_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_281,plain,(
    ! [D_78,A_79] :
      ( ~ r2_hidden(D_78,A_79)
      | ~ r2_hidden(D_78,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_269])).

tff(c_285,plain,(
    ! [A_80] :
      ( ~ r2_hidden('#skF_3'(A_80),k1_xboole_0)
      | v1_relat_1(A_80) ) ),
    inference(resolution,[status(thm)],[c_48,c_281])).

tff(c_290,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_48,c_285])).

tff(c_54,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_50,plain,(
    ! [A_51] : k7_relat_1(k1_xboole_0,A_51) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_312,plain,(
    ! [B_87,A_88] :
      ( k2_relat_1(k7_relat_1(B_87,A_88)) = k9_relat_1(B_87,A_88)
      | ~ v1_relat_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_321,plain,(
    ! [A_51] :
      ( k9_relat_1(k1_xboole_0,A_51) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_312])).

tff(c_325,plain,(
    ! [A_51] : k9_relat_1(k1_xboole_0,A_51) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_54,c_321])).

tff(c_58,plain,(
    k9_relat_1(k1_xboole_0,'#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_337,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n008.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:55:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.35  
% 2.26/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.36  %$ r2_hidden > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_6 > #skF_2 > #skF_3 > #skF_5 > #skF_4
% 2.26/1.36  
% 2.26/1.36  %Foreground sorts:
% 2.26/1.36  
% 2.26/1.36  
% 2.26/1.36  %Background operators:
% 2.26/1.36  
% 2.26/1.36  
% 2.26/1.36  %Foreground operators:
% 2.26/1.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.26/1.36  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 2.26/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.26/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.26/1.36  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.26/1.36  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.26/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.26/1.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.26/1.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.26/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.26/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.26/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.26/1.36  tff('#skF_6', type, '#skF_6': $i).
% 2.26/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.26/1.36  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.26/1.36  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.26/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.26/1.36  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.26/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.26/1.36  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.26/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.26/1.36  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.26/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.26/1.36  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.26/1.36  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.26/1.36  
% 2.26/1.37  tff(f_68, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.26/1.37  tff(f_44, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.26/1.37  tff(f_38, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.26/1.37  tff(f_77, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.26/1.37  tff(f_70, axiom, (![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 2.26/1.37  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.26/1.37  tff(f_80, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 2.26/1.37  tff(c_48, plain, (![A_33]: (r2_hidden('#skF_3'(A_33), A_33) | v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.26/1.37  tff(c_28, plain, (![A_13]: (k4_xboole_0(k1_xboole_0, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.26/1.37  tff(c_269, plain, (![D_75, B_76, A_77]: (~r2_hidden(D_75, B_76) | ~r2_hidden(D_75, k4_xboole_0(A_77, B_76)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.26/1.37  tff(c_281, plain, (![D_78, A_79]: (~r2_hidden(D_78, A_79) | ~r2_hidden(D_78, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_269])).
% 2.26/1.37  tff(c_285, plain, (![A_80]: (~r2_hidden('#skF_3'(A_80), k1_xboole_0) | v1_relat_1(A_80))), inference(resolution, [status(thm)], [c_48, c_281])).
% 2.26/1.37  tff(c_290, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_285])).
% 2.26/1.37  tff(c_54, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.26/1.37  tff(c_50, plain, (![A_51]: (k7_relat_1(k1_xboole_0, A_51)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.26/1.37  tff(c_312, plain, (![B_87, A_88]: (k2_relat_1(k7_relat_1(B_87, A_88))=k9_relat_1(B_87, A_88) | ~v1_relat_1(B_87))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.26/1.37  tff(c_321, plain, (![A_51]: (k9_relat_1(k1_xboole_0, A_51)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_50, c_312])).
% 2.26/1.37  tff(c_325, plain, (![A_51]: (k9_relat_1(k1_xboole_0, A_51)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_290, c_54, c_321])).
% 2.26/1.37  tff(c_58, plain, (k9_relat_1(k1_xboole_0, '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.26/1.37  tff(c_337, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_325, c_58])).
% 2.26/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.37  
% 2.26/1.37  Inference rules
% 2.26/1.37  ----------------------
% 2.26/1.37  #Ref     : 0
% 2.26/1.37  #Sup     : 67
% 2.26/1.37  #Fact    : 0
% 2.26/1.37  #Define  : 0
% 2.26/1.37  #Split   : 0
% 2.26/1.37  #Chain   : 0
% 2.26/1.37  #Close   : 0
% 2.26/1.37  
% 2.26/1.37  Ordering : KBO
% 2.26/1.37  
% 2.26/1.37  Simplification rules
% 2.26/1.37  ----------------------
% 2.26/1.37  #Subsume      : 0
% 2.26/1.37  #Demod        : 19
% 2.26/1.37  #Tautology    : 54
% 2.26/1.37  #SimpNegUnit  : 0
% 2.26/1.37  #BackRed      : 1
% 2.26/1.37  
% 2.26/1.37  #Partial instantiations: 0
% 2.26/1.37  #Strategies tried      : 1
% 2.26/1.37  
% 2.26/1.37  Timing (in seconds)
% 2.26/1.37  ----------------------
% 2.26/1.37  Preprocessing        : 0.34
% 2.26/1.37  Parsing              : 0.18
% 2.26/1.37  CNF conversion       : 0.02
% 2.26/1.37  Main loop            : 0.17
% 2.26/1.37  Inferencing          : 0.06
% 2.26/1.37  Reduction            : 0.06
% 2.26/1.37  Demodulation         : 0.05
% 2.26/1.37  BG Simplification    : 0.02
% 2.26/1.37  Subsumption          : 0.03
% 2.26/1.37  Abstraction          : 0.01
% 2.26/1.37  MUC search           : 0.00
% 2.26/1.37  Cooper               : 0.00
% 2.26/1.37  Total                : 0.54
% 2.26/1.37  Index Insertion      : 0.00
% 2.26/1.37  Index Deletion       : 0.00
% 2.26/1.37  Index Matching       : 0.00
% 2.26/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
