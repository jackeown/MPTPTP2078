%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:40 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   46 (  46 expanded)
%              Number of leaves         :   34 (  34 expanded)
%              Depth                    :    5
%              Number of atoms          :   28 (  28 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_69,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_62,axiom,(
    ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_30,plain,(
    ! [A_36] :
      ( r2_hidden('#skF_1'(A_36),A_36)
      | v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_131,plain,(
    ! [B_71,A_72] :
      ( ~ r2_hidden(B_71,A_72)
      | k4_xboole_0(A_72,k1_tarski(B_71)) != A_72 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_141,plain,(
    ! [B_73] : ~ r2_hidden(B_73,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_131])).

tff(c_146,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_30,c_141])).

tff(c_36,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_32,plain,(
    ! [A_54] : k7_relat_1(k1_xboole_0,A_54) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_172,plain,(
    ! [B_77,A_78] :
      ( k2_relat_1(k7_relat_1(B_77,A_78)) = k9_relat_1(B_77,A_78)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_181,plain,(
    ! [A_54] :
      ( k9_relat_1(k1_xboole_0,A_54) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_172])).

tff(c_185,plain,(
    ! [A_54] : k9_relat_1(k1_xboole_0,A_54) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_36,c_181])).

tff(c_40,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n011.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 12:45:42 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.16  
% 1.74/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.16  %$ r2_hidden > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.74/1.16  
% 1.74/1.16  %Foreground sorts:
% 1.74/1.16  
% 1.74/1.16  
% 1.74/1.16  %Background operators:
% 1.74/1.16  
% 1.74/1.16  
% 1.74/1.16  %Foreground operators:
% 1.74/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.74/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.74/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.74/1.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.74/1.16  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.74/1.16  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.74/1.16  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.74/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.74/1.16  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.74/1.16  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.74/1.16  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.74/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.74/1.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.74/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.74/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.74/1.16  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.74/1.16  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.74/1.16  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.74/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.74/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.74/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.74/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.74/1.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.74/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.74/1.16  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.74/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.74/1.16  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.74/1.16  
% 1.74/1.17  tff(f_60, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 1.74/1.17  tff(f_29, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.74/1.17  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.74/1.17  tff(f_69, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.74/1.17  tff(f_62, axiom, (![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 1.74/1.17  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.74/1.17  tff(f_72, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 1.74/1.17  tff(c_30, plain, (![A_36]: (r2_hidden('#skF_1'(A_36), A_36) | v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.74/1.17  tff(c_4, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.74/1.17  tff(c_131, plain, (![B_71, A_72]: (~r2_hidden(B_71, A_72) | k4_xboole_0(A_72, k1_tarski(B_71))!=A_72)), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.74/1.17  tff(c_141, plain, (![B_73]: (~r2_hidden(B_73, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_131])).
% 1.74/1.17  tff(c_146, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_141])).
% 1.74/1.17  tff(c_36, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.74/1.17  tff(c_32, plain, (![A_54]: (k7_relat_1(k1_xboole_0, A_54)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.74/1.17  tff(c_172, plain, (![B_77, A_78]: (k2_relat_1(k7_relat_1(B_77, A_78))=k9_relat_1(B_77, A_78) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.74/1.17  tff(c_181, plain, (![A_54]: (k9_relat_1(k1_xboole_0, A_54)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_172])).
% 1.74/1.17  tff(c_185, plain, (![A_54]: (k9_relat_1(k1_xboole_0, A_54)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_146, c_36, c_181])).
% 1.74/1.17  tff(c_40, plain, (k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.74/1.17  tff(c_188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_185, c_40])).
% 1.74/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.17  
% 1.74/1.17  Inference rules
% 1.74/1.17  ----------------------
% 1.74/1.17  #Ref     : 0
% 1.74/1.17  #Sup     : 35
% 1.74/1.17  #Fact    : 0
% 1.74/1.17  #Define  : 0
% 1.74/1.17  #Split   : 0
% 1.74/1.17  #Chain   : 0
% 1.74/1.17  #Close   : 0
% 1.74/1.17  
% 1.74/1.17  Ordering : KBO
% 1.74/1.17  
% 1.74/1.17  Simplification rules
% 1.74/1.17  ----------------------
% 1.74/1.17  #Subsume      : 0
% 1.74/1.17  #Demod        : 4
% 1.74/1.17  #Tautology    : 30
% 1.74/1.17  #SimpNegUnit  : 0
% 1.74/1.17  #BackRed      : 1
% 1.74/1.17  
% 1.74/1.17  #Partial instantiations: 0
% 1.74/1.17  #Strategies tried      : 1
% 1.74/1.17  
% 1.74/1.17  Timing (in seconds)
% 1.74/1.17  ----------------------
% 1.74/1.17  Preprocessing        : 0.30
% 1.74/1.17  Parsing              : 0.16
% 1.74/1.17  CNF conversion       : 0.02
% 1.74/1.17  Main loop            : 0.12
% 1.74/1.17  Inferencing          : 0.05
% 1.74/1.17  Reduction            : 0.04
% 1.74/1.17  Demodulation         : 0.03
% 1.74/1.17  BG Simplification    : 0.01
% 1.74/1.17  Subsumption          : 0.01
% 1.74/1.17  Abstraction          : 0.01
% 1.74/1.17  MUC search           : 0.00
% 1.74/1.17  Cooper               : 0.00
% 1.74/1.17  Total                : 0.44
% 1.74/1.17  Index Insertion      : 0.00
% 1.74/1.17  Index Deletion       : 0.00
% 1.74/1.17  Index Matching       : 0.00
% 1.74/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
