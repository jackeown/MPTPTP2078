%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:02 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   50 (  52 expanded)
%              Number of leaves         :   34 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   32 (  34 expanded)
%              Number of equality atoms :   19 (  21 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k3_xboole_0(B,k2_zfmisc_1(A,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_73,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_156,plain,(
    ! [A_69] :
      ( r2_hidden('#skF_1'(A_69),A_69)
      | v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    ! [C_63,B_64] : ~ r2_hidden(C_63,k4_xboole_0(B_64,k1_tarski(C_63))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_69,plain,(
    ! [C_63] : ~ r2_hidden(C_63,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_66])).

tff(c_161,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_156,c_69])).

tff(c_280,plain,(
    ! [B_88,A_89] :
      ( k3_xboole_0(B_88,k2_zfmisc_1(A_89,k2_relat_1(B_88))) = k7_relat_1(B_88,A_89)
      | ~ v1_relat_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_203,plain,(
    ! [A_78,B_79] : k5_xboole_0(A_78,k3_xboole_0(A_78,B_79)) = k4_xboole_0(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_70,plain,(
    ! [B_65,A_66] : k5_xboole_0(B_65,A_66) = k5_xboole_0(A_66,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_108,plain,(
    ! [A_6] : k5_xboole_0(k1_xboole_0,A_6) = A_6 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_70])).

tff(c_210,plain,(
    ! [B_79] : k4_xboole_0(k1_xboole_0,B_79) = k3_xboole_0(k1_xboole_0,B_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_108])).

tff(c_222,plain,(
    ! [B_79] : k3_xboole_0(k1_xboole_0,B_79) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_210])).

tff(c_287,plain,(
    ! [A_89] :
      ( k7_relat_1(k1_xboole_0,A_89) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_222])).

tff(c_300,plain,(
    ! [A_89] : k7_relat_1(k1_xboole_0,A_89) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_287])).

tff(c_40,plain,(
    k7_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_306,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:04:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.65  
% 2.54/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.66  %$ r2_hidden > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.54/1.66  
% 2.54/1.66  %Foreground sorts:
% 2.54/1.66  
% 2.54/1.66  
% 2.54/1.66  %Background operators:
% 2.54/1.66  
% 2.54/1.66  
% 2.54/1.66  %Foreground operators:
% 2.54/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.54/1.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.54/1.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.54/1.66  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.54/1.66  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.54/1.66  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.54/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.54/1.66  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.54/1.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.54/1.66  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.54/1.66  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.54/1.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.54/1.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.54/1.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.54/1.66  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.54/1.66  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.54/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.54/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.54/1.66  tff('#skF_4', type, '#skF_4': $i).
% 2.54/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.66  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.54/1.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.54/1.66  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.54/1.66  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.54/1.66  
% 2.54/1.67  tff(f_66, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.54/1.67  tff(f_31, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.54/1.67  tff(f_54, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.54/1.67  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k3_xboole_0(B, k2_zfmisc_1(A, k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_relat_1)).
% 2.54/1.67  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.54/1.67  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.54/1.67  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 2.54/1.67  tff(f_73, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 2.54/1.67  tff(c_156, plain, (![A_69]: (r2_hidden('#skF_1'(A_69), A_69) | v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.54/1.67  tff(c_6, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.54/1.67  tff(c_66, plain, (![C_63, B_64]: (~r2_hidden(C_63, k4_xboole_0(B_64, k1_tarski(C_63))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.54/1.67  tff(c_69, plain, (![C_63]: (~r2_hidden(C_63, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_66])).
% 2.54/1.67  tff(c_161, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_156, c_69])).
% 2.54/1.67  tff(c_280, plain, (![B_88, A_89]: (k3_xboole_0(B_88, k2_zfmisc_1(A_89, k2_relat_1(B_88)))=k7_relat_1(B_88, A_89) | ~v1_relat_1(B_88))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.54/1.67  tff(c_203, plain, (![A_78, B_79]: (k5_xboole_0(A_78, k3_xboole_0(A_78, B_79))=k4_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.54/1.67  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.54/1.67  tff(c_70, plain, (![B_65, A_66]: (k5_xboole_0(B_65, A_66)=k5_xboole_0(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.54/1.67  tff(c_108, plain, (![A_6]: (k5_xboole_0(k1_xboole_0, A_6)=A_6)), inference(superposition, [status(thm), theory('equality')], [c_8, c_70])).
% 2.54/1.67  tff(c_210, plain, (![B_79]: (k4_xboole_0(k1_xboole_0, B_79)=k3_xboole_0(k1_xboole_0, B_79))), inference(superposition, [status(thm), theory('equality')], [c_203, c_108])).
% 2.54/1.67  tff(c_222, plain, (![B_79]: (k3_xboole_0(k1_xboole_0, B_79)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_210])).
% 2.54/1.67  tff(c_287, plain, (![A_89]: (k7_relat_1(k1_xboole_0, A_89)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_280, c_222])).
% 2.54/1.67  tff(c_300, plain, (![A_89]: (k7_relat_1(k1_xboole_0, A_89)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_161, c_287])).
% 2.54/1.67  tff(c_40, plain, (k7_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.54/1.67  tff(c_306, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_300, c_40])).
% 2.54/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.67  
% 2.54/1.67  Inference rules
% 2.54/1.67  ----------------------
% 2.54/1.67  #Ref     : 0
% 2.54/1.67  #Sup     : 59
% 2.54/1.67  #Fact    : 0
% 2.54/1.67  #Define  : 0
% 2.54/1.67  #Split   : 0
% 2.54/1.67  #Chain   : 0
% 2.54/1.67  #Close   : 0
% 2.54/1.67  
% 2.54/1.67  Ordering : KBO
% 2.54/1.67  
% 2.54/1.67  Simplification rules
% 2.54/1.67  ----------------------
% 2.54/1.67  #Subsume      : 1
% 2.54/1.67  #Demod        : 22
% 2.54/1.67  #Tautology    : 48
% 2.54/1.67  #SimpNegUnit  : 1
% 2.54/1.67  #BackRed      : 1
% 2.54/1.67  
% 2.54/1.67  #Partial instantiations: 0
% 2.54/1.67  #Strategies tried      : 1
% 2.54/1.67  
% 2.54/1.67  Timing (in seconds)
% 2.54/1.67  ----------------------
% 2.54/1.68  Preprocessing        : 0.50
% 2.54/1.68  Parsing              : 0.25
% 2.54/1.68  CNF conversion       : 0.04
% 2.54/1.68  Main loop            : 0.26
% 2.54/1.68  Inferencing          : 0.10
% 2.54/1.68  Reduction            : 0.09
% 2.54/1.68  Demodulation         : 0.07
% 2.54/1.68  BG Simplification    : 0.02
% 2.65/1.68  Subsumption          : 0.03
% 2.65/1.68  Abstraction          : 0.02
% 2.65/1.68  MUC search           : 0.00
% 2.65/1.68  Cooper               : 0.00
% 2.65/1.68  Total                : 0.80
% 2.65/1.68  Index Insertion      : 0.00
% 2.65/1.68  Index Deletion       : 0.00
% 2.65/1.68  Index Matching       : 0.00
% 2.65/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
