%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:30 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   45 (  50 expanded)
%              Number of leaves         :   33 (  35 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  39 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_6 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_84,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_73,plain,(
    ! [A_69] :
      ( r2_hidden('#skF_2'(A_69),A_69)
      | v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_61,plain,(
    ! [C_65,B_66] : ~ r2_hidden(C_65,k4_xboole_0(B_66,k1_tarski(C_65))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_64,plain,(
    ! [C_65] : ~ r2_hidden(C_65,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_61])).

tff(c_78,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_73,c_64])).

tff(c_614,plain,(
    ! [A_138,B_139,C_140] :
      ( r2_hidden(k4_tarski(A_138,'#skF_5'(A_138,B_139,C_140)),C_140)
      | ~ r2_hidden(A_138,k10_relat_1(C_140,B_139))
      | ~ v1_relat_1(C_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_630,plain,(
    ! [A_138,B_139] :
      ( ~ r2_hidden(A_138,k10_relat_1(k1_xboole_0,B_139))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_614,c_64])).

tff(c_637,plain,(
    ! [A_141,B_142] : ~ r2_hidden(A_141,k10_relat_1(k1_xboole_0,B_142)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_630])).

tff(c_675,plain,(
    ! [B_142] : k10_relat_1(k1_xboole_0,B_142) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_637])).

tff(c_44,plain,(
    k10_relat_1(k1_xboole_0,'#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_696,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_675,c_44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:12:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.34  
% 2.51/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.34  %$ r2_hidden > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_6 > #skF_5 > #skF_4
% 2.51/1.34  
% 2.51/1.34  %Foreground sorts:
% 2.51/1.34  
% 2.51/1.34  
% 2.51/1.34  %Background operators:
% 2.51/1.34  
% 2.51/1.34  
% 2.51/1.34  %Foreground operators:
% 2.51/1.34  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.51/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.51/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.51/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.51/1.34  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.51/1.34  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.51/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.51/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.51/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.51/1.34  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.51/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.51/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.51/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.51/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.51/1.34  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.51/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.51/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.51/1.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.51/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.34  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.51/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.51/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.51/1.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.51/1.34  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.51/1.34  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.51/1.34  
% 2.51/1.35  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.51/1.35  tff(f_70, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.51/1.35  tff(f_37, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.51/1.35  tff(f_58, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.51/1.35  tff(f_81, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.51/1.35  tff(f_84, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 2.51/1.35  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.51/1.35  tff(c_73, plain, (![A_69]: (r2_hidden('#skF_2'(A_69), A_69) | v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.51/1.35  tff(c_6, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.51/1.35  tff(c_61, plain, (![C_65, B_66]: (~r2_hidden(C_65, k4_xboole_0(B_66, k1_tarski(C_65))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.51/1.35  tff(c_64, plain, (![C_65]: (~r2_hidden(C_65, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_61])).
% 2.51/1.35  tff(c_78, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_73, c_64])).
% 2.51/1.35  tff(c_614, plain, (![A_138, B_139, C_140]: (r2_hidden(k4_tarski(A_138, '#skF_5'(A_138, B_139, C_140)), C_140) | ~r2_hidden(A_138, k10_relat_1(C_140, B_139)) | ~v1_relat_1(C_140))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.51/1.35  tff(c_630, plain, (![A_138, B_139]: (~r2_hidden(A_138, k10_relat_1(k1_xboole_0, B_139)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_614, c_64])).
% 2.51/1.35  tff(c_637, plain, (![A_141, B_142]: (~r2_hidden(A_141, k10_relat_1(k1_xboole_0, B_142)))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_630])).
% 2.51/1.35  tff(c_675, plain, (![B_142]: (k10_relat_1(k1_xboole_0, B_142)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_637])).
% 2.51/1.35  tff(c_44, plain, (k10_relat_1(k1_xboole_0, '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.51/1.35  tff(c_696, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_675, c_44])).
% 2.51/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.35  
% 2.51/1.35  Inference rules
% 2.51/1.35  ----------------------
% 2.51/1.35  #Ref     : 1
% 2.51/1.35  #Sup     : 143
% 2.51/1.35  #Fact    : 0
% 2.51/1.35  #Define  : 0
% 2.51/1.35  #Split   : 0
% 2.51/1.35  #Chain   : 0
% 2.51/1.35  #Close   : 0
% 2.51/1.35  
% 2.51/1.35  Ordering : KBO
% 2.51/1.35  
% 2.51/1.35  Simplification rules
% 2.51/1.35  ----------------------
% 2.51/1.35  #Subsume      : 26
% 2.51/1.35  #Demod        : 66
% 2.51/1.35  #Tautology    : 80
% 2.51/1.35  #SimpNegUnit  : 5
% 2.51/1.35  #BackRed      : 3
% 2.51/1.35  
% 2.51/1.35  #Partial instantiations: 0
% 2.51/1.35  #Strategies tried      : 1
% 2.51/1.35  
% 2.51/1.35  Timing (in seconds)
% 2.51/1.35  ----------------------
% 2.51/1.36  Preprocessing        : 0.33
% 2.51/1.36  Parsing              : 0.17
% 2.51/1.36  CNF conversion       : 0.02
% 2.51/1.36  Main loop            : 0.27
% 2.51/1.36  Inferencing          : 0.11
% 2.51/1.36  Reduction            : 0.08
% 2.51/1.36  Demodulation         : 0.05
% 2.51/1.36  BG Simplification    : 0.02
% 2.51/1.36  Subsumption          : 0.05
% 2.51/1.36  Abstraction          : 0.02
% 2.51/1.36  MUC search           : 0.00
% 2.51/1.36  Cooper               : 0.00
% 2.51/1.36  Total                : 0.63
% 2.51/1.36  Index Insertion      : 0.00
% 2.51/1.36  Index Deletion       : 0.00
% 2.51/1.36  Index Matching       : 0.00
% 2.51/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
