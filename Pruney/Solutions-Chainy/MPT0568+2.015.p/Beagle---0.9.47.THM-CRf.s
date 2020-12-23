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
% DateTime   : Thu Dec  3 10:01:22 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   36 (  36 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  33 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_36,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_61,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_24,plain,(
    ! [A_15] :
      ( v1_relat_1(A_15)
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_28,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_24])).

tff(c_117,plain,(
    ! [A_35,B_36,C_37] :
      ( r2_hidden(k4_tarski(A_35,'#skF_2'(A_35,B_36,C_37)),C_37)
      | ~ r2_hidden(A_35,k10_relat_1(C_37,B_36))
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_39,plain,(
    ! [A_18,B_19] :
      ( ~ r2_hidden(A_18,B_19)
      | ~ r1_xboole_0(k1_tarski(A_18),B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_44,plain,(
    ! [A_18] : ~ r2_hidden(A_18,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_39])).

tff(c_129,plain,(
    ! [A_35,B_36] :
      ( ~ r2_hidden(A_35,k10_relat_1(k1_xboole_0,B_36))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_117,c_44])).

tff(c_135,plain,(
    ! [A_38,B_39] : ~ r2_hidden(A_38,k10_relat_1(k1_xboole_0,B_39)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_129])).

tff(c_158,plain,(
    ! [B_39] : k10_relat_1(k1_xboole_0,B_39) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_135])).

tff(c_22,plain,(
    k10_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:59:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.15  
% 1.76/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.15  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.76/1.15  
% 1.76/1.15  %Foreground sorts:
% 1.76/1.15  
% 1.76/1.15  
% 1.76/1.15  %Background operators:
% 1.76/1.15  
% 1.76/1.15  
% 1.76/1.15  %Foreground operators:
% 1.76/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.76/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.76/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.76/1.15  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.76/1.15  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.76/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.76/1.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.76/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.76/1.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.76/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.76/1.15  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.76/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.76/1.15  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.76/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.76/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.76/1.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.76/1.15  
% 1.76/1.16  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.76/1.16  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.76/1.16  tff(f_47, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.76/1.16  tff(f_58, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 1.76/1.16  tff(f_36, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.76/1.16  tff(f_43, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.76/1.16  tff(f_61, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 1.76/1.16  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.76/1.16  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.76/1.16  tff(c_24, plain, (![A_15]: (v1_relat_1(A_15) | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.76/1.16  tff(c_28, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_24])).
% 1.76/1.16  tff(c_117, plain, (![A_35, B_36, C_37]: (r2_hidden(k4_tarski(A_35, '#skF_2'(A_35, B_36, C_37)), C_37) | ~r2_hidden(A_35, k10_relat_1(C_37, B_36)) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.76/1.16  tff(c_6, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.76/1.16  tff(c_39, plain, (![A_18, B_19]: (~r2_hidden(A_18, B_19) | ~r1_xboole_0(k1_tarski(A_18), B_19))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.76/1.16  tff(c_44, plain, (![A_18]: (~r2_hidden(A_18, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_39])).
% 1.76/1.16  tff(c_129, plain, (![A_35, B_36]: (~r2_hidden(A_35, k10_relat_1(k1_xboole_0, B_36)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_117, c_44])).
% 1.76/1.16  tff(c_135, plain, (![A_38, B_39]: (~r2_hidden(A_38, k10_relat_1(k1_xboole_0, B_39)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_129])).
% 1.76/1.16  tff(c_158, plain, (![B_39]: (k10_relat_1(k1_xboole_0, B_39)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_135])).
% 1.76/1.16  tff(c_22, plain, (k10_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.76/1.16  tff(c_163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_158, c_22])).
% 1.76/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.16  
% 1.76/1.16  Inference rules
% 1.76/1.16  ----------------------
% 1.76/1.16  #Ref     : 0
% 1.76/1.16  #Sup     : 27
% 1.76/1.16  #Fact    : 0
% 1.76/1.16  #Define  : 0
% 1.76/1.16  #Split   : 0
% 1.76/1.16  #Chain   : 0
% 1.76/1.16  #Close   : 0
% 1.76/1.16  
% 1.76/1.16  Ordering : KBO
% 1.76/1.16  
% 1.76/1.16  Simplification rules
% 1.76/1.16  ----------------------
% 1.76/1.16  #Subsume      : 7
% 1.76/1.16  #Demod        : 8
% 1.76/1.16  #Tautology    : 8
% 1.76/1.16  #SimpNegUnit  : 0
% 1.76/1.16  #BackRed      : 2
% 1.76/1.16  
% 1.76/1.16  #Partial instantiations: 0
% 1.76/1.16  #Strategies tried      : 1
% 1.76/1.16  
% 1.76/1.16  Timing (in seconds)
% 1.76/1.16  ----------------------
% 1.76/1.16  Preprocessing        : 0.28
% 1.76/1.16  Parsing              : 0.15
% 1.76/1.16  CNF conversion       : 0.02
% 1.76/1.16  Main loop            : 0.13
% 1.76/1.16  Inferencing          : 0.06
% 1.76/1.16  Reduction            : 0.03
% 1.76/1.16  Demodulation         : 0.02
% 1.76/1.16  BG Simplification    : 0.01
% 1.76/1.16  Subsumption          : 0.02
% 1.76/1.16  Abstraction          : 0.01
% 1.76/1.16  MUC search           : 0.00
% 1.76/1.16  Cooper               : 0.00
% 1.76/1.16  Total                : 0.43
% 1.76/1.16  Index Insertion      : 0.00
% 1.76/1.16  Index Deletion       : 0.00
% 1.76/1.16  Index Matching       : 0.00
% 1.76/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
