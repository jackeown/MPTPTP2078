%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:21 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   39 (  60 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :   49 (  88 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_58,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_8,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_21,plain,(
    ! [A_14] :
      ( v1_relat_1(A_14)
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_25,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_21])).

tff(c_105,plain,(
    ! [A_33,B_34,C_35] :
      ( r2_hidden(k4_tarski(A_33,'#skF_3'(A_33,B_34,C_35)),C_35)
      | ~ r2_hidden(A_33,k10_relat_1(C_35,B_34))
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_43,plain,(
    ! [A_20,B_21,C_22] :
      ( r2_hidden('#skF_3'(A_20,B_21,C_22),B_21)
      | ~ r2_hidden(A_20,k10_relat_1(C_22,B_21))
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_53,plain,(
    ! [B_26,A_27,C_28] :
      ( ~ v1_xboole_0(B_26)
      | ~ r2_hidden(A_27,k10_relat_1(C_28,B_26))
      | ~ v1_relat_1(C_28) ) ),
    inference(resolution,[status(thm)],[c_43,c_2])).

tff(c_69,plain,(
    ! [B_29,C_30] :
      ( ~ v1_xboole_0(B_29)
      | ~ v1_relat_1(C_30)
      | k10_relat_1(C_30,B_29) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_53])).

tff(c_73,plain,(
    ! [C_31] :
      ( ~ v1_relat_1(C_31)
      | k10_relat_1(C_31,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_69])).

tff(c_77,plain,(
    k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_25,c_73])).

tff(c_47,plain,(
    ! [B_21,A_20,C_22] :
      ( ~ v1_xboole_0(B_21)
      | ~ r2_hidden(A_20,k10_relat_1(C_22,B_21))
      | ~ v1_relat_1(C_22) ) ),
    inference(resolution,[status(thm)],[c_43,c_2])).

tff(c_81,plain,(
    ! [A_20] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_20,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_47])).

tff(c_85,plain,(
    ! [A_20] : ~ r2_hidden(A_20,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_6,c_81])).

tff(c_109,plain,(
    ! [A_33,B_34] :
      ( ~ r2_hidden(A_33,k10_relat_1(k1_xboole_0,B_34))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_105,c_85])).

tff(c_122,plain,(
    ! [A_36,B_37] : ~ r2_hidden(A_36,k10_relat_1(k1_xboole_0,B_37)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_109])).

tff(c_143,plain,(
    ! [B_37] : k10_relat_1(k1_xboole_0,B_37) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_122])).

tff(c_20,plain,(
    k10_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_149,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:45:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.20  
% 1.77/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.21  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_4 > #skF_3
% 1.77/1.21  
% 1.77/1.21  %Foreground sorts:
% 1.77/1.21  
% 1.77/1.21  
% 1.77/1.21  %Background operators:
% 1.77/1.21  
% 1.77/1.21  
% 1.77/1.21  %Foreground operators:
% 1.77/1.21  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.77/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.77/1.21  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.77/1.21  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.77/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.77/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.77/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.21  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.77/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.77/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.77/1.21  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.77/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.77/1.21  
% 1.77/1.22  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.77/1.22  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.77/1.22  tff(f_44, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.77/1.22  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 1.77/1.22  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.77/1.22  tff(f_58, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 1.77/1.22  tff(c_8, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.77/1.22  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.77/1.22  tff(c_21, plain, (![A_14]: (v1_relat_1(A_14) | ~v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.77/1.22  tff(c_25, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_21])).
% 1.77/1.22  tff(c_105, plain, (![A_33, B_34, C_35]: (r2_hidden(k4_tarski(A_33, '#skF_3'(A_33, B_34, C_35)), C_35) | ~r2_hidden(A_33, k10_relat_1(C_35, B_34)) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.77/1.22  tff(c_43, plain, (![A_20, B_21, C_22]: (r2_hidden('#skF_3'(A_20, B_21, C_22), B_21) | ~r2_hidden(A_20, k10_relat_1(C_22, B_21)) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.77/1.22  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.77/1.22  tff(c_53, plain, (![B_26, A_27, C_28]: (~v1_xboole_0(B_26) | ~r2_hidden(A_27, k10_relat_1(C_28, B_26)) | ~v1_relat_1(C_28))), inference(resolution, [status(thm)], [c_43, c_2])).
% 1.77/1.22  tff(c_69, plain, (![B_29, C_30]: (~v1_xboole_0(B_29) | ~v1_relat_1(C_30) | k10_relat_1(C_30, B_29)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_53])).
% 1.77/1.22  tff(c_73, plain, (![C_31]: (~v1_relat_1(C_31) | k10_relat_1(C_31, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_69])).
% 1.77/1.22  tff(c_77, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_25, c_73])).
% 1.77/1.22  tff(c_47, plain, (![B_21, A_20, C_22]: (~v1_xboole_0(B_21) | ~r2_hidden(A_20, k10_relat_1(C_22, B_21)) | ~v1_relat_1(C_22))), inference(resolution, [status(thm)], [c_43, c_2])).
% 1.77/1.22  tff(c_81, plain, (![A_20]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_20, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_77, c_47])).
% 1.77/1.22  tff(c_85, plain, (![A_20]: (~r2_hidden(A_20, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_25, c_6, c_81])).
% 1.77/1.22  tff(c_109, plain, (![A_33, B_34]: (~r2_hidden(A_33, k10_relat_1(k1_xboole_0, B_34)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_105, c_85])).
% 1.77/1.22  tff(c_122, plain, (![A_36, B_37]: (~r2_hidden(A_36, k10_relat_1(k1_xboole_0, B_37)))), inference(demodulation, [status(thm), theory('equality')], [c_25, c_109])).
% 1.77/1.22  tff(c_143, plain, (![B_37]: (k10_relat_1(k1_xboole_0, B_37)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_122])).
% 1.77/1.22  tff(c_20, plain, (k10_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.77/1.22  tff(c_149, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_143, c_20])).
% 1.77/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.22  
% 1.77/1.22  Inference rules
% 1.77/1.22  ----------------------
% 1.77/1.22  #Ref     : 0
% 1.77/1.22  #Sup     : 25
% 1.77/1.22  #Fact    : 0
% 1.77/1.22  #Define  : 0
% 1.77/1.22  #Split   : 0
% 1.77/1.22  #Chain   : 0
% 1.77/1.22  #Close   : 0
% 1.77/1.22  
% 1.77/1.22  Ordering : KBO
% 1.77/1.22  
% 1.77/1.22  Simplification rules
% 1.77/1.22  ----------------------
% 1.77/1.22  #Subsume      : 2
% 1.77/1.22  #Demod        : 7
% 1.77/1.22  #Tautology    : 7
% 1.77/1.22  #SimpNegUnit  : 0
% 1.77/1.22  #BackRed      : 2
% 1.77/1.22  
% 1.77/1.22  #Partial instantiations: 0
% 1.77/1.22  #Strategies tried      : 1
% 1.77/1.22  
% 1.77/1.22  Timing (in seconds)
% 1.77/1.22  ----------------------
% 1.77/1.22  Preprocessing        : 0.28
% 1.77/1.22  Parsing              : 0.16
% 1.77/1.22  CNF conversion       : 0.02
% 1.77/1.22  Main loop            : 0.13
% 1.77/1.22  Inferencing          : 0.06
% 1.77/1.22  Reduction            : 0.03
% 1.77/1.22  Demodulation         : 0.02
% 1.77/1.22  BG Simplification    : 0.01
% 1.77/1.22  Subsumption          : 0.02
% 1.77/1.22  Abstraction          : 0.01
% 1.77/1.22  MUC search           : 0.00
% 1.77/1.22  Cooper               : 0.00
% 1.77/1.22  Total                : 0.43
% 1.77/1.22  Index Insertion      : 0.00
% 1.77/1.22  Index Deletion       : 0.00
% 1.77/1.22  Index Matching       : 0.00
% 1.77/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
