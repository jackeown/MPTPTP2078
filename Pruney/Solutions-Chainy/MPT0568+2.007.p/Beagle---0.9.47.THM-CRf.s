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
% DateTime   : Thu Dec  3 10:01:21 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   42 (  44 expanded)
%              Number of leaves         :   24 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 (  50 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_67,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_70,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_69,plain,(
    ! [A_23,B_24] : ~ r2_hidden(A_23,k2_zfmisc_1(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_75,plain,(
    ! [A_7] : ~ r2_hidden(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_69])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_41,plain,(
    ! [A_18] :
      ( v1_relat_1(A_18)
      | ~ v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_45,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_41])).

tff(c_28,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_142,plain,(
    ! [A_38,B_39,C_40] :
      ( r2_hidden('#skF_2'(A_38,B_39,C_40),k2_relat_1(C_40))
      | ~ r2_hidden(A_38,k10_relat_1(C_40,B_39))
      | ~ v1_relat_1(C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_148,plain,(
    ! [A_38,B_39] :
      ( r2_hidden('#skF_2'(A_38,B_39,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_38,k10_relat_1(k1_xboole_0,B_39))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_142])).

tff(c_151,plain,(
    ! [A_38,B_39] :
      ( r2_hidden('#skF_2'(A_38,B_39,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_38,k10_relat_1(k1_xboole_0,B_39)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_148])).

tff(c_153,plain,(
    ! [A_41,B_42] : ~ r2_hidden(A_41,k10_relat_1(k1_xboole_0,B_42)) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_151])).

tff(c_164,plain,(
    ! [B_43] : v1_xboole_0(k10_relat_1(k1_xboole_0,B_43)) ),
    inference(resolution,[status(thm)],[c_4,c_153])).

tff(c_77,plain,(
    ! [B_26,A_27] :
      ( ~ v1_xboole_0(B_26)
      | B_26 = A_27
      | ~ v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_80,plain,(
    ! [A_27] :
      ( k1_xboole_0 = A_27
      | ~ v1_xboole_0(A_27) ) ),
    inference(resolution,[status(thm)],[c_6,c_77])).

tff(c_173,plain,(
    ! [B_43] : k10_relat_1(k1_xboole_0,B_43) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_164,c_80])).

tff(c_32,plain,(
    k10_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:27:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.20  
% 1.82/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.20  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.82/1.20  
% 1.82/1.20  %Foreground sorts:
% 1.82/1.20  
% 1.82/1.20  
% 1.82/1.20  %Background operators:
% 1.82/1.20  
% 1.82/1.20  
% 1.82/1.20  %Foreground operators:
% 1.82/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.82/1.20  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.82/1.20  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.82/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.82/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.82/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.82/1.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.82/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.20  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.82/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.82/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.82/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.82/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.82/1.21  
% 1.82/1.22  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.82/1.22  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.82/1.22  tff(f_49, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.82/1.22  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.82/1.22  tff(f_53, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.82/1.22  tff(f_67, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.82/1.22  tff(f_64, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 1.82/1.22  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 1.82/1.22  tff(f_70, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 1.82/1.22  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.82/1.22  tff(c_12, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.82/1.22  tff(c_69, plain, (![A_23, B_24]: (~r2_hidden(A_23, k2_zfmisc_1(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.82/1.22  tff(c_75, plain, (![A_7]: (~r2_hidden(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_69])).
% 1.82/1.22  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.82/1.22  tff(c_41, plain, (![A_18]: (v1_relat_1(A_18) | ~v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.82/1.22  tff(c_45, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_41])).
% 1.82/1.22  tff(c_28, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.82/1.22  tff(c_142, plain, (![A_38, B_39, C_40]: (r2_hidden('#skF_2'(A_38, B_39, C_40), k2_relat_1(C_40)) | ~r2_hidden(A_38, k10_relat_1(C_40, B_39)) | ~v1_relat_1(C_40))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.82/1.22  tff(c_148, plain, (![A_38, B_39]: (r2_hidden('#skF_2'(A_38, B_39, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_38, k10_relat_1(k1_xboole_0, B_39)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_142])).
% 1.82/1.22  tff(c_151, plain, (![A_38, B_39]: (r2_hidden('#skF_2'(A_38, B_39, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_38, k10_relat_1(k1_xboole_0, B_39)))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_148])).
% 1.82/1.22  tff(c_153, plain, (![A_41, B_42]: (~r2_hidden(A_41, k10_relat_1(k1_xboole_0, B_42)))), inference(negUnitSimplification, [status(thm)], [c_75, c_151])).
% 1.82/1.22  tff(c_164, plain, (![B_43]: (v1_xboole_0(k10_relat_1(k1_xboole_0, B_43)))), inference(resolution, [status(thm)], [c_4, c_153])).
% 1.82/1.22  tff(c_77, plain, (![B_26, A_27]: (~v1_xboole_0(B_26) | B_26=A_27 | ~v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.82/1.22  tff(c_80, plain, (![A_27]: (k1_xboole_0=A_27 | ~v1_xboole_0(A_27))), inference(resolution, [status(thm)], [c_6, c_77])).
% 1.82/1.22  tff(c_173, plain, (![B_43]: (k10_relat_1(k1_xboole_0, B_43)=k1_xboole_0)), inference(resolution, [status(thm)], [c_164, c_80])).
% 1.82/1.22  tff(c_32, plain, (k10_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.82/1.22  tff(c_181, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_173, c_32])).
% 1.82/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.22  
% 1.82/1.22  Inference rules
% 1.82/1.22  ----------------------
% 1.82/1.22  #Ref     : 0
% 1.82/1.22  #Sup     : 33
% 1.82/1.22  #Fact    : 0
% 1.82/1.22  #Define  : 0
% 1.82/1.22  #Split   : 0
% 1.82/1.22  #Chain   : 0
% 1.82/1.22  #Close   : 0
% 1.82/1.22  
% 1.82/1.22  Ordering : KBO
% 1.82/1.22  
% 1.82/1.22  Simplification rules
% 1.82/1.22  ----------------------
% 1.82/1.22  #Subsume      : 2
% 1.82/1.22  #Demod        : 6
% 1.82/1.22  #Tautology    : 16
% 1.82/1.22  #SimpNegUnit  : 1
% 1.82/1.22  #BackRed      : 3
% 1.82/1.22  
% 1.82/1.22  #Partial instantiations: 0
% 1.82/1.22  #Strategies tried      : 1
% 1.82/1.22  
% 1.82/1.22  Timing (in seconds)
% 1.82/1.22  ----------------------
% 1.82/1.22  Preprocessing        : 0.29
% 1.82/1.22  Parsing              : 0.16
% 1.82/1.22  CNF conversion       : 0.02
% 1.82/1.22  Main loop            : 0.15
% 1.82/1.22  Inferencing          : 0.06
% 1.82/1.22  Reduction            : 0.04
% 1.82/1.22  Demodulation         : 0.03
% 1.82/1.22  BG Simplification    : 0.01
% 1.82/1.22  Subsumption          : 0.03
% 1.82/1.22  Abstraction          : 0.01
% 1.82/1.22  MUC search           : 0.00
% 1.82/1.22  Cooper               : 0.00
% 1.82/1.22  Total                : 0.47
% 1.82/1.22  Index Insertion      : 0.00
% 1.82/1.22  Index Deletion       : 0.00
% 1.82/1.22  Index Matching       : 0.00
% 1.82/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
