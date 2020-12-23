%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:35 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   38 (  44 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   40 (  50 expanded)
%              Number of equality atoms :   14 (  21 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_57,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_88,plain,(
    ! [A_25,B_26] :
      ( r2_hidden('#skF_1'(A_25,B_26),B_26)
      | r2_hidden('#skF_2'(A_25,B_26),A_25)
      | B_26 = A_25 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_69,plain,(
    ! [A_20,B_21] : ~ r2_hidden(A_20,k2_zfmisc_1(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_72,plain,(
    ! [A_4] : ~ r2_hidden(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_69])).

tff(c_95,plain,(
    ! [B_26] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_26),B_26)
      | k1_xboole_0 = B_26 ) ),
    inference(resolution,[status(thm)],[c_88,c_72])).

tff(c_42,plain,(
    ! [B_18] : k2_zfmisc_1(k1_xboole_0,B_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_18,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_46,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_18])).

tff(c_28,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_160,plain,(
    ! [A_39,B_40,C_41] :
      ( r2_hidden('#skF_3'(A_39,B_40,C_41),k2_relat_1(C_41))
      | ~ r2_hidden(A_39,k10_relat_1(C_41,B_40))
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_163,plain,(
    ! [A_39,B_40] :
      ( r2_hidden('#skF_3'(A_39,B_40,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_39,k10_relat_1(k1_xboole_0,B_40))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_160])).

tff(c_165,plain,(
    ! [A_39,B_40] :
      ( r2_hidden('#skF_3'(A_39,B_40,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_39,k10_relat_1(k1_xboole_0,B_40)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_163])).

tff(c_167,plain,(
    ! [A_42,B_43] : ~ r2_hidden(A_42,k10_relat_1(k1_xboole_0,B_43)) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_165])).

tff(c_190,plain,(
    ! [B_43] : k10_relat_1(k1_xboole_0,B_43) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_95,c_167])).

tff(c_32,plain,(
    k10_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_196,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:37:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.22  
% 1.80/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.22  %$ r2_hidden > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 1.80/1.22  
% 1.80/1.22  %Foreground sorts:
% 1.80/1.22  
% 1.80/1.22  
% 1.80/1.22  %Background operators:
% 1.80/1.22  
% 1.80/1.22  
% 1.80/1.22  %Foreground operators:
% 1.80/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.80/1.22  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.80/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.80/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.80/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.22  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.80/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.80/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.80/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.80/1.22  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.80/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.80/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.80/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.80/1.22  
% 1.99/1.23  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 1.99/1.23  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.99/1.23  tff(f_41, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.99/1.23  tff(f_43, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.99/1.23  tff(f_57, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.99/1.23  tff(f_54, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 1.99/1.23  tff(f_60, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 1.99/1.23  tff(c_88, plain, (![A_25, B_26]: (r2_hidden('#skF_1'(A_25, B_26), B_26) | r2_hidden('#skF_2'(A_25, B_26), A_25) | B_26=A_25)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.99/1.23  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.99/1.23  tff(c_69, plain, (![A_20, B_21]: (~r2_hidden(A_20, k2_zfmisc_1(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.99/1.23  tff(c_72, plain, (![A_4]: (~r2_hidden(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_69])).
% 1.99/1.23  tff(c_95, plain, (![B_26]: (r2_hidden('#skF_1'(k1_xboole_0, B_26), B_26) | k1_xboole_0=B_26)), inference(resolution, [status(thm)], [c_88, c_72])).
% 1.99/1.23  tff(c_42, plain, (![B_18]: (k2_zfmisc_1(k1_xboole_0, B_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.99/1.23  tff(c_18, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.99/1.23  tff(c_46, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_42, c_18])).
% 1.99/1.23  tff(c_28, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.99/1.23  tff(c_160, plain, (![A_39, B_40, C_41]: (r2_hidden('#skF_3'(A_39, B_40, C_41), k2_relat_1(C_41)) | ~r2_hidden(A_39, k10_relat_1(C_41, B_40)) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.99/1.23  tff(c_163, plain, (![A_39, B_40]: (r2_hidden('#skF_3'(A_39, B_40, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_39, k10_relat_1(k1_xboole_0, B_40)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_160])).
% 1.99/1.23  tff(c_165, plain, (![A_39, B_40]: (r2_hidden('#skF_3'(A_39, B_40, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_39, k10_relat_1(k1_xboole_0, B_40)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_163])).
% 1.99/1.23  tff(c_167, plain, (![A_42, B_43]: (~r2_hidden(A_42, k10_relat_1(k1_xboole_0, B_43)))), inference(negUnitSimplification, [status(thm)], [c_72, c_165])).
% 1.99/1.23  tff(c_190, plain, (![B_43]: (k10_relat_1(k1_xboole_0, B_43)=k1_xboole_0)), inference(resolution, [status(thm)], [c_95, c_167])).
% 1.99/1.23  tff(c_32, plain, (k10_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.99/1.23  tff(c_196, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_190, c_32])).
% 1.99/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.23  
% 1.99/1.23  Inference rules
% 1.99/1.23  ----------------------
% 1.99/1.23  #Ref     : 0
% 1.99/1.23  #Sup     : 34
% 1.99/1.23  #Fact    : 0
% 1.99/1.23  #Define  : 0
% 1.99/1.23  #Split   : 0
% 1.99/1.23  #Chain   : 0
% 1.99/1.23  #Close   : 0
% 1.99/1.23  
% 1.99/1.23  Ordering : KBO
% 1.99/1.23  
% 1.99/1.23  Simplification rules
% 1.99/1.23  ----------------------
% 1.99/1.23  #Subsume      : 6
% 1.99/1.23  #Demod        : 4
% 1.99/1.23  #Tautology    : 16
% 1.99/1.23  #SimpNegUnit  : 1
% 1.99/1.23  #BackRed      : 2
% 1.99/1.23  
% 1.99/1.23  #Partial instantiations: 0
% 1.99/1.23  #Strategies tried      : 1
% 1.99/1.23  
% 1.99/1.23  Timing (in seconds)
% 1.99/1.23  ----------------------
% 1.99/1.23  Preprocessing        : 0.29
% 1.99/1.23  Parsing              : 0.17
% 1.99/1.23  CNF conversion       : 0.02
% 1.99/1.23  Main loop            : 0.15
% 1.99/1.23  Inferencing          : 0.06
% 1.99/1.23  Reduction            : 0.04
% 1.99/1.23  Demodulation         : 0.03
% 1.99/1.23  BG Simplification    : 0.01
% 1.99/1.23  Subsumption          : 0.03
% 1.99/1.23  Abstraction          : 0.01
% 1.99/1.23  MUC search           : 0.00
% 1.99/1.23  Cooper               : 0.00
% 1.99/1.23  Total                : 0.46
% 1.99/1.23  Index Insertion      : 0.00
% 1.99/1.23  Index Deletion       : 0.00
% 1.99/1.23  Index Matching       : 0.00
% 1.99/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
