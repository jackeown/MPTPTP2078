%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:33 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   40 (  45 expanded)
%              Number of leaves         :   24 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   41 (  48 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

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

tff(f_58,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_43,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

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

tff(f_61,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_91,plain,(
    ! [A_23,B_24] :
      ( r2_hidden('#skF_1'(A_23,B_24),B_24)
      | r2_hidden('#skF_2'(A_23,B_24),A_23)
      | B_24 = A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_72,plain,(
    ! [A_18,B_19] : ~ r2_hidden(A_18,k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_78,plain,(
    ! [A_4] : ~ r2_hidden(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_72])).

tff(c_98,plain,(
    ! [B_24] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_24),B_24)
      | k1_xboole_0 = B_24 ) ),
    inference(resolution,[status(thm)],[c_91,c_78])).

tff(c_32,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_43,plain,(
    ! [A_15] : v1_relat_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_45,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_43])).

tff(c_28,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_163,plain,(
    ! [A_37,B_38,C_39] :
      ( r2_hidden('#skF_3'(A_37,B_38,C_39),k2_relat_1(C_39))
      | ~ r2_hidden(A_37,k10_relat_1(C_39,B_38))
      | ~ v1_relat_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_166,plain,(
    ! [A_37,B_38] :
      ( r2_hidden('#skF_3'(A_37,B_38,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_37,k10_relat_1(k1_xboole_0,B_38))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_163])).

tff(c_168,plain,(
    ! [A_37,B_38] :
      ( r2_hidden('#skF_3'(A_37,B_38,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_37,k10_relat_1(k1_xboole_0,B_38)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_166])).

tff(c_170,plain,(
    ! [A_40,B_41] : ~ r2_hidden(A_40,k10_relat_1(k1_xboole_0,B_41)) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_168])).

tff(c_193,plain,(
    ! [B_41] : k10_relat_1(k1_xboole_0,B_41) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_98,c_170])).

tff(c_34,plain,(
    k10_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:57:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.25  
% 1.92/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.25  %$ r2_hidden > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 1.92/1.25  
% 1.92/1.25  %Foreground sorts:
% 1.92/1.25  
% 1.92/1.25  
% 1.92/1.25  %Background operators:
% 1.92/1.25  
% 1.92/1.25  
% 1.92/1.25  %Foreground operators:
% 1.92/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.92/1.25  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.92/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.92/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.92/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.25  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.92/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.92/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.92/1.25  tff('#skF_4', type, '#skF_4': $i).
% 1.92/1.25  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.92/1.25  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.92/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.92/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.92/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.92/1.25  
% 1.96/1.26  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 1.96/1.26  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.96/1.26  tff(f_41, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.96/1.26  tff(f_58, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 1.96/1.26  tff(f_43, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.96/1.26  tff(f_57, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.96/1.26  tff(f_54, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 1.96/1.26  tff(f_61, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 1.96/1.26  tff(c_91, plain, (![A_23, B_24]: (r2_hidden('#skF_1'(A_23, B_24), B_24) | r2_hidden('#skF_2'(A_23, B_24), A_23) | B_24=A_23)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.96/1.26  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.96/1.26  tff(c_72, plain, (![A_18, B_19]: (~r2_hidden(A_18, k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.96/1.26  tff(c_78, plain, (![A_4]: (~r2_hidden(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_72])).
% 1.96/1.26  tff(c_98, plain, (![B_24]: (r2_hidden('#skF_1'(k1_xboole_0, B_24), B_24) | k1_xboole_0=B_24)), inference(resolution, [status(thm)], [c_91, c_78])).
% 1.96/1.26  tff(c_32, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.96/1.26  tff(c_43, plain, (![A_15]: (v1_relat_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.96/1.26  tff(c_45, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_43])).
% 1.96/1.26  tff(c_28, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.96/1.26  tff(c_163, plain, (![A_37, B_38, C_39]: (r2_hidden('#skF_3'(A_37, B_38, C_39), k2_relat_1(C_39)) | ~r2_hidden(A_37, k10_relat_1(C_39, B_38)) | ~v1_relat_1(C_39))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.96/1.26  tff(c_166, plain, (![A_37, B_38]: (r2_hidden('#skF_3'(A_37, B_38, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_37, k10_relat_1(k1_xboole_0, B_38)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_163])).
% 1.96/1.26  tff(c_168, plain, (![A_37, B_38]: (r2_hidden('#skF_3'(A_37, B_38, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_37, k10_relat_1(k1_xboole_0, B_38)))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_166])).
% 1.96/1.26  tff(c_170, plain, (![A_40, B_41]: (~r2_hidden(A_40, k10_relat_1(k1_xboole_0, B_41)))), inference(negUnitSimplification, [status(thm)], [c_78, c_168])).
% 1.96/1.26  tff(c_193, plain, (![B_41]: (k10_relat_1(k1_xboole_0, B_41)=k1_xboole_0)), inference(resolution, [status(thm)], [c_98, c_170])).
% 1.96/1.26  tff(c_34, plain, (k10_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.96/1.26  tff(c_199, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_193, c_34])).
% 1.96/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.26  
% 1.96/1.26  Inference rules
% 1.96/1.26  ----------------------
% 1.96/1.26  #Ref     : 0
% 1.96/1.26  #Sup     : 35
% 1.96/1.26  #Fact    : 0
% 1.96/1.26  #Define  : 0
% 1.96/1.26  #Split   : 0
% 1.96/1.26  #Chain   : 0
% 1.96/1.26  #Close   : 0
% 1.96/1.26  
% 1.96/1.26  Ordering : KBO
% 1.96/1.26  
% 1.96/1.26  Simplification rules
% 1.96/1.26  ----------------------
% 1.96/1.26  #Subsume      : 6
% 1.96/1.26  #Demod        : 3
% 1.96/1.26  #Tautology    : 17
% 1.96/1.26  #SimpNegUnit  : 1
% 1.96/1.26  #BackRed      : 2
% 1.96/1.26  
% 1.96/1.26  #Partial instantiations: 0
% 1.96/1.26  #Strategies tried      : 1
% 1.96/1.26  
% 1.96/1.26  Timing (in seconds)
% 1.96/1.26  ----------------------
% 1.96/1.26  Preprocessing        : 0.28
% 1.96/1.26  Parsing              : 0.16
% 1.96/1.26  CNF conversion       : 0.02
% 1.96/1.26  Main loop            : 0.16
% 1.96/1.26  Inferencing          : 0.07
% 1.96/1.26  Reduction            : 0.04
% 1.96/1.26  Demodulation         : 0.03
% 1.96/1.26  BG Simplification    : 0.01
% 1.96/1.26  Subsumption          : 0.03
% 1.96/1.26  Abstraction          : 0.01
% 1.96/1.26  MUC search           : 0.00
% 1.96/1.26  Cooper               : 0.00
% 1.96/1.26  Total                : 0.47
% 1.96/1.26  Index Insertion      : 0.00
% 1.96/1.26  Index Deletion       : 0.00
% 1.96/1.26  Index Matching       : 0.00
% 1.96/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
