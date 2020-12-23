%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:23 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   40 (  45 expanded)
%              Number of leaves         :   24 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   43 (  50 expanded)
%              Number of equality atoms :   13 (  17 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_33,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_60,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_63,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_103,plain,(
    ! [A_29,B_30] :
      ( r2_hidden('#skF_1'(A_29,B_30),B_30)
      | r2_hidden('#skF_2'(A_29,B_30),A_29)
      | B_30 = A_29 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_70,plain,(
    ! [A_18,B_19] : ~ r2_hidden(A_18,k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_76,plain,(
    ! [A_4] : ~ r2_hidden(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_70])).

tff(c_117,plain,(
    ! [B_30] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_30),B_30)
      | k1_xboole_0 = B_30 ) ),
    inference(resolution,[status(thm)],[c_103,c_76])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_43,plain,(
    ! [A_15] :
      ( v1_relat_1(A_15)
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_47,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_43])).

tff(c_30,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_161,plain,(
    ! [A_37,B_38,C_39] :
      ( r2_hidden('#skF_3'(A_37,B_38,C_39),k2_relat_1(C_39))
      | ~ r2_hidden(A_37,k10_relat_1(C_39,B_38))
      | ~ v1_relat_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_164,plain,(
    ! [A_37,B_38] :
      ( r2_hidden('#skF_3'(A_37,B_38,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_37,k10_relat_1(k1_xboole_0,B_38))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_161])).

tff(c_166,plain,(
    ! [A_37,B_38] :
      ( r2_hidden('#skF_3'(A_37,B_38,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_37,k10_relat_1(k1_xboole_0,B_38)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_164])).

tff(c_168,plain,(
    ! [A_40,B_41] : ~ r2_hidden(A_40,k10_relat_1(k1_xboole_0,B_41)) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_166])).

tff(c_190,plain,(
    ! [B_41] : k10_relat_1(k1_xboole_0,B_41) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_117,c_168])).

tff(c_34,plain,(
    k10_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:40:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.30  
% 1.89/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.30  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.06/1.30  
% 2.06/1.30  %Foreground sorts:
% 2.06/1.30  
% 2.06/1.30  
% 2.06/1.30  %Background operators:
% 2.06/1.30  
% 2.06/1.30  
% 2.06/1.30  %Foreground operators:
% 2.06/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.06/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.06/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.30  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.06/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.06/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.06/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.30  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.06/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.06/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.06/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.06/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.06/1.30  
% 2.06/1.31  tff(f_33, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 2.06/1.31  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.06/1.31  tff(f_42, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.06/1.31  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.06/1.31  tff(f_46, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.06/1.31  tff(f_60, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.06/1.31  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 2.06/1.31  tff(f_63, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 2.06/1.31  tff(c_103, plain, (![A_29, B_30]: (r2_hidden('#skF_1'(A_29, B_30), B_30) | r2_hidden('#skF_2'(A_29, B_30), A_29) | B_30=A_29)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.06/1.31  tff(c_14, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.06/1.31  tff(c_70, plain, (![A_18, B_19]: (~r2_hidden(A_18, k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.06/1.31  tff(c_76, plain, (![A_4]: (~r2_hidden(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_70])).
% 2.06/1.31  tff(c_117, plain, (![B_30]: (r2_hidden('#skF_1'(k1_xboole_0, B_30), B_30) | k1_xboole_0=B_30)), inference(resolution, [status(thm)], [c_103, c_76])).
% 2.06/1.31  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.06/1.31  tff(c_43, plain, (![A_15]: (v1_relat_1(A_15) | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.06/1.31  tff(c_47, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_43])).
% 2.06/1.31  tff(c_30, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.06/1.31  tff(c_161, plain, (![A_37, B_38, C_39]: (r2_hidden('#skF_3'(A_37, B_38, C_39), k2_relat_1(C_39)) | ~r2_hidden(A_37, k10_relat_1(C_39, B_38)) | ~v1_relat_1(C_39))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.06/1.31  tff(c_164, plain, (![A_37, B_38]: (r2_hidden('#skF_3'(A_37, B_38, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_37, k10_relat_1(k1_xboole_0, B_38)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_161])).
% 2.06/1.31  tff(c_166, plain, (![A_37, B_38]: (r2_hidden('#skF_3'(A_37, B_38, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_37, k10_relat_1(k1_xboole_0, B_38)))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_164])).
% 2.06/1.31  tff(c_168, plain, (![A_40, B_41]: (~r2_hidden(A_40, k10_relat_1(k1_xboole_0, B_41)))), inference(negUnitSimplification, [status(thm)], [c_76, c_166])).
% 2.06/1.31  tff(c_190, plain, (![B_41]: (k10_relat_1(k1_xboole_0, B_41)=k1_xboole_0)), inference(resolution, [status(thm)], [c_117, c_168])).
% 2.06/1.31  tff(c_34, plain, (k10_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.06/1.31  tff(c_197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_190, c_34])).
% 2.06/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.31  
% 2.06/1.31  Inference rules
% 2.06/1.31  ----------------------
% 2.06/1.31  #Ref     : 0
% 2.06/1.31  #Sup     : 33
% 2.06/1.31  #Fact    : 0
% 2.06/1.31  #Define  : 0
% 2.06/1.31  #Split   : 0
% 2.06/1.31  #Chain   : 0
% 2.06/1.31  #Close   : 0
% 2.06/1.31  
% 2.06/1.31  Ordering : KBO
% 2.06/1.31  
% 2.06/1.31  Simplification rules
% 2.06/1.31  ----------------------
% 2.06/1.31  #Subsume      : 6
% 2.06/1.31  #Demod        : 3
% 2.06/1.31  #Tautology    : 15
% 2.06/1.31  #SimpNegUnit  : 1
% 2.06/1.31  #BackRed      : 2
% 2.06/1.31  
% 2.06/1.31  #Partial instantiations: 0
% 2.06/1.31  #Strategies tried      : 1
% 2.06/1.31  
% 2.06/1.31  Timing (in seconds)
% 2.06/1.31  ----------------------
% 2.06/1.32  Preprocessing        : 0.37
% 2.06/1.32  Parsing              : 0.22
% 2.06/1.32  CNF conversion       : 0.02
% 2.06/1.32  Main loop            : 0.18
% 2.06/1.32  Inferencing          : 0.08
% 2.06/1.32  Reduction            : 0.05
% 2.06/1.32  Demodulation         : 0.03
% 2.06/1.32  BG Simplification    : 0.02
% 2.06/1.32  Subsumption          : 0.03
% 2.06/1.32  Abstraction          : 0.01
% 2.06/1.32  MUC search           : 0.00
% 2.06/1.32  Cooper               : 0.00
% 2.06/1.32  Total                : 0.58
% 2.06/1.32  Index Insertion      : 0.00
% 2.06/1.32  Index Deletion       : 0.00
% 2.06/1.32  Index Matching       : 0.00
% 2.06/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
