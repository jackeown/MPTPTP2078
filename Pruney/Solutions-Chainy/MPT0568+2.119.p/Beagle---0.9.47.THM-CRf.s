%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:36 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   45 (  50 expanded)
%              Number of leaves         :   26 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   48 (  58 expanded)
%              Number of equality atoms :   14 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_51,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_73,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_10] : r1_xboole_0(A_10,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_97,plain,(
    ! [A_31,B_32,C_33] :
      ( ~ r1_xboole_0(A_31,B_32)
      | ~ r2_hidden(C_33,k3_xboole_0(A_31,B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_103,plain,(
    ! [A_34,B_35] :
      ( ~ r1_xboole_0(A_34,B_35)
      | k3_xboole_0(A_34,B_35) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_97])).

tff(c_108,plain,(
    ! [A_36] : k3_xboole_0(A_36,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_103])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_113,plain,(
    ! [A_36,C_5] :
      ( ~ r1_xboole_0(A_36,k1_xboole_0)
      | ~ r2_hidden(C_5,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_4])).

tff(c_118,plain,(
    ! [C_5] : ~ r2_hidden(C_5,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_113])).

tff(c_43,plain,(
    ! [B_24] : k2_zfmisc_1(k1_xboole_0,B_24) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_47,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_18])).

tff(c_28,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_231,plain,(
    ! [A_53,B_54,C_55] :
      ( r2_hidden('#skF_3'(A_53,B_54,C_55),k2_relat_1(C_55))
      | ~ r2_hidden(A_53,k10_relat_1(C_55,B_54))
      | ~ v1_relat_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_234,plain,(
    ! [A_53,B_54] :
      ( r2_hidden('#skF_3'(A_53,B_54,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_53,k10_relat_1(k1_xboole_0,B_54))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_231])).

tff(c_236,plain,(
    ! [A_53,B_54] :
      ( r2_hidden('#skF_3'(A_53,B_54,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_53,k10_relat_1(k1_xboole_0,B_54)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_234])).

tff(c_238,plain,(
    ! [A_56,B_57] : ~ r2_hidden(A_56,k10_relat_1(k1_xboole_0,B_57)) ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_236])).

tff(c_250,plain,(
    ! [B_57] : k10_relat_1(k1_xboole_0,B_57) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_238])).

tff(c_32,plain,(
    k10_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:13:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.34  
% 2.09/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.35  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.09/1.35  
% 2.09/1.35  %Foreground sorts:
% 2.09/1.35  
% 2.09/1.35  
% 2.09/1.35  %Background operators:
% 2.09/1.35  
% 2.09/1.35  
% 2.09/1.35  %Foreground operators:
% 2.09/1.35  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.09/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.09/1.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.09/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.09/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.09/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.35  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.09/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.09/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.09/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.09/1.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.09/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.09/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.09/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.09/1.35  
% 2.09/1.36  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.09/1.36  tff(f_51, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.09/1.36  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.09/1.36  tff(f_57, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.09/1.36  tff(f_59, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.09/1.36  tff(f_73, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.09/1.36  tff(f_70, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.09/1.36  tff(f_76, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 2.09/1.36  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.09/1.36  tff(c_10, plain, (![A_10]: (r1_xboole_0(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.09/1.36  tff(c_97, plain, (![A_31, B_32, C_33]: (~r1_xboole_0(A_31, B_32) | ~r2_hidden(C_33, k3_xboole_0(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.09/1.36  tff(c_103, plain, (![A_34, B_35]: (~r1_xboole_0(A_34, B_35) | k3_xboole_0(A_34, B_35)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_97])).
% 2.09/1.36  tff(c_108, plain, (![A_36]: (k3_xboole_0(A_36, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_103])).
% 2.09/1.36  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.09/1.36  tff(c_113, plain, (![A_36, C_5]: (~r1_xboole_0(A_36, k1_xboole_0) | ~r2_hidden(C_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_108, c_4])).
% 2.09/1.36  tff(c_118, plain, (![C_5]: (~r2_hidden(C_5, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_113])).
% 2.09/1.36  tff(c_43, plain, (![B_24]: (k2_zfmisc_1(k1_xboole_0, B_24)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.09/1.36  tff(c_18, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.09/1.36  tff(c_47, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_43, c_18])).
% 2.09/1.36  tff(c_28, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.09/1.36  tff(c_231, plain, (![A_53, B_54, C_55]: (r2_hidden('#skF_3'(A_53, B_54, C_55), k2_relat_1(C_55)) | ~r2_hidden(A_53, k10_relat_1(C_55, B_54)) | ~v1_relat_1(C_55))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.09/1.36  tff(c_234, plain, (![A_53, B_54]: (r2_hidden('#skF_3'(A_53, B_54, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_53, k10_relat_1(k1_xboole_0, B_54)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_231])).
% 2.09/1.36  tff(c_236, plain, (![A_53, B_54]: (r2_hidden('#skF_3'(A_53, B_54, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_53, k10_relat_1(k1_xboole_0, B_54)))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_234])).
% 2.09/1.36  tff(c_238, plain, (![A_56, B_57]: (~r2_hidden(A_56, k10_relat_1(k1_xboole_0, B_57)))), inference(negUnitSimplification, [status(thm)], [c_118, c_236])).
% 2.09/1.36  tff(c_250, plain, (![B_57]: (k10_relat_1(k1_xboole_0, B_57)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_238])).
% 2.09/1.36  tff(c_32, plain, (k10_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.09/1.36  tff(c_255, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_250, c_32])).
% 2.09/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.36  
% 2.09/1.36  Inference rules
% 2.09/1.36  ----------------------
% 2.09/1.36  #Ref     : 0
% 2.09/1.36  #Sup     : 53
% 2.09/1.36  #Fact    : 0
% 2.09/1.36  #Define  : 0
% 2.09/1.36  #Split   : 0
% 2.09/1.36  #Chain   : 0
% 2.09/1.36  #Close   : 0
% 2.09/1.36  
% 2.09/1.36  Ordering : KBO
% 2.09/1.36  
% 2.09/1.36  Simplification rules
% 2.09/1.36  ----------------------
% 2.09/1.36  #Subsume      : 4
% 2.09/1.36  #Demod        : 15
% 2.09/1.36  #Tautology    : 33
% 2.09/1.36  #SimpNegUnit  : 2
% 2.09/1.36  #BackRed      : 2
% 2.09/1.36  
% 2.09/1.36  #Partial instantiations: 0
% 2.09/1.36  #Strategies tried      : 1
% 2.09/1.36  
% 2.09/1.36  Timing (in seconds)
% 2.09/1.36  ----------------------
% 2.09/1.36  Preprocessing        : 0.34
% 2.09/1.36  Parsing              : 0.16
% 2.09/1.36  CNF conversion       : 0.03
% 2.09/1.36  Main loop            : 0.20
% 2.09/1.36  Inferencing          : 0.08
% 2.09/1.36  Reduction            : 0.06
% 2.09/1.36  Demodulation         : 0.04
% 2.09/1.36  BG Simplification    : 0.01
% 2.09/1.36  Subsumption          : 0.04
% 2.09/1.36  Abstraction          : 0.01
% 2.09/1.36  MUC search           : 0.00
% 2.09/1.36  Cooper               : 0.00
% 2.09/1.36  Total                : 0.58
% 2.09/1.36  Index Insertion      : 0.00
% 2.09/1.36  Index Deletion       : 0.00
% 2.09/1.36  Index Matching       : 0.00
% 2.09/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
