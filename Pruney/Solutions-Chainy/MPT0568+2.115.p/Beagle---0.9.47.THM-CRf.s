%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:35 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   39 (  39 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   39 (  39 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_51,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_73,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_44,plain,(
    ! [A_23,B_24] : v1_relat_1(k2_zfmisc_1(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_46,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_44])).

tff(c_152,plain,(
    ! [A_46,B_47,C_48] :
      ( r2_hidden(k4_tarski(A_46,'#skF_3'(A_46,B_47,C_48)),C_48)
      | ~ r2_hidden(A_46,k10_relat_1(C_48,B_47))
      | ~ v1_relat_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_77,plain,(
    ! [A_29,B_30,C_31] :
      ( ~ r1_xboole_0(A_29,B_30)
      | ~ r2_hidden(C_31,k3_xboole_0(A_29,B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_84,plain,(
    ! [A_8,C_31] :
      ( ~ r1_xboole_0(A_8,k1_xboole_0)
      | ~ r2_hidden(C_31,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_77])).

tff(c_87,plain,(
    ! [C_31] : ~ r2_hidden(C_31,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_84])).

tff(c_160,plain,(
    ! [A_46,B_47] :
      ( ~ r2_hidden(A_46,k10_relat_1(k1_xboole_0,B_47))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_152,c_87])).

tff(c_170,plain,(
    ! [A_49,B_50] : ~ r2_hidden(A_49,k10_relat_1(k1_xboole_0,B_50)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_160])).

tff(c_187,plain,(
    ! [B_50] : k10_relat_1(k1_xboole_0,B_50) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_170])).

tff(c_28,plain,(
    k10_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:51:46 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.15  
% 1.61/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.16  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.61/1.16  
% 1.61/1.16  %Foreground sorts:
% 1.61/1.16  
% 1.61/1.16  
% 1.61/1.16  %Background operators:
% 1.61/1.16  
% 1.61/1.16  
% 1.61/1.16  %Foreground operators:
% 1.61/1.16  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.61/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.61/1.16  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.61/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.61/1.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.61/1.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.61/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.16  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.61/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.61/1.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.61/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.61/1.16  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.61/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.61/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.61/1.16  
% 1.61/1.17  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.61/1.17  tff(f_57, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.61/1.17  tff(f_59, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.61/1.17  tff(f_70, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 1.61/1.17  tff(f_51, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.61/1.17  tff(f_49, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 1.61/1.17  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.61/1.17  tff(f_73, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 1.61/1.17  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.61/1.17  tff(c_14, plain, (![A_10]: (k2_zfmisc_1(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.61/1.17  tff(c_44, plain, (![A_23, B_24]: (v1_relat_1(k2_zfmisc_1(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.61/1.17  tff(c_46, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_44])).
% 1.61/1.17  tff(c_152, plain, (![A_46, B_47, C_48]: (r2_hidden(k4_tarski(A_46, '#skF_3'(A_46, B_47, C_48)), C_48) | ~r2_hidden(A_46, k10_relat_1(C_48, B_47)) | ~v1_relat_1(C_48))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.61/1.17  tff(c_10, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.61/1.17  tff(c_8, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.61/1.17  tff(c_77, plain, (![A_29, B_30, C_31]: (~r1_xboole_0(A_29, B_30) | ~r2_hidden(C_31, k3_xboole_0(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.61/1.17  tff(c_84, plain, (![A_8, C_31]: (~r1_xboole_0(A_8, k1_xboole_0) | ~r2_hidden(C_31, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_77])).
% 1.61/1.17  tff(c_87, plain, (![C_31]: (~r2_hidden(C_31, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_84])).
% 1.61/1.17  tff(c_160, plain, (![A_46, B_47]: (~r2_hidden(A_46, k10_relat_1(k1_xboole_0, B_47)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_152, c_87])).
% 1.61/1.17  tff(c_170, plain, (![A_49, B_50]: (~r2_hidden(A_49, k10_relat_1(k1_xboole_0, B_50)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_160])).
% 1.61/1.17  tff(c_187, plain, (![B_50]: (k10_relat_1(k1_xboole_0, B_50)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_170])).
% 1.61/1.17  tff(c_28, plain, (k10_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.61/1.17  tff(c_192, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_187, c_28])).
% 1.61/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.17  
% 1.61/1.17  Inference rules
% 1.61/1.17  ----------------------
% 1.61/1.17  #Ref     : 0
% 1.61/1.17  #Sup     : 34
% 1.61/1.17  #Fact    : 0
% 1.61/1.17  #Define  : 0
% 1.61/1.17  #Split   : 0
% 1.61/1.17  #Chain   : 0
% 1.61/1.17  #Close   : 0
% 1.61/1.17  
% 1.61/1.17  Ordering : KBO
% 1.61/1.17  
% 1.61/1.17  Simplification rules
% 1.61/1.17  ----------------------
% 1.61/1.17  #Subsume      : 3
% 1.61/1.17  #Demod        : 9
% 1.61/1.17  #Tautology    : 18
% 1.61/1.17  #SimpNegUnit  : 1
% 1.61/1.17  #BackRed      : 2
% 1.61/1.17  
% 1.61/1.17  #Partial instantiations: 0
% 1.61/1.17  #Strategies tried      : 1
% 1.61/1.17  
% 1.61/1.17  Timing (in seconds)
% 1.61/1.17  ----------------------
% 1.61/1.17  Preprocessing        : 0.28
% 1.61/1.17  Parsing              : 0.15
% 1.61/1.17  CNF conversion       : 0.02
% 1.61/1.17  Main loop            : 0.15
% 1.61/1.17  Inferencing          : 0.06
% 1.61/1.17  Reduction            : 0.04
% 1.61/1.17  Demodulation         : 0.03
% 1.61/1.17  BG Simplification    : 0.01
% 1.61/1.17  Subsumption          : 0.02
% 1.61/1.17  Abstraction          : 0.01
% 1.61/1.17  MUC search           : 0.00
% 1.61/1.17  Cooper               : 0.00
% 1.61/1.17  Total                : 0.45
% 1.61/1.17  Index Insertion      : 0.00
% 1.61/1.17  Index Deletion       : 0.00
% 1.61/1.17  Index Matching       : 0.00
% 1.61/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
