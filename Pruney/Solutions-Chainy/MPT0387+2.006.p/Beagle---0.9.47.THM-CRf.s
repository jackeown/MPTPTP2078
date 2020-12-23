%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:11 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   45 (  46 expanded)
%              Number of leaves         :   26 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :   53 (  55 expanded)
%              Number of equality atoms :   13 (  14 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_2 > #skF_3

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( r2_hidden(k1_xboole_0,A)
       => k1_setfam_1(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_setfam_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ~ ( r1_tarski(A,k2_zfmisc_1(B,C))
        & r2_hidden(D,A)
        & ! [E,F] :
            ~ ( r2_hidden(E,B)
              & r2_hidden(F,C)
              & D = k4_tarski(E,F) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_30,plain,(
    k1_setfam_1('#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_32,plain,(
    r2_hidden(k1_xboole_0,'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_28,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k1_setfam_1(B_22),A_21)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [B_20] : k2_zfmisc_1(k1_xboole_0,B_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_148,plain,(
    ! [A_47,B_48,C_49,D_50] :
      ( r2_hidden('#skF_3'(A_47,B_48,C_49,D_50),B_48)
      | ~ r2_hidden(D_50,A_47)
      | ~ r1_tarski(A_47,k2_zfmisc_1(B_48,C_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_14,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_75,plain,(
    ! [A_33,B_34,C_35] :
      ( ~ r1_xboole_0(A_33,B_34)
      | ~ r2_hidden(C_35,k3_xboole_0(A_33,B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_82,plain,(
    ! [A_11,C_35] :
      ( ~ r1_xboole_0(A_11,k1_xboole_0)
      | ~ r2_hidden(C_35,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_75])).

tff(c_85,plain,(
    ! [C_35] : ~ r2_hidden(C_35,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_82])).

tff(c_152,plain,(
    ! [D_50,A_47,C_49] :
      ( ~ r2_hidden(D_50,A_47)
      | ~ r1_tarski(A_47,k2_zfmisc_1(k1_xboole_0,C_49)) ) ),
    inference(resolution,[status(thm)],[c_148,c_85])).

tff(c_164,plain,(
    ! [D_51,A_52] :
      ( ~ r2_hidden(D_51,A_52)
      | ~ r1_tarski(A_52,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_152])).

tff(c_181,plain,(
    ! [A_53] :
      ( ~ r1_tarski(A_53,k1_xboole_0)
      | v1_xboole_0(A_53) ) ),
    inference(resolution,[status(thm)],[c_4,c_164])).

tff(c_187,plain,(
    ! [B_54] :
      ( v1_xboole_0(k1_setfam_1(B_54))
      | ~ r2_hidden(k1_xboole_0,B_54) ) ),
    inference(resolution,[status(thm)],[c_28,c_181])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_192,plain,(
    ! [B_55] :
      ( k1_setfam_1(B_55) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,B_55) ) ),
    inference(resolution,[status(thm)],[c_187,c_6])).

tff(c_195,plain,(
    k1_setfam_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_192])).

tff(c_199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_195])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:02:22 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.19  
% 1.84/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.19  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_2 > #skF_3
% 1.84/1.19  
% 1.84/1.19  %Foreground sorts:
% 1.84/1.19  
% 1.84/1.19  
% 1.84/1.19  %Background operators:
% 1.84/1.19  
% 1.84/1.19  
% 1.84/1.19  %Foreground operators:
% 1.84/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.84/1.19  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.84/1.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.84/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.84/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.84/1.19  tff('#skF_5', type, '#skF_5': $i).
% 1.84/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.84/1.19  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 1.84/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.84/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.19  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.84/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.84/1.19  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 1.84/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.84/1.19  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.84/1.19  
% 1.84/1.20  tff(f_81, negated_conjecture, ~(![A]: (r2_hidden(k1_xboole_0, A) => (k1_setfam_1(A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_setfam_1)).
% 1.84/1.20  tff(f_76, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 1.84/1.20  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.84/1.20  tff(f_72, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.84/1.20  tff(f_66, axiom, (![A, B, C, D]: ~((r1_tarski(A, k2_zfmisc_1(B, C)) & r2_hidden(D, A)) & (![E, F]: ~((r2_hidden(E, B) & r2_hidden(F, C)) & (D = k4_tarski(E, F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_zfmisc_1)).
% 1.84/1.20  tff(f_53, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.84/1.20  tff(f_51, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 1.84/1.20  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.84/1.20  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.84/1.20  tff(c_30, plain, (k1_setfam_1('#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.84/1.20  tff(c_32, plain, (r2_hidden(k1_xboole_0, '#skF_5')), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.84/1.20  tff(c_28, plain, (![B_22, A_21]: (r1_tarski(k1_setfam_1(B_22), A_21) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.84/1.20  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.84/1.20  tff(c_26, plain, (![B_20]: (k2_zfmisc_1(k1_xboole_0, B_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.84/1.20  tff(c_148, plain, (![A_47, B_48, C_49, D_50]: (r2_hidden('#skF_3'(A_47, B_48, C_49, D_50), B_48) | ~r2_hidden(D_50, A_47) | ~r1_tarski(A_47, k2_zfmisc_1(B_48, C_49)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.84/1.20  tff(c_14, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.84/1.20  tff(c_12, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.84/1.20  tff(c_75, plain, (![A_33, B_34, C_35]: (~r1_xboole_0(A_33, B_34) | ~r2_hidden(C_35, k3_xboole_0(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.84/1.20  tff(c_82, plain, (![A_11, C_35]: (~r1_xboole_0(A_11, k1_xboole_0) | ~r2_hidden(C_35, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_75])).
% 1.84/1.20  tff(c_85, plain, (![C_35]: (~r2_hidden(C_35, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_82])).
% 1.84/1.20  tff(c_152, plain, (![D_50, A_47, C_49]: (~r2_hidden(D_50, A_47) | ~r1_tarski(A_47, k2_zfmisc_1(k1_xboole_0, C_49)))), inference(resolution, [status(thm)], [c_148, c_85])).
% 1.84/1.20  tff(c_164, plain, (![D_51, A_52]: (~r2_hidden(D_51, A_52) | ~r1_tarski(A_52, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_152])).
% 1.84/1.20  tff(c_181, plain, (![A_53]: (~r1_tarski(A_53, k1_xboole_0) | v1_xboole_0(A_53))), inference(resolution, [status(thm)], [c_4, c_164])).
% 1.84/1.20  tff(c_187, plain, (![B_54]: (v1_xboole_0(k1_setfam_1(B_54)) | ~r2_hidden(k1_xboole_0, B_54))), inference(resolution, [status(thm)], [c_28, c_181])).
% 1.84/1.20  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.84/1.20  tff(c_192, plain, (![B_55]: (k1_setfam_1(B_55)=k1_xboole_0 | ~r2_hidden(k1_xboole_0, B_55))), inference(resolution, [status(thm)], [c_187, c_6])).
% 1.84/1.20  tff(c_195, plain, (k1_setfam_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_192])).
% 1.84/1.20  tff(c_199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_195])).
% 1.84/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.20  
% 1.84/1.20  Inference rules
% 1.84/1.20  ----------------------
% 1.84/1.20  #Ref     : 0
% 1.84/1.20  #Sup     : 34
% 1.84/1.20  #Fact    : 0
% 1.84/1.20  #Define  : 0
% 1.84/1.20  #Split   : 0
% 1.84/1.20  #Chain   : 0
% 1.84/1.20  #Close   : 0
% 1.84/1.20  
% 1.84/1.20  Ordering : KBO
% 1.84/1.20  
% 1.84/1.20  Simplification rules
% 1.84/1.20  ----------------------
% 1.84/1.20  #Subsume      : 0
% 1.84/1.20  #Demod        : 8
% 1.84/1.20  #Tautology    : 18
% 1.84/1.20  #SimpNegUnit  : 2
% 1.84/1.20  #BackRed      : 0
% 1.84/1.20  
% 1.84/1.20  #Partial instantiations: 0
% 1.84/1.20  #Strategies tried      : 1
% 1.84/1.20  
% 1.84/1.20  Timing (in seconds)
% 1.84/1.20  ----------------------
% 1.84/1.20  Preprocessing        : 0.26
% 1.84/1.20  Parsing              : 0.14
% 1.84/1.20  CNF conversion       : 0.02
% 1.84/1.20  Main loop            : 0.14
% 1.84/1.20  Inferencing          : 0.06
% 1.84/1.20  Reduction            : 0.04
% 1.84/1.20  Demodulation         : 0.03
% 1.84/1.20  BG Simplification    : 0.01
% 1.84/1.20  Subsumption          : 0.02
% 1.84/1.20  Abstraction          : 0.01
% 1.84/1.20  MUC search           : 0.00
% 1.84/1.20  Cooper               : 0.00
% 1.84/1.21  Total                : 0.43
% 1.84/1.21  Index Insertion      : 0.00
% 1.84/1.21  Index Deletion       : 0.00
% 1.84/1.21  Index Matching       : 0.00
% 1.84/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
