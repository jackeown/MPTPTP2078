%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:16 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   39 (  43 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   51 (  69 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_xboole_0 > #nlpp > k1_setfam_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r1_xboole_0(A,C) )
       => r1_xboole_0(k1_setfam_1(B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_setfam_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_36,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_46,plain,(
    ! [B_22,A_23] :
      ( r1_tarski(k1_setfam_1(B_22),A_23)
      | ~ r2_hidden(A_23,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_50,plain,(
    ! [B_22,A_23] :
      ( k3_xboole_0(k1_setfam_1(B_22),A_23) = k1_setfam_1(B_22)
      | ~ r2_hidden(A_23,B_22) ) ),
    inference(resolution,[status(thm)],[c_46,c_28])).

tff(c_64,plain,(
    ! [A_32,B_33] :
      ( r2_hidden('#skF_3'(A_32,B_33),B_33)
      | r1_xboole_0(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_179,plain,(
    ! [A_51,A_52,B_53] :
      ( r2_hidden('#skF_3'(A_51,k3_xboole_0(A_52,B_53)),B_53)
      | r1_xboole_0(A_51,k3_xboole_0(A_52,B_53)) ) ),
    inference(resolution,[status(thm)],[c_64,c_4])).

tff(c_26,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),A_9)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_34,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_75,plain,(
    ! [A_34,B_35,C_36] :
      ( ~ r1_xboole_0(A_34,B_35)
      | ~ r2_hidden(C_36,B_35)
      | ~ r2_hidden(C_36,A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_82,plain,(
    ! [C_37] :
      ( ~ r2_hidden(C_37,'#skF_6')
      | ~ r2_hidden(C_37,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_75])).

tff(c_92,plain,(
    ! [B_10] :
      ( ~ r2_hidden('#skF_3'('#skF_6',B_10),'#skF_4')
      | r1_xboole_0('#skF_6',B_10) ) ),
    inference(resolution,[status(thm)],[c_26,c_82])).

tff(c_207,plain,(
    ! [A_54] : r1_xboole_0('#skF_6',k3_xboole_0(A_54,'#skF_4')) ),
    inference(resolution,[status(thm)],[c_179,c_92])).

tff(c_20,plain,(
    ! [B_8,A_7] :
      ( r1_xboole_0(B_8,A_7)
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_218,plain,(
    ! [A_55] : r1_xboole_0(k3_xboole_0(A_55,'#skF_4'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_207,c_20])).

tff(c_237,plain,(
    ! [B_57] :
      ( r1_xboole_0(k1_setfam_1(B_57),'#skF_6')
      | ~ r2_hidden('#skF_4',B_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_218])).

tff(c_32,plain,(
    ~ r1_xboole_0(k1_setfam_1('#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_244,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_237,c_32])).

tff(c_250,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_244])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:37:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.28  
% 2.15/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.29  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_xboole_0 > #nlpp > k1_setfam_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 2.15/1.29  
% 2.15/1.29  %Foreground sorts:
% 2.15/1.29  
% 2.15/1.29  
% 2.15/1.29  %Background operators:
% 2.15/1.29  
% 2.15/1.29  
% 2.15/1.29  %Foreground operators:
% 2.15/1.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.15/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.29  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.15/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.15/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.15/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.15/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.15/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.15/1.29  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.15/1.29  
% 2.15/1.30  tff(f_71, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r1_xboole_0(A, C)) => r1_xboole_0(k1_setfam_1(B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_setfam_1)).
% 2.15/1.30  tff(f_64, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.15/1.30  tff(f_60, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.15/1.30  tff(f_56, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.15/1.30  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.15/1.30  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.15/1.30  tff(c_36, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.15/1.30  tff(c_46, plain, (![B_22, A_23]: (r1_tarski(k1_setfam_1(B_22), A_23) | ~r2_hidden(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.15/1.30  tff(c_28, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.15/1.30  tff(c_50, plain, (![B_22, A_23]: (k3_xboole_0(k1_setfam_1(B_22), A_23)=k1_setfam_1(B_22) | ~r2_hidden(A_23, B_22))), inference(resolution, [status(thm)], [c_46, c_28])).
% 2.15/1.30  tff(c_64, plain, (![A_32, B_33]: (r2_hidden('#skF_3'(A_32, B_33), B_33) | r1_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.15/1.30  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.15/1.30  tff(c_179, plain, (![A_51, A_52, B_53]: (r2_hidden('#skF_3'(A_51, k3_xboole_0(A_52, B_53)), B_53) | r1_xboole_0(A_51, k3_xboole_0(A_52, B_53)))), inference(resolution, [status(thm)], [c_64, c_4])).
% 2.15/1.30  tff(c_26, plain, (![A_9, B_10]: (r2_hidden('#skF_3'(A_9, B_10), A_9) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.15/1.30  tff(c_34, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.15/1.30  tff(c_75, plain, (![A_34, B_35, C_36]: (~r1_xboole_0(A_34, B_35) | ~r2_hidden(C_36, B_35) | ~r2_hidden(C_36, A_34))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.15/1.30  tff(c_82, plain, (![C_37]: (~r2_hidden(C_37, '#skF_6') | ~r2_hidden(C_37, '#skF_4'))), inference(resolution, [status(thm)], [c_34, c_75])).
% 2.15/1.30  tff(c_92, plain, (![B_10]: (~r2_hidden('#skF_3'('#skF_6', B_10), '#skF_4') | r1_xboole_0('#skF_6', B_10))), inference(resolution, [status(thm)], [c_26, c_82])).
% 2.15/1.30  tff(c_207, plain, (![A_54]: (r1_xboole_0('#skF_6', k3_xboole_0(A_54, '#skF_4')))), inference(resolution, [status(thm)], [c_179, c_92])).
% 2.15/1.30  tff(c_20, plain, (![B_8, A_7]: (r1_xboole_0(B_8, A_7) | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.15/1.30  tff(c_218, plain, (![A_55]: (r1_xboole_0(k3_xboole_0(A_55, '#skF_4'), '#skF_6'))), inference(resolution, [status(thm)], [c_207, c_20])).
% 2.15/1.30  tff(c_237, plain, (![B_57]: (r1_xboole_0(k1_setfam_1(B_57), '#skF_6') | ~r2_hidden('#skF_4', B_57))), inference(superposition, [status(thm), theory('equality')], [c_50, c_218])).
% 2.15/1.30  tff(c_32, plain, (~r1_xboole_0(k1_setfam_1('#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.15/1.30  tff(c_244, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_237, c_32])).
% 2.15/1.30  tff(c_250, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_244])).
% 2.15/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.30  
% 2.15/1.30  Inference rules
% 2.15/1.30  ----------------------
% 2.15/1.30  #Ref     : 0
% 2.15/1.30  #Sup     : 46
% 2.15/1.30  #Fact    : 0
% 2.15/1.30  #Define  : 0
% 2.15/1.30  #Split   : 0
% 2.15/1.30  #Chain   : 0
% 2.15/1.30  #Close   : 0
% 2.15/1.30  
% 2.15/1.30  Ordering : KBO
% 2.15/1.30  
% 2.15/1.30  Simplification rules
% 2.15/1.30  ----------------------
% 2.15/1.30  #Subsume      : 2
% 2.15/1.30  #Demod        : 5
% 2.15/1.30  #Tautology    : 10
% 2.15/1.30  #SimpNegUnit  : 0
% 2.15/1.30  #BackRed      : 0
% 2.15/1.30  
% 2.15/1.30  #Partial instantiations: 0
% 2.15/1.30  #Strategies tried      : 1
% 2.15/1.30  
% 2.15/1.30  Timing (in seconds)
% 2.15/1.30  ----------------------
% 2.15/1.30  Preprocessing        : 0.31
% 2.15/1.30  Parsing              : 0.17
% 2.15/1.30  CNF conversion       : 0.02
% 2.15/1.30  Main loop            : 0.19
% 2.15/1.30  Inferencing          : 0.08
% 2.15/1.30  Reduction            : 0.05
% 2.15/1.30  Demodulation         : 0.03
% 2.15/1.30  BG Simplification    : 0.02
% 2.15/1.30  Subsumption          : 0.04
% 2.15/1.30  Abstraction          : 0.01
% 2.15/1.30  MUC search           : 0.00
% 2.15/1.30  Cooper               : 0.00
% 2.15/1.30  Total                : 0.53
% 2.15/1.30  Index Insertion      : 0.00
% 2.15/1.30  Index Deletion       : 0.00
% 2.15/1.30  Index Matching       : 0.00
% 2.15/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
