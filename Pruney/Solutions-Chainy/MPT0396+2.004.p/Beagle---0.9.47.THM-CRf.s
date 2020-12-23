%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:30 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   32 (  35 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :   48 (  57 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > #nlpp > k3_tarski > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_setfam_1(A,B)
       => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_setfam_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_20,plain,(
    r1_setfam_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_1'(A_6,B_7),A_6)
      | r1_tarski(k3_tarski(A_6),B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12,plain,(
    ! [A_9,B_10,C_19] :
      ( r2_hidden('#skF_3'(A_9,B_10,C_19),B_10)
      | ~ r2_hidden(C_19,A_9)
      | ~ r1_setfam_1(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_61,plain,(
    ! [C_44,A_45,B_46] :
      ( r1_tarski(C_44,'#skF_3'(A_45,B_46,C_44))
      | ~ r2_hidden(C_44,A_45)
      | ~ r1_setfam_1(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,k3_tarski(B_5))
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_33,plain,(
    ! [A_29,C_30,B_31] :
      ( r1_tarski(A_29,C_30)
      | ~ r1_tarski(B_31,C_30)
      | ~ r1_tarski(A_29,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    ! [A_29,B_5,A_4] :
      ( r1_tarski(A_29,k3_tarski(B_5))
      | ~ r1_tarski(A_29,A_4)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(resolution,[status(thm)],[c_4,c_33])).

tff(c_91,plain,(
    ! [C_57,B_58,A_59,B_60] :
      ( r1_tarski(C_57,k3_tarski(B_58))
      | ~ r2_hidden('#skF_3'(A_59,B_60,C_57),B_58)
      | ~ r2_hidden(C_57,A_59)
      | ~ r1_setfam_1(A_59,B_60) ) ),
    inference(resolution,[status(thm)],[c_61,c_36])).

tff(c_96,plain,(
    ! [C_61,B_62,A_63] :
      ( r1_tarski(C_61,k3_tarski(B_62))
      | ~ r2_hidden(C_61,A_63)
      | ~ r1_setfam_1(A_63,B_62) ) ),
    inference(resolution,[status(thm)],[c_12,c_91])).

tff(c_118,plain,(
    ! [A_70,B_71,B_72] :
      ( r1_tarski('#skF_1'(A_70,B_71),k3_tarski(B_72))
      | ~ r1_setfam_1(A_70,B_72)
      | r1_tarski(k3_tarski(A_70),B_71) ) ),
    inference(resolution,[status(thm)],[c_8,c_96])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( ~ r1_tarski('#skF_1'(A_6,B_7),B_7)
      | r1_tarski(k3_tarski(A_6),B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_129,plain,(
    ! [A_73,B_74] :
      ( ~ r1_setfam_1(A_73,B_74)
      | r1_tarski(k3_tarski(A_73),k3_tarski(B_74)) ) ),
    inference(resolution,[status(thm)],[c_118,c_6])).

tff(c_18,plain,(
    ~ r1_tarski(k3_tarski('#skF_4'),k3_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_136,plain,(
    ~ r1_setfam_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_129,c_18])).

tff(c_142,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_136])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:59:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.17  
% 1.90/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.18  %$ r2_hidden > r1_tarski > r1_setfam_1 > #nlpp > k3_tarski > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 1.90/1.18  
% 1.90/1.18  %Foreground sorts:
% 1.90/1.18  
% 1.90/1.18  
% 1.90/1.18  %Background operators:
% 1.90/1.18  
% 1.90/1.18  
% 1.90/1.18  %Foreground operators:
% 1.90/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.18  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.90/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.90/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.18  tff('#skF_5', type, '#skF_5': $i).
% 1.90/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.18  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.90/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.90/1.18  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.90/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.90/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.90/1.18  
% 1.90/1.19  tff(f_59, negated_conjecture, ~(![A, B]: (r1_setfam_1(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_setfam_1)).
% 1.90/1.19  tff(f_42, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 1.90/1.19  tff(f_54, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_setfam_1)).
% 1.90/1.19  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_zfmisc_1)).
% 1.90/1.19  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.90/1.19  tff(c_20, plain, (r1_setfam_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.90/1.19  tff(c_8, plain, (![A_6, B_7]: (r2_hidden('#skF_1'(A_6, B_7), A_6) | r1_tarski(k3_tarski(A_6), B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.90/1.19  tff(c_12, plain, (![A_9, B_10, C_19]: (r2_hidden('#skF_3'(A_9, B_10, C_19), B_10) | ~r2_hidden(C_19, A_9) | ~r1_setfam_1(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.90/1.19  tff(c_61, plain, (![C_44, A_45, B_46]: (r1_tarski(C_44, '#skF_3'(A_45, B_46, C_44)) | ~r2_hidden(C_44, A_45) | ~r1_setfam_1(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.90/1.19  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(A_4, k3_tarski(B_5)) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.90/1.19  tff(c_33, plain, (![A_29, C_30, B_31]: (r1_tarski(A_29, C_30) | ~r1_tarski(B_31, C_30) | ~r1_tarski(A_29, B_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.90/1.19  tff(c_36, plain, (![A_29, B_5, A_4]: (r1_tarski(A_29, k3_tarski(B_5)) | ~r1_tarski(A_29, A_4) | ~r2_hidden(A_4, B_5))), inference(resolution, [status(thm)], [c_4, c_33])).
% 1.90/1.19  tff(c_91, plain, (![C_57, B_58, A_59, B_60]: (r1_tarski(C_57, k3_tarski(B_58)) | ~r2_hidden('#skF_3'(A_59, B_60, C_57), B_58) | ~r2_hidden(C_57, A_59) | ~r1_setfam_1(A_59, B_60))), inference(resolution, [status(thm)], [c_61, c_36])).
% 1.90/1.19  tff(c_96, plain, (![C_61, B_62, A_63]: (r1_tarski(C_61, k3_tarski(B_62)) | ~r2_hidden(C_61, A_63) | ~r1_setfam_1(A_63, B_62))), inference(resolution, [status(thm)], [c_12, c_91])).
% 1.90/1.19  tff(c_118, plain, (![A_70, B_71, B_72]: (r1_tarski('#skF_1'(A_70, B_71), k3_tarski(B_72)) | ~r1_setfam_1(A_70, B_72) | r1_tarski(k3_tarski(A_70), B_71))), inference(resolution, [status(thm)], [c_8, c_96])).
% 1.90/1.19  tff(c_6, plain, (![A_6, B_7]: (~r1_tarski('#skF_1'(A_6, B_7), B_7) | r1_tarski(k3_tarski(A_6), B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.90/1.19  tff(c_129, plain, (![A_73, B_74]: (~r1_setfam_1(A_73, B_74) | r1_tarski(k3_tarski(A_73), k3_tarski(B_74)))), inference(resolution, [status(thm)], [c_118, c_6])).
% 1.90/1.19  tff(c_18, plain, (~r1_tarski(k3_tarski('#skF_4'), k3_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.90/1.19  tff(c_136, plain, (~r1_setfam_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_129, c_18])).
% 1.90/1.19  tff(c_142, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_136])).
% 1.90/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.19  
% 1.90/1.19  Inference rules
% 1.90/1.19  ----------------------
% 1.90/1.19  #Ref     : 0
% 1.90/1.19  #Sup     : 28
% 1.90/1.19  #Fact    : 0
% 1.90/1.19  #Define  : 0
% 1.90/1.19  #Split   : 0
% 1.90/1.19  #Chain   : 0
% 1.90/1.19  #Close   : 0
% 1.90/1.19  
% 1.90/1.19  Ordering : KBO
% 1.90/1.19  
% 1.90/1.19  Simplification rules
% 1.90/1.19  ----------------------
% 1.90/1.19  #Subsume      : 1
% 1.90/1.19  #Demod        : 1
% 1.90/1.19  #Tautology    : 1
% 1.90/1.19  #SimpNegUnit  : 0
% 1.90/1.19  #BackRed      : 0
% 1.90/1.19  
% 1.90/1.19  #Partial instantiations: 0
% 1.90/1.19  #Strategies tried      : 1
% 1.90/1.19  
% 1.90/1.19  Timing (in seconds)
% 1.90/1.19  ----------------------
% 1.90/1.19  Preprocessing        : 0.26
% 1.90/1.19  Parsing              : 0.14
% 1.90/1.19  CNF conversion       : 0.02
% 1.90/1.19  Main loop            : 0.17
% 1.90/1.19  Inferencing          : 0.08
% 1.90/1.19  Reduction            : 0.04
% 1.90/1.19  Demodulation         : 0.03
% 1.90/1.19  BG Simplification    : 0.01
% 1.90/1.19  Subsumption          : 0.04
% 1.90/1.19  Abstraction          : 0.01
% 1.90/1.19  MUC search           : 0.00
% 1.90/1.19  Cooper               : 0.00
% 1.90/1.19  Total                : 0.46
% 1.90/1.19  Index Insertion      : 0.00
% 1.90/1.19  Index Deletion       : 0.00
% 1.90/1.19  Index Matching       : 0.00
% 1.90/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
