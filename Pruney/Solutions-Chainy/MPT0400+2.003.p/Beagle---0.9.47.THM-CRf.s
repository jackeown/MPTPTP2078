%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:38 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   32 (  40 expanded)
%              Number of leaves         :   14 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :   59 (  88 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > #nlpp > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_setfam_1(A,B)
          & r1_setfam_1(B,C) )
       => r1_setfam_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_setfam_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_16,plain,(
    r1_setfam_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r2_hidden('#skF_1'(A_4,B_5),A_4)
      | r1_setfam_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    r1_setfam_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6,plain,(
    ! [A_4,B_5,C_14] :
      ( r2_hidden('#skF_2'(A_4,B_5,C_14),B_5)
      | ~ r2_hidden(C_14,A_4)
      | ~ r1_setfam_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [C_14,A_4,B_5] :
      ( r1_tarski(C_14,'#skF_2'(A_4,B_5,C_14))
      | ~ r2_hidden(C_14,A_4)
      | ~ r1_setfam_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_21,plain,(
    ! [C_27,A_28,B_29] :
      ( r1_tarski(C_27,'#skF_2'(A_28,B_29,C_27))
      | ~ r2_hidden(C_27,A_28)
      | ~ r1_setfam_1(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ! [A_30,A_31,B_32,C_33] :
      ( r1_tarski(A_30,'#skF_2'(A_31,B_32,C_33))
      | ~ r1_tarski(A_30,C_33)
      | ~ r2_hidden(C_33,A_31)
      | ~ r1_setfam_1(A_31,B_32) ) ),
    inference(resolution,[status(thm)],[c_21,c_2])).

tff(c_8,plain,(
    ! [A_4,B_5,D_13] :
      ( ~ r1_tarski('#skF_1'(A_4,B_5),D_13)
      | ~ r2_hidden(D_13,B_5)
      | r1_setfam_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_57,plain,(
    ! [A_50,A_47,B_46,C_49,B_48] :
      ( ~ r2_hidden('#skF_2'(A_47,B_46,C_49),B_48)
      | r1_setfam_1(A_50,B_48)
      | ~ r1_tarski('#skF_1'(A_50,B_48),C_49)
      | ~ r2_hidden(C_49,A_47)
      | ~ r1_setfam_1(A_47,B_46) ) ),
    inference(resolution,[status(thm)],[c_30,c_8])).

tff(c_61,plain,(
    ! [A_51,B_52,C_53,A_54] :
      ( r1_setfam_1(A_51,B_52)
      | ~ r1_tarski('#skF_1'(A_51,B_52),C_53)
      | ~ r2_hidden(C_53,A_54)
      | ~ r1_setfam_1(A_54,B_52) ) ),
    inference(resolution,[status(thm)],[c_6,c_57])).

tff(c_70,plain,(
    ! [A_57,B_56,A_59,B_58,A_55] :
      ( r1_setfam_1(A_55,B_56)
      | ~ r2_hidden('#skF_2'(A_59,B_58,'#skF_1'(A_55,B_56)),A_57)
      | ~ r1_setfam_1(A_57,B_56)
      | ~ r2_hidden('#skF_1'(A_55,B_56),A_59)
      | ~ r1_setfam_1(A_59,B_58) ) ),
    inference(resolution,[status(thm)],[c_4,c_61])).

tff(c_85,plain,(
    ! [A_66,B_67,B_68,A_69] :
      ( r1_setfam_1(A_66,B_67)
      | ~ r1_setfam_1(B_68,B_67)
      | ~ r2_hidden('#skF_1'(A_66,B_67),A_69)
      | ~ r1_setfam_1(A_69,B_68) ) ),
    inference(resolution,[status(thm)],[c_6,c_70])).

tff(c_92,plain,(
    ! [A_70,A_71] :
      ( r1_setfam_1(A_70,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_70,'#skF_5'),A_71)
      | ~ r1_setfam_1(A_71,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_14,c_85])).

tff(c_98,plain,(
    ! [A_72] :
      ( ~ r1_setfam_1(A_72,'#skF_4')
      | r1_setfam_1(A_72,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_10,c_92])).

tff(c_12,plain,(
    ~ r1_setfam_1('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_103,plain,(
    ~ r1_setfam_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_98,c_12])).

tff(c_108,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_103])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:55:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.18  
% 1.84/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.18  %$ r2_hidden > r1_tarski > r1_setfam_1 > #nlpp > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 1.84/1.18  
% 1.84/1.18  %Foreground sorts:
% 1.84/1.18  
% 1.84/1.18  
% 1.84/1.18  %Background operators:
% 1.84/1.18  
% 1.84/1.18  
% 1.84/1.18  %Foreground operators:
% 1.84/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.18  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.84/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.84/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.84/1.18  tff('#skF_5', type, '#skF_5': $i).
% 1.84/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.84/1.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.84/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.84/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.84/1.18  
% 1.84/1.20  tff(f_50, negated_conjecture, ~(![A, B, C]: ((r1_setfam_1(A, B) & r1_setfam_1(B, C)) => r1_setfam_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_setfam_1)).
% 1.84/1.20  tff(f_43, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_setfam_1)).
% 1.84/1.20  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.84/1.20  tff(c_16, plain, (r1_setfam_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.84/1.20  tff(c_10, plain, (![A_4, B_5]: (r2_hidden('#skF_1'(A_4, B_5), A_4) | r1_setfam_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.84/1.20  tff(c_14, plain, (r1_setfam_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.84/1.20  tff(c_6, plain, (![A_4, B_5, C_14]: (r2_hidden('#skF_2'(A_4, B_5, C_14), B_5) | ~r2_hidden(C_14, A_4) | ~r1_setfam_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.84/1.20  tff(c_4, plain, (![C_14, A_4, B_5]: (r1_tarski(C_14, '#skF_2'(A_4, B_5, C_14)) | ~r2_hidden(C_14, A_4) | ~r1_setfam_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.84/1.20  tff(c_21, plain, (![C_27, A_28, B_29]: (r1_tarski(C_27, '#skF_2'(A_28, B_29, C_27)) | ~r2_hidden(C_27, A_28) | ~r1_setfam_1(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.84/1.20  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.84/1.20  tff(c_30, plain, (![A_30, A_31, B_32, C_33]: (r1_tarski(A_30, '#skF_2'(A_31, B_32, C_33)) | ~r1_tarski(A_30, C_33) | ~r2_hidden(C_33, A_31) | ~r1_setfam_1(A_31, B_32))), inference(resolution, [status(thm)], [c_21, c_2])).
% 1.84/1.20  tff(c_8, plain, (![A_4, B_5, D_13]: (~r1_tarski('#skF_1'(A_4, B_5), D_13) | ~r2_hidden(D_13, B_5) | r1_setfam_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.84/1.20  tff(c_57, plain, (![A_50, A_47, B_46, C_49, B_48]: (~r2_hidden('#skF_2'(A_47, B_46, C_49), B_48) | r1_setfam_1(A_50, B_48) | ~r1_tarski('#skF_1'(A_50, B_48), C_49) | ~r2_hidden(C_49, A_47) | ~r1_setfam_1(A_47, B_46))), inference(resolution, [status(thm)], [c_30, c_8])).
% 1.84/1.20  tff(c_61, plain, (![A_51, B_52, C_53, A_54]: (r1_setfam_1(A_51, B_52) | ~r1_tarski('#skF_1'(A_51, B_52), C_53) | ~r2_hidden(C_53, A_54) | ~r1_setfam_1(A_54, B_52))), inference(resolution, [status(thm)], [c_6, c_57])).
% 1.84/1.20  tff(c_70, plain, (![A_57, B_56, A_59, B_58, A_55]: (r1_setfam_1(A_55, B_56) | ~r2_hidden('#skF_2'(A_59, B_58, '#skF_1'(A_55, B_56)), A_57) | ~r1_setfam_1(A_57, B_56) | ~r2_hidden('#skF_1'(A_55, B_56), A_59) | ~r1_setfam_1(A_59, B_58))), inference(resolution, [status(thm)], [c_4, c_61])).
% 1.84/1.20  tff(c_85, plain, (![A_66, B_67, B_68, A_69]: (r1_setfam_1(A_66, B_67) | ~r1_setfam_1(B_68, B_67) | ~r2_hidden('#skF_1'(A_66, B_67), A_69) | ~r1_setfam_1(A_69, B_68))), inference(resolution, [status(thm)], [c_6, c_70])).
% 1.84/1.20  tff(c_92, plain, (![A_70, A_71]: (r1_setfam_1(A_70, '#skF_5') | ~r2_hidden('#skF_1'(A_70, '#skF_5'), A_71) | ~r1_setfam_1(A_71, '#skF_4'))), inference(resolution, [status(thm)], [c_14, c_85])).
% 1.84/1.20  tff(c_98, plain, (![A_72]: (~r1_setfam_1(A_72, '#skF_4') | r1_setfam_1(A_72, '#skF_5'))), inference(resolution, [status(thm)], [c_10, c_92])).
% 1.84/1.20  tff(c_12, plain, (~r1_setfam_1('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.84/1.20  tff(c_103, plain, (~r1_setfam_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_98, c_12])).
% 1.84/1.20  tff(c_108, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_103])).
% 1.84/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.20  
% 1.84/1.20  Inference rules
% 1.84/1.20  ----------------------
% 1.84/1.20  #Ref     : 0
% 1.84/1.20  #Sup     : 19
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
% 1.84/1.20  #Demod        : 1
% 1.84/1.20  #Tautology    : 1
% 1.84/1.20  #SimpNegUnit  : 0
% 1.84/1.20  #BackRed      : 0
% 1.84/1.20  
% 1.84/1.20  #Partial instantiations: 0
% 1.84/1.20  #Strategies tried      : 1
% 1.84/1.20  
% 1.84/1.20  Timing (in seconds)
% 1.84/1.20  ----------------------
% 1.84/1.20  Preprocessing        : 0.25
% 1.84/1.20  Parsing              : 0.14
% 1.84/1.20  CNF conversion       : 0.02
% 1.84/1.20  Main loop            : 0.16
% 1.84/1.20  Inferencing          : 0.07
% 1.84/1.20  Reduction            : 0.03
% 1.84/1.20  Demodulation         : 0.02
% 1.84/1.20  BG Simplification    : 0.01
% 1.84/1.20  Subsumption          : 0.04
% 1.84/1.20  Abstraction          : 0.01
% 1.84/1.20  MUC search           : 0.00
% 1.84/1.20  Cooper               : 0.00
% 1.84/1.20  Total                : 0.43
% 1.84/1.20  Index Insertion      : 0.00
% 1.84/1.20  Index Deletion       : 0.00
% 1.84/1.20  Index Matching       : 0.00
% 1.84/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
