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
% DateTime   : Thu Dec  3 09:57:29 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   40 (  49 expanded)
%              Number of leaves         :   18 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :   51 (  70 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => r1_setfam_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_setfam_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_24,plain,(
    ~ r1_setfam_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_1'(A_10,B_11),A_10)
      | r1_setfam_1(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_36,plain,(
    ! [A_26,B_27] :
      ( k2_xboole_0(A_26,B_27) = B_27
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_44,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_26,c_36])).

tff(c_58,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(k1_tarski(A_29),B_30)
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_65,plain,(
    ! [A_29,B_30] :
      ( k2_xboole_0(k1_tarski(A_29),B_30) = B_30
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(resolution,[status(thm)],[c_58,c_10])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_82,plain,(
    ! [A_35,C_36,B_37] :
      ( r1_tarski(A_35,C_36)
      | ~ r1_tarski(k2_xboole_0(A_35,B_37),C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_94,plain,(
    ! [A_38,B_39] : r1_tarski(A_38,k2_xboole_0(A_38,B_39)) ),
    inference(resolution,[status(thm)],[c_6,c_82])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_145,plain,(
    ! [A_46,B_47,B_48] : r1_tarski(A_46,k2_xboole_0(k2_xboole_0(A_46,B_47),B_48)) ),
    inference(resolution,[status(thm)],[c_94,c_8])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r2_hidden(A_8,B_9)
      | ~ r1_tarski(k1_tarski(A_8),B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_349,plain,(
    ! [A_61,B_62,B_63] : r2_hidden(A_61,k2_xboole_0(k2_xboole_0(k1_tarski(A_61),B_62),B_63)) ),
    inference(resolution,[status(thm)],[c_145,c_12])).

tff(c_386,plain,(
    ! [A_65,B_66,B_67] :
      ( r2_hidden(A_65,k2_xboole_0(B_66,B_67))
      | ~ r2_hidden(A_65,B_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_349])).

tff(c_404,plain,(
    ! [A_68] :
      ( r2_hidden(A_68,'#skF_4')
      | ~ r2_hidden(A_68,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_386])).

tff(c_526,plain,(
    ! [B_79] :
      ( r2_hidden('#skF_1'('#skF_3',B_79),'#skF_4')
      | r1_setfam_1('#skF_3',B_79) ) ),
    inference(resolution,[status(thm)],[c_22,c_404])).

tff(c_120,plain,(
    ! [A_40,B_41,D_42] :
      ( ~ r1_tarski('#skF_1'(A_40,B_41),D_42)
      | ~ r2_hidden(D_42,B_41)
      | r1_setfam_1(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_130,plain,(
    ! [A_40,B_41] :
      ( ~ r2_hidden('#skF_1'(A_40,B_41),B_41)
      | r1_setfam_1(A_40,B_41) ) ),
    inference(resolution,[status(thm)],[c_6,c_120])).

tff(c_530,plain,(
    r1_setfam_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_526,c_130])).

tff(c_534,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_24,c_530])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:38:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.29  
% 2.21/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.29  %$ r2_hidden > r1_tarski > r1_setfam_1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 2.21/1.29  
% 2.21/1.29  %Foreground sorts:
% 2.21/1.29  
% 2.21/1.29  
% 2.21/1.29  %Background operators:
% 2.21/1.29  
% 2.21/1.29  
% 2.21/1.29  %Foreground operators:
% 2.21/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.29  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.21/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.21/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.21/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.21/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.21/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.21/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.21/1.29  
% 2.21/1.30  tff(f_60, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => r1_setfam_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_setfam_1)).
% 2.21/1.30  tff(f_55, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 2.21/1.30  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.21/1.30  tff(f_43, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.21/1.30  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.21/1.30  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.21/1.30  tff(c_24, plain, (~r1_setfam_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.21/1.30  tff(c_22, plain, (![A_10, B_11]: (r2_hidden('#skF_1'(A_10, B_11), A_10) | r1_setfam_1(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.21/1.30  tff(c_26, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.21/1.30  tff(c_36, plain, (![A_26, B_27]: (k2_xboole_0(A_26, B_27)=B_27 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.21/1.30  tff(c_44, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_26, c_36])).
% 2.21/1.30  tff(c_58, plain, (![A_29, B_30]: (r1_tarski(k1_tarski(A_29), B_30) | ~r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.21/1.30  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.21/1.30  tff(c_65, plain, (![A_29, B_30]: (k2_xboole_0(k1_tarski(A_29), B_30)=B_30 | ~r2_hidden(A_29, B_30))), inference(resolution, [status(thm)], [c_58, c_10])).
% 2.21/1.30  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.21/1.30  tff(c_82, plain, (![A_35, C_36, B_37]: (r1_tarski(A_35, C_36) | ~r1_tarski(k2_xboole_0(A_35, B_37), C_36))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.21/1.30  tff(c_94, plain, (![A_38, B_39]: (r1_tarski(A_38, k2_xboole_0(A_38, B_39)))), inference(resolution, [status(thm)], [c_6, c_82])).
% 2.21/1.30  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.21/1.30  tff(c_145, plain, (![A_46, B_47, B_48]: (r1_tarski(A_46, k2_xboole_0(k2_xboole_0(A_46, B_47), B_48)))), inference(resolution, [status(thm)], [c_94, c_8])).
% 2.21/1.30  tff(c_12, plain, (![A_8, B_9]: (r2_hidden(A_8, B_9) | ~r1_tarski(k1_tarski(A_8), B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.21/1.30  tff(c_349, plain, (![A_61, B_62, B_63]: (r2_hidden(A_61, k2_xboole_0(k2_xboole_0(k1_tarski(A_61), B_62), B_63)))), inference(resolution, [status(thm)], [c_145, c_12])).
% 2.21/1.30  tff(c_386, plain, (![A_65, B_66, B_67]: (r2_hidden(A_65, k2_xboole_0(B_66, B_67)) | ~r2_hidden(A_65, B_66))), inference(superposition, [status(thm), theory('equality')], [c_65, c_349])).
% 2.21/1.30  tff(c_404, plain, (![A_68]: (r2_hidden(A_68, '#skF_4') | ~r2_hidden(A_68, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_386])).
% 2.21/1.30  tff(c_526, plain, (![B_79]: (r2_hidden('#skF_1'('#skF_3', B_79), '#skF_4') | r1_setfam_1('#skF_3', B_79))), inference(resolution, [status(thm)], [c_22, c_404])).
% 2.21/1.30  tff(c_120, plain, (![A_40, B_41, D_42]: (~r1_tarski('#skF_1'(A_40, B_41), D_42) | ~r2_hidden(D_42, B_41) | r1_setfam_1(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.21/1.30  tff(c_130, plain, (![A_40, B_41]: (~r2_hidden('#skF_1'(A_40, B_41), B_41) | r1_setfam_1(A_40, B_41))), inference(resolution, [status(thm)], [c_6, c_120])).
% 2.21/1.30  tff(c_530, plain, (r1_setfam_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_526, c_130])).
% 2.21/1.30  tff(c_534, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_24, c_530])).
% 2.21/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.30  
% 2.21/1.30  Inference rules
% 2.21/1.30  ----------------------
% 2.21/1.30  #Ref     : 0
% 2.21/1.30  #Sup     : 110
% 2.21/1.30  #Fact    : 0
% 2.21/1.30  #Define  : 0
% 2.21/1.30  #Split   : 1
% 2.21/1.30  #Chain   : 0
% 2.21/1.30  #Close   : 0
% 2.21/1.30  
% 2.21/1.30  Ordering : KBO
% 2.21/1.30  
% 2.21/1.30  Simplification rules
% 2.21/1.30  ----------------------
% 2.21/1.30  #Subsume      : 9
% 2.21/1.30  #Demod        : 44
% 2.21/1.30  #Tautology    : 52
% 2.21/1.30  #SimpNegUnit  : 1
% 2.21/1.30  #BackRed      : 0
% 2.21/1.30  
% 2.21/1.30  #Partial instantiations: 0
% 2.21/1.30  #Strategies tried      : 1
% 2.21/1.30  
% 2.21/1.30  Timing (in seconds)
% 2.21/1.30  ----------------------
% 2.21/1.30  Preprocessing        : 0.26
% 2.21/1.31  Parsing              : 0.15
% 2.21/1.31  CNF conversion       : 0.02
% 2.21/1.31  Main loop            : 0.26
% 2.21/1.31  Inferencing          : 0.11
% 2.21/1.31  Reduction            : 0.07
% 2.21/1.31  Demodulation         : 0.05
% 2.21/1.31  BG Simplification    : 0.01
% 2.21/1.31  Subsumption          : 0.06
% 2.21/1.31  Abstraction          : 0.01
% 2.21/1.31  MUC search           : 0.00
% 2.21/1.31  Cooper               : 0.00
% 2.21/1.31  Total                : 0.55
% 2.21/1.31  Index Insertion      : 0.00
% 2.21/1.31  Index Deletion       : 0.00
% 2.21/1.31  Index Matching       : 0.00
% 2.21/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
