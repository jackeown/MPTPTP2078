%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:53 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   49 (  60 expanded)
%              Number of leaves         :   28 (  34 expanded)
%              Depth                    :    6
%              Number of atoms          :   46 (  71 expanded)
%              Number of equality atoms :   11 (  16 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
       => ( k1_mcart_1(A) = B
          & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_53,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_51,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_34,plain,
    ( ~ r2_hidden(k2_mcart_1('#skF_1'),'#skF_3')
    | k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_66,plain,(
    k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_36,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_112,plain,(
    ! [A_62,B_63,C_64] :
      ( r2_hidden(k1_mcart_1(A_62),B_63)
      | ~ r2_hidden(A_62,k2_zfmisc_1(B_63,C_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_115,plain,(
    r2_hidden(k1_mcart_1('#skF_1'),k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_112])).

tff(c_26,plain,(
    ! [A_34] : k1_setfam_1(k1_tarski(A_34)) = A_34 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_67,plain,(
    ! [B_44,A_45] :
      ( r1_tarski(k1_setfam_1(B_44),A_45)
      | ~ r2_hidden(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_70,plain,(
    ! [A_34,A_45] :
      ( r1_tarski(A_34,A_45)
      | ~ r2_hidden(A_45,k1_tarski(A_34)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_67])).

tff(c_122,plain,(
    r1_tarski('#skF_2',k1_mcart_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_115,c_70])).

tff(c_24,plain,(
    ! [A_33] : k3_tarski(k1_tarski(A_33)) = A_33 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_71,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,k3_tarski(B_47))
      | ~ r2_hidden(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_74,plain,(
    ! [A_46,A_33] :
      ( r1_tarski(A_46,A_33)
      | ~ r2_hidden(A_46,k1_tarski(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_71])).

tff(c_123,plain,(
    r1_tarski(k1_mcart_1('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_115,c_74])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_130,plain,
    ( k1_mcart_1('#skF_1') = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_mcart_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_123,c_2])).

tff(c_133,plain,(
    k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_130])).

tff(c_135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_133])).

tff(c_136,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_1'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_174,plain,(
    ! [A_77,C_78,B_79] :
      ( r2_hidden(k2_mcart_1(A_77),C_78)
      | ~ r2_hidden(A_77,k2_zfmisc_1(B_79,C_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_176,plain,(
    r2_hidden(k2_mcart_1('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_174])).

tff(c_180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_176])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:33:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.27  
% 1.95/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.27  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1
% 1.95/1.27  
% 1.95/1.27  %Foreground sorts:
% 1.95/1.27  
% 1.95/1.27  
% 1.95/1.27  %Background operators:
% 1.95/1.27  
% 1.95/1.27  
% 1.95/1.27  %Foreground operators:
% 1.95/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.95/1.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.95/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.95/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.95/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.95/1.27  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.27  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.27  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.27  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.95/1.27  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.95/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.27  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.95/1.27  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.95/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.95/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.27  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.95/1.27  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.95/1.27  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.95/1.27  
% 1.95/1.28  tff(f_70, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_mcart_1)).
% 1.95/1.28  tff(f_63, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.95/1.28  tff(f_53, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 1.95/1.28  tff(f_57, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 1.95/1.28  tff(f_51, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 1.95/1.28  tff(f_49, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 1.95/1.28  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.95/1.28  tff(c_34, plain, (~r2_hidden(k2_mcart_1('#skF_1'), '#skF_3') | k1_mcart_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.95/1.28  tff(c_66, plain, (k1_mcart_1('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_34])).
% 1.95/1.28  tff(c_36, plain, (r2_hidden('#skF_1', k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.95/1.28  tff(c_112, plain, (![A_62, B_63, C_64]: (r2_hidden(k1_mcart_1(A_62), B_63) | ~r2_hidden(A_62, k2_zfmisc_1(B_63, C_64)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.95/1.28  tff(c_115, plain, (r2_hidden(k1_mcart_1('#skF_1'), k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_112])).
% 1.95/1.28  tff(c_26, plain, (![A_34]: (k1_setfam_1(k1_tarski(A_34))=A_34)), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.95/1.28  tff(c_67, plain, (![B_44, A_45]: (r1_tarski(k1_setfam_1(B_44), A_45) | ~r2_hidden(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.95/1.28  tff(c_70, plain, (![A_34, A_45]: (r1_tarski(A_34, A_45) | ~r2_hidden(A_45, k1_tarski(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_67])).
% 1.95/1.28  tff(c_122, plain, (r1_tarski('#skF_2', k1_mcart_1('#skF_1'))), inference(resolution, [status(thm)], [c_115, c_70])).
% 1.95/1.28  tff(c_24, plain, (![A_33]: (k3_tarski(k1_tarski(A_33))=A_33)), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.95/1.28  tff(c_71, plain, (![A_46, B_47]: (r1_tarski(A_46, k3_tarski(B_47)) | ~r2_hidden(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.95/1.28  tff(c_74, plain, (![A_46, A_33]: (r1_tarski(A_46, A_33) | ~r2_hidden(A_46, k1_tarski(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_71])).
% 1.95/1.28  tff(c_123, plain, (r1_tarski(k1_mcart_1('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_115, c_74])).
% 1.95/1.28  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.95/1.28  tff(c_130, plain, (k1_mcart_1('#skF_1')='#skF_2' | ~r1_tarski('#skF_2', k1_mcart_1('#skF_1'))), inference(resolution, [status(thm)], [c_123, c_2])).
% 1.95/1.28  tff(c_133, plain, (k1_mcart_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_122, c_130])).
% 1.95/1.28  tff(c_135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_133])).
% 1.95/1.28  tff(c_136, plain, (~r2_hidden(k2_mcart_1('#skF_1'), '#skF_3')), inference(splitRight, [status(thm)], [c_34])).
% 1.95/1.28  tff(c_174, plain, (![A_77, C_78, B_79]: (r2_hidden(k2_mcart_1(A_77), C_78) | ~r2_hidden(A_77, k2_zfmisc_1(B_79, C_78)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.95/1.28  tff(c_176, plain, (r2_hidden(k2_mcart_1('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_36, c_174])).
% 1.95/1.28  tff(c_180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_136, c_176])).
% 1.95/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.28  
% 1.95/1.28  Inference rules
% 1.95/1.28  ----------------------
% 1.95/1.28  #Ref     : 0
% 1.95/1.28  #Sup     : 31
% 1.95/1.28  #Fact    : 0
% 1.95/1.28  #Define  : 0
% 1.95/1.28  #Split   : 1
% 1.95/1.28  #Chain   : 0
% 1.95/1.28  #Close   : 0
% 1.95/1.28  
% 1.95/1.28  Ordering : KBO
% 1.95/1.28  
% 1.95/1.28  Simplification rules
% 1.95/1.28  ----------------------
% 1.95/1.28  #Subsume      : 0
% 1.95/1.28  #Demod        : 4
% 1.95/1.28  #Tautology    : 17
% 1.95/1.28  #SimpNegUnit  : 3
% 1.95/1.28  #BackRed      : 0
% 1.95/1.28  
% 1.95/1.28  #Partial instantiations: 0
% 1.95/1.28  #Strategies tried      : 1
% 1.95/1.28  
% 1.95/1.28  Timing (in seconds)
% 1.95/1.28  ----------------------
% 1.95/1.28  Preprocessing        : 0.33
% 1.95/1.28  Parsing              : 0.18
% 1.95/1.28  CNF conversion       : 0.02
% 1.95/1.28  Main loop            : 0.14
% 1.95/1.28  Inferencing          : 0.05
% 1.95/1.28  Reduction            : 0.04
% 1.95/1.28  Demodulation         : 0.03
% 1.95/1.28  BG Simplification    : 0.01
% 1.95/1.28  Subsumption          : 0.02
% 1.95/1.28  Abstraction          : 0.01
% 1.95/1.29  MUC search           : 0.00
% 1.95/1.29  Cooper               : 0.00
% 1.95/1.29  Total                : 0.50
% 1.95/1.29  Index Insertion      : 0.00
% 1.95/1.29  Index Deletion       : 0.00
% 1.95/1.29  Index Matching       : 0.00
% 1.95/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
