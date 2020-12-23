%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:39 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   48 (  50 expanded)
%              Number of leaves         :   29 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   49 (  55 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_setfam_1(B,k1_tarski(A))
       => ! [C] :
            ( r2_hidden(C,B)
           => r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_setfam_1)).

tff(f_56,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_54,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_setfam_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_36,plain,(
    ~ r1_tarski('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_40,plain,(
    r1_setfam_1('#skF_3',k1_tarski('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_26,plain,(
    ! [A_38] : k3_tarski(k1_tarski(A_38)) = A_38 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_24,plain,(
    ! [A_37] : r1_tarski(A_37,k1_zfmisc_1(k3_tarski(A_37))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_38,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_148,plain,(
    ! [C_80,B_81,A_82] :
      ( r2_hidden(C_80,B_81)
      | ~ r2_hidden(C_80,A_82)
      | ~ r1_tarski(A_82,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_155,plain,(
    ! [B_83] :
      ( r2_hidden('#skF_4',B_83)
      | ~ r1_tarski('#skF_3',B_83) ) ),
    inference(resolution,[status(thm)],[c_38,c_148])).

tff(c_30,plain,(
    ! [A_41,B_42] :
      ( m1_subset_1(A_41,B_42)
      | ~ r2_hidden(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_163,plain,(
    ! [B_84] :
      ( m1_subset_1('#skF_4',B_84)
      | ~ r1_tarski('#skF_3',B_84) ) ),
    inference(resolution,[status(thm)],[c_155,c_30])).

tff(c_189,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k3_tarski('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_24,c_163])).

tff(c_32,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(A_43,B_44)
      | ~ m1_subset_1(A_43,k1_zfmisc_1(B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_193,plain,(
    r1_tarski('#skF_4',k3_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_189,c_32])).

tff(c_28,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(k3_tarski(A_39),k3_tarski(B_40))
      | ~ r1_setfam_1(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_117,plain,(
    ! [A_71,C_72,B_73] :
      ( r1_tarski(A_71,C_72)
      | ~ r1_tarski(B_73,C_72)
      | ~ r1_tarski(A_71,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_483,plain,(
    ! [A_130,B_131,A_132] :
      ( r1_tarski(A_130,k3_tarski(B_131))
      | ~ r1_tarski(A_130,k3_tarski(A_132))
      | ~ r1_setfam_1(A_132,B_131) ) ),
    inference(resolution,[status(thm)],[c_28,c_117])).

tff(c_519,plain,(
    ! [B_133] :
      ( r1_tarski('#skF_4',k3_tarski(B_133))
      | ~ r1_setfam_1('#skF_3',B_133) ) ),
    inference(resolution,[status(thm)],[c_193,c_483])).

tff(c_536,plain,(
    ! [A_134] :
      ( r1_tarski('#skF_4',A_134)
      | ~ r1_setfam_1('#skF_3',k1_tarski(A_134)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_519])).

tff(c_539,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_536])).

tff(c_543,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_539])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:47:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.38  
% 2.68/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.39  %$ r2_hidden > r1_tarski > r1_setfam_1 > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.68/1.39  
% 2.68/1.39  %Foreground sorts:
% 2.68/1.39  
% 2.68/1.39  
% 2.68/1.39  %Background operators:
% 2.68/1.39  
% 2.68/1.39  
% 2.68/1.39  %Foreground operators:
% 2.68/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.39  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.68/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.68/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.68/1.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.68/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.68/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.68/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.68/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.68/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.68/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.68/1.39  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.68/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.68/1.39  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.68/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.39  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.68/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.68/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.39  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.68/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.68/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.68/1.39  
% 2.68/1.40  tff(f_76, negated_conjecture, ~(![A, B]: (r1_setfam_1(B, k1_tarski(A)) => (![C]: (r2_hidden(C, B) => r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_setfam_1)).
% 2.68/1.40  tff(f_56, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 2.68/1.40  tff(f_54, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 2.68/1.40  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.68/1.40  tff(f_64, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.68/1.40  tff(f_68, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.68/1.40  tff(f_60, axiom, (![A, B]: (r1_setfam_1(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_setfam_1)).
% 2.68/1.40  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.68/1.40  tff(c_36, plain, (~r1_tarski('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.68/1.40  tff(c_40, plain, (r1_setfam_1('#skF_3', k1_tarski('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.68/1.40  tff(c_26, plain, (![A_38]: (k3_tarski(k1_tarski(A_38))=A_38)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.68/1.40  tff(c_24, plain, (![A_37]: (r1_tarski(A_37, k1_zfmisc_1(k3_tarski(A_37))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.68/1.40  tff(c_38, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.68/1.40  tff(c_148, plain, (![C_80, B_81, A_82]: (r2_hidden(C_80, B_81) | ~r2_hidden(C_80, A_82) | ~r1_tarski(A_82, B_81))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.68/1.40  tff(c_155, plain, (![B_83]: (r2_hidden('#skF_4', B_83) | ~r1_tarski('#skF_3', B_83))), inference(resolution, [status(thm)], [c_38, c_148])).
% 2.68/1.40  tff(c_30, plain, (![A_41, B_42]: (m1_subset_1(A_41, B_42) | ~r2_hidden(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.68/1.40  tff(c_163, plain, (![B_84]: (m1_subset_1('#skF_4', B_84) | ~r1_tarski('#skF_3', B_84))), inference(resolution, [status(thm)], [c_155, c_30])).
% 2.68/1.40  tff(c_189, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k3_tarski('#skF_3')))), inference(resolution, [status(thm)], [c_24, c_163])).
% 2.68/1.40  tff(c_32, plain, (![A_43, B_44]: (r1_tarski(A_43, B_44) | ~m1_subset_1(A_43, k1_zfmisc_1(B_44)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.68/1.40  tff(c_193, plain, (r1_tarski('#skF_4', k3_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_189, c_32])).
% 2.68/1.40  tff(c_28, plain, (![A_39, B_40]: (r1_tarski(k3_tarski(A_39), k3_tarski(B_40)) | ~r1_setfam_1(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.68/1.40  tff(c_117, plain, (![A_71, C_72, B_73]: (r1_tarski(A_71, C_72) | ~r1_tarski(B_73, C_72) | ~r1_tarski(A_71, B_73))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.68/1.40  tff(c_483, plain, (![A_130, B_131, A_132]: (r1_tarski(A_130, k3_tarski(B_131)) | ~r1_tarski(A_130, k3_tarski(A_132)) | ~r1_setfam_1(A_132, B_131))), inference(resolution, [status(thm)], [c_28, c_117])).
% 2.68/1.40  tff(c_519, plain, (![B_133]: (r1_tarski('#skF_4', k3_tarski(B_133)) | ~r1_setfam_1('#skF_3', B_133))), inference(resolution, [status(thm)], [c_193, c_483])).
% 2.68/1.40  tff(c_536, plain, (![A_134]: (r1_tarski('#skF_4', A_134) | ~r1_setfam_1('#skF_3', k1_tarski(A_134)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_519])).
% 2.68/1.40  tff(c_539, plain, (r1_tarski('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_536])).
% 2.68/1.40  tff(c_543, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_539])).
% 2.68/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.40  
% 2.68/1.40  Inference rules
% 2.68/1.40  ----------------------
% 2.68/1.40  #Ref     : 0
% 2.68/1.40  #Sup     : 127
% 2.68/1.40  #Fact    : 0
% 2.68/1.40  #Define  : 0
% 2.68/1.40  #Split   : 2
% 2.68/1.40  #Chain   : 0
% 2.68/1.40  #Close   : 0
% 2.68/1.40  
% 2.68/1.40  Ordering : KBO
% 2.68/1.40  
% 2.68/1.40  Simplification rules
% 2.68/1.40  ----------------------
% 2.68/1.40  #Subsume      : 26
% 2.68/1.40  #Demod        : 4
% 2.68/1.40  #Tautology    : 19
% 2.68/1.40  #SimpNegUnit  : 1
% 2.68/1.40  #BackRed      : 0
% 2.68/1.40  
% 2.68/1.40  #Partial instantiations: 0
% 2.68/1.40  #Strategies tried      : 1
% 2.68/1.40  
% 2.68/1.40  Timing (in seconds)
% 2.68/1.40  ----------------------
% 2.68/1.40  Preprocessing        : 0.30
% 2.68/1.40  Parsing              : 0.16
% 2.68/1.40  CNF conversion       : 0.02
% 2.68/1.40  Main loop            : 0.33
% 2.68/1.40  Inferencing          : 0.13
% 2.68/1.40  Reduction            : 0.09
% 2.68/1.40  Demodulation         : 0.06
% 2.68/1.40  BG Simplification    : 0.02
% 2.68/1.40  Subsumption          : 0.08
% 2.68/1.40  Abstraction          : 0.02
% 2.68/1.40  MUC search           : 0.00
% 2.68/1.40  Cooper               : 0.00
% 2.68/1.40  Total                : 0.66
% 2.68/1.40  Index Insertion      : 0.00
% 2.68/1.40  Index Deletion       : 0.00
% 2.68/1.40  Index Matching       : 0.00
% 2.68/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
