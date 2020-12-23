%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:28 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   32 (  37 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :   38 (  52 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_58,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_46,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_31,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

tff(c_12,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_16,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_61,plain,(
    ! [B_25,A_26] :
      ( B_25 = A_26
      | ~ r1_tarski(A_26,B_25)
      | ~ v1_zfmisc_1(B_25)
      | v1_xboole_0(B_25)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_75,plain,(
    ! [A_30,B_31] :
      ( k3_xboole_0(A_30,B_31) = A_30
      | ~ v1_zfmisc_1(A_30)
      | v1_xboole_0(A_30)
      | v1_xboole_0(k3_xboole_0(A_30,B_31)) ) ),
    inference(resolution,[status(thm)],[c_2,c_61])).

tff(c_14,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_78,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_75,c_14])).

tff(c_81,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_78])).

tff(c_82,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_81])).

tff(c_57,plain,(
    ! [A_22,B_23,C_24] : r1_tarski(k2_xboole_0(k3_xboole_0(A_22,B_23),k3_xboole_0(A_22,C_24)),k2_xboole_0(B_23,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ! [A_22,A_3,B_4] : r1_tarski(k2_xboole_0(k3_xboole_0(A_22,A_3),k3_xboole_0(A_22,k3_xboole_0(A_3,B_4))),A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_57])).

tff(c_90,plain,(
    ! [B_4] : r1_tarski(k2_xboole_0('#skF_1',k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',B_4))),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_60])).

tff(c_114,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_90])).

tff(c_116,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_114])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:47:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.17  
% 1.75/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.18  %$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 1.75/1.18  
% 1.75/1.18  %Foreground sorts:
% 1.75/1.18  
% 1.75/1.18  
% 1.75/1.18  %Background operators:
% 1.75/1.18  
% 1.75/1.18  
% 1.75/1.18  %Foreground operators:
% 1.75/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.75/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.75/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.75/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.75/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.18  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.75/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.75/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.75/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.75/1.18  
% 1.75/1.19  tff(f_58, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tex_2)).
% 1.75/1.19  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 1.75/1.19  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.75/1.19  tff(f_46, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 1.75/1.19  tff(f_31, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 1.75/1.19  tff(c_12, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.75/1.19  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k3_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.75/1.19  tff(c_18, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.75/1.19  tff(c_16, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.75/1.19  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.75/1.19  tff(c_61, plain, (![B_25, A_26]: (B_25=A_26 | ~r1_tarski(A_26, B_25) | ~v1_zfmisc_1(B_25) | v1_xboole_0(B_25) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.75/1.19  tff(c_75, plain, (![A_30, B_31]: (k3_xboole_0(A_30, B_31)=A_30 | ~v1_zfmisc_1(A_30) | v1_xboole_0(A_30) | v1_xboole_0(k3_xboole_0(A_30, B_31)))), inference(resolution, [status(thm)], [c_2, c_61])).
% 1.75/1.19  tff(c_14, plain, (~v1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.75/1.19  tff(c_78, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1' | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_75, c_14])).
% 1.75/1.19  tff(c_81, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1' | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_78])).
% 1.75/1.19  tff(c_82, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_18, c_81])).
% 1.75/1.19  tff(c_57, plain, (![A_22, B_23, C_24]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_22, B_23), k3_xboole_0(A_22, C_24)), k2_xboole_0(B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.75/1.19  tff(c_60, plain, (![A_22, A_3, B_4]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_22, A_3), k3_xboole_0(A_22, k3_xboole_0(A_3, B_4))), A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_57])).
% 1.75/1.19  tff(c_90, plain, (![B_4]: (r1_tarski(k2_xboole_0('#skF_1', k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', B_4))), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_60])).
% 1.75/1.19  tff(c_114, plain, (r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_90])).
% 1.75/1.19  tff(c_116, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_114])).
% 1.75/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.19  
% 1.75/1.19  Inference rules
% 1.75/1.19  ----------------------
% 1.75/1.19  #Ref     : 0
% 1.75/1.19  #Sup     : 24
% 1.75/1.19  #Fact    : 0
% 1.75/1.19  #Define  : 0
% 1.75/1.19  #Split   : 0
% 1.75/1.19  #Chain   : 0
% 1.75/1.19  #Close   : 0
% 1.75/1.19  
% 1.75/1.19  Ordering : KBO
% 1.75/1.19  
% 1.75/1.19  Simplification rules
% 1.75/1.19  ----------------------
% 1.75/1.19  #Subsume      : 1
% 1.75/1.19  #Demod        : 6
% 1.75/1.19  #Tautology    : 9
% 1.75/1.19  #SimpNegUnit  : 3
% 1.75/1.19  #BackRed      : 1
% 1.75/1.19  
% 1.75/1.19  #Partial instantiations: 0
% 1.75/1.19  #Strategies tried      : 1
% 1.75/1.19  
% 1.75/1.19  Timing (in seconds)
% 1.75/1.19  ----------------------
% 1.75/1.19  Preprocessing        : 0.27
% 1.75/1.19  Parsing              : 0.16
% 1.75/1.19  CNF conversion       : 0.02
% 1.75/1.19  Main loop            : 0.13
% 1.75/1.19  Inferencing          : 0.06
% 1.75/1.19  Reduction            : 0.03
% 1.75/1.19  Demodulation         : 0.03
% 1.75/1.19  BG Simplification    : 0.01
% 1.75/1.19  Subsumption          : 0.02
% 1.75/1.19  Abstraction          : 0.01
% 1.75/1.19  MUC search           : 0.00
% 1.75/1.19  Cooper               : 0.00
% 1.75/1.19  Total                : 0.43
% 1.75/1.19  Index Insertion      : 0.00
% 1.75/1.19  Index Deletion       : 0.00
% 1.75/1.19  Index Matching       : 0.00
% 1.75/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
