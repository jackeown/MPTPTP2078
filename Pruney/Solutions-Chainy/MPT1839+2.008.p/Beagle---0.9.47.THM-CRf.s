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
% DateTime   : Thu Dec  3 10:28:22 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   37 (  44 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   39 (  55 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_20,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_26,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_24,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_128,plain,(
    ! [A_34,B_35] : k2_xboole_0(k3_xboole_0(A_34,B_35),k4_xboole_0(A_34,B_35)) = A_34 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_137,plain,(
    ! [A_34,B_35] : r1_tarski(k3_xboole_0(A_34,B_35),A_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_10])).

tff(c_385,plain,(
    ! [B_57,A_58] :
      ( B_57 = A_58
      | ~ r1_tarski(A_58,B_57)
      | ~ v1_zfmisc_1(B_57)
      | v1_xboole_0(B_57)
      | v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_566,plain,(
    ! [A_67,B_68] :
      ( k3_xboole_0(A_67,B_68) = A_67
      | ~ v1_zfmisc_1(A_67)
      | v1_xboole_0(A_67)
      | v1_xboole_0(k3_xboole_0(A_67,B_68)) ) ),
    inference(resolution,[status(thm)],[c_137,c_385])).

tff(c_22,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_569,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_566,c_22])).

tff(c_578,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_569])).

tff(c_579,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_578])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_149,plain,(
    ! [A_36,B_37] : r1_tarski(k3_xboole_0(A_36,B_37),A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_10])).

tff(c_155,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_149])).

tff(c_611,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_579,c_155])).

tff(c_626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_611])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n023.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 12:19:51 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.45  
% 2.71/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.45  %$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_1
% 2.71/1.45  
% 2.71/1.45  %Foreground sorts:
% 2.71/1.45  
% 2.71/1.45  
% 2.71/1.45  %Background operators:
% 2.71/1.45  
% 2.71/1.45  
% 2.71/1.45  %Foreground operators:
% 2.71/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.71/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.71/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.71/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.71/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.71/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.71/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.71/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.45  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.71/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.71/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.71/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.71/1.45  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.71/1.45  
% 2.71/1.46  tff(f_66, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tex_2)).
% 2.71/1.46  tff(f_33, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.71/1.46  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.71/1.46  tff(f_54, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.71/1.46  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.71/1.46  tff(c_20, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.71/1.46  tff(c_26, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.71/1.46  tff(c_24, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.71/1.46  tff(c_128, plain, (![A_34, B_35]: (k2_xboole_0(k3_xboole_0(A_34, B_35), k4_xboole_0(A_34, B_35))=A_34)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.71/1.46  tff(c_10, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.71/1.46  tff(c_137, plain, (![A_34, B_35]: (r1_tarski(k3_xboole_0(A_34, B_35), A_34))), inference(superposition, [status(thm), theory('equality')], [c_128, c_10])).
% 2.71/1.46  tff(c_385, plain, (![B_57, A_58]: (B_57=A_58 | ~r1_tarski(A_58, B_57) | ~v1_zfmisc_1(B_57) | v1_xboole_0(B_57) | v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.71/1.46  tff(c_566, plain, (![A_67, B_68]: (k3_xboole_0(A_67, B_68)=A_67 | ~v1_zfmisc_1(A_67) | v1_xboole_0(A_67) | v1_xboole_0(k3_xboole_0(A_67, B_68)))), inference(resolution, [status(thm)], [c_137, c_385])).
% 2.71/1.46  tff(c_22, plain, (~v1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.71/1.46  tff(c_569, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1' | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_566, c_22])).
% 2.71/1.46  tff(c_578, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1' | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_569])).
% 2.71/1.46  tff(c_579, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_26, c_578])).
% 2.71/1.46  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.71/1.46  tff(c_149, plain, (![A_36, B_37]: (r1_tarski(k3_xboole_0(A_36, B_37), A_36))), inference(superposition, [status(thm), theory('equality')], [c_128, c_10])).
% 2.71/1.46  tff(c_155, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_149])).
% 2.71/1.46  tff(c_611, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_579, c_155])).
% 2.71/1.46  tff(c_626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_611])).
% 2.71/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.46  
% 2.71/1.46  Inference rules
% 2.71/1.46  ----------------------
% 2.71/1.46  #Ref     : 0
% 2.71/1.46  #Sup     : 150
% 2.71/1.46  #Fact    : 0
% 2.71/1.46  #Define  : 0
% 2.71/1.46  #Split   : 1
% 2.71/1.46  #Chain   : 0
% 2.71/1.46  #Close   : 0
% 2.71/1.46  
% 2.71/1.46  Ordering : KBO
% 2.71/1.46  
% 2.71/1.46  Simplification rules
% 2.71/1.46  ----------------------
% 2.71/1.46  #Subsume      : 2
% 2.71/1.46  #Demod        : 74
% 2.71/1.46  #Tautology    : 90
% 2.71/1.46  #SimpNegUnit  : 4
% 2.71/1.46  #BackRed      : 1
% 2.71/1.46  
% 2.71/1.46  #Partial instantiations: 0
% 2.71/1.46  #Strategies tried      : 1
% 2.71/1.46  
% 2.71/1.46  Timing (in seconds)
% 2.71/1.46  ----------------------
% 2.71/1.47  Preprocessing        : 0.32
% 2.71/1.47  Parsing              : 0.17
% 2.71/1.47  CNF conversion       : 0.02
% 2.71/1.47  Main loop            : 0.32
% 2.71/1.47  Inferencing          : 0.11
% 2.71/1.47  Reduction            : 0.13
% 2.71/1.47  Demodulation         : 0.10
% 2.71/1.47  BG Simplification    : 0.02
% 2.71/1.47  Subsumption          : 0.05
% 2.71/1.47  Abstraction          : 0.02
% 2.71/1.47  MUC search           : 0.00
% 2.71/1.47  Cooper               : 0.00
% 2.71/1.47  Total                : 0.67
% 2.71/1.47  Index Insertion      : 0.00
% 2.71/1.47  Index Deletion       : 0.00
% 2.71/1.47  Index Matching       : 0.00
% 2.71/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
