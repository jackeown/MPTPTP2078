%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:19 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   39 (  42 expanded)
%              Number of leaves         :   24 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   33 (  45 expanded)
%              Number of equality atoms :   12 (  15 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_44,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_88,plain,(
    ! [A_31,B_32] :
      ( k3_xboole_0(A_31,B_32) = A_31
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_96,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_88])).

tff(c_42,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_283,plain,(
    ! [A_57,B_58] :
      ( k4_xboole_0(A_57,B_58) = k3_subset_1(A_57,B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_296,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_283])).

tff(c_10,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_xboole_0(A_7,C_9)
      | ~ r1_tarski(A_7,k4_xboole_0(B_8,C_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_351,plain,(
    ! [A_60] :
      ( r1_xboole_0(A_60,'#skF_5')
      | ~ r1_tarski(A_60,k3_subset_1('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_10])).

tff(c_355,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_351])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_367,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_355,c_4])).

tff(c_369,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_367])).

tff(c_371,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_369])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:11:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.26  
% 2.24/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.27  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.24/1.27  
% 2.24/1.27  %Foreground sorts:
% 2.24/1.27  
% 2.24/1.27  
% 2.24/1.27  %Background operators:
% 2.24/1.27  
% 2.24/1.27  
% 2.24/1.27  %Foreground operators:
% 2.24/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.24/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.24/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.24/1.27  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.24/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.24/1.27  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.24/1.27  tff('#skF_5', type, '#skF_5': $i).
% 2.24/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.24/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.24/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.24/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.24/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.24/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.24/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.24/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.24/1.27  
% 2.24/1.28  tff(f_79, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_subset_1)).
% 2.24/1.28  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.24/1.28  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.24/1.28  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.24/1.28  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.24/1.28  tff(c_40, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.24/1.28  tff(c_44, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.24/1.28  tff(c_88, plain, (![A_31, B_32]: (k3_xboole_0(A_31, B_32)=A_31 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.24/1.28  tff(c_96, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_44, c_88])).
% 2.24/1.28  tff(c_42, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.24/1.28  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.24/1.28  tff(c_283, plain, (![A_57, B_58]: (k4_xboole_0(A_57, B_58)=k3_subset_1(A_57, B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.24/1.28  tff(c_296, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_283])).
% 2.24/1.28  tff(c_10, plain, (![A_7, C_9, B_8]: (r1_xboole_0(A_7, C_9) | ~r1_tarski(A_7, k4_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.24/1.28  tff(c_351, plain, (![A_60]: (r1_xboole_0(A_60, '#skF_5') | ~r1_tarski(A_60, k3_subset_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_296, c_10])).
% 2.24/1.28  tff(c_355, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_42, c_351])).
% 2.24/1.28  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.24/1.28  tff(c_367, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_355, c_4])).
% 2.24/1.28  tff(c_369, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_367])).
% 2.24/1.28  tff(c_371, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_369])).
% 2.24/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.28  
% 2.24/1.28  Inference rules
% 2.24/1.28  ----------------------
% 2.24/1.28  #Ref     : 0
% 2.24/1.28  #Sup     : 91
% 2.24/1.28  #Fact    : 0
% 2.24/1.28  #Define  : 0
% 2.24/1.28  #Split   : 0
% 2.24/1.28  #Chain   : 0
% 2.24/1.28  #Close   : 0
% 2.24/1.28  
% 2.24/1.28  Ordering : KBO
% 2.24/1.28  
% 2.24/1.28  Simplification rules
% 2.24/1.28  ----------------------
% 2.24/1.28  #Subsume      : 6
% 2.24/1.28  #Demod        : 13
% 2.24/1.28  #Tautology    : 57
% 2.24/1.28  #SimpNegUnit  : 3
% 2.24/1.28  #BackRed      : 3
% 2.24/1.28  
% 2.24/1.28  #Partial instantiations: 0
% 2.24/1.28  #Strategies tried      : 1
% 2.24/1.28  
% 2.24/1.28  Timing (in seconds)
% 2.24/1.28  ----------------------
% 2.24/1.28  Preprocessing        : 0.30
% 2.24/1.28  Parsing              : 0.16
% 2.24/1.28  CNF conversion       : 0.02
% 2.24/1.28  Main loop            : 0.22
% 2.24/1.28  Inferencing          : 0.08
% 2.24/1.28  Reduction            : 0.07
% 2.24/1.28  Demodulation         : 0.05
% 2.24/1.28  BG Simplification    : 0.01
% 2.24/1.28  Subsumption          : 0.04
% 2.24/1.28  Abstraction          : 0.01
% 2.24/1.28  MUC search           : 0.00
% 2.24/1.28  Cooper               : 0.00
% 2.24/1.28  Total                : 0.54
% 2.24/1.28  Index Insertion      : 0.00
% 2.24/1.28  Index Deletion       : 0.00
% 2.24/1.28  Index Matching       : 0.00
% 2.24/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
