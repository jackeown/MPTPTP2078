%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:03 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   48 (  68 expanded)
%              Number of leaves         :   23 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  81 expanded)
%              Number of equality atoms :   23 (  42 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_43,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_16,plain,(
    ! [A_12] : k1_subset_1(A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,
    ( k1_subset_1('#skF_1') != '#skF_2'
    | ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_29,plain,
    ( k1_xboole_0 != '#skF_2'
    | ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_22])).

tff(c_73,plain,(
    ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_29])).

tff(c_28,plain,
    ( r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2'))
    | k1_subset_1('#skF_1') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_30,plain,
    ( r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_28])).

tff(c_75,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_30])).

tff(c_12,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_77,plain,(
    ! [A_9] : r1_tarski('#skF_2',A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_12])).

tff(c_91,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_73])).

tff(c_92,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_29])).

tff(c_93,plain,(
    r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_29])).

tff(c_97,plain,(
    ! [A_27,B_28] :
      ( k3_xboole_0(A_27,B_28) = A_27
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_104,plain,(
    k3_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_93,c_97])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_390,plain,(
    ! [A_46,B_47] :
      ( k4_xboole_0(A_46,B_47) = k3_subset_1(A_46,B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_394,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_390])).

tff(c_14,plain,(
    ! [A_10,B_11] : r1_xboole_0(k4_xboole_0(A_10,B_11),B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_167,plain,(
    ! [A_31,B_32] :
      ( k3_xboole_0(A_31,B_32) = k1_xboole_0
      | ~ r1_xboole_0(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_176,plain,(
    ! [A_33,B_34] : k3_xboole_0(k4_xboole_0(A_33,B_34),B_34) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_167])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_184,plain,(
    ! [B_34,A_33] : k3_xboole_0(B_34,k4_xboole_0(A_33,B_34)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_2])).

tff(c_398,plain,(
    k3_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_184])).

tff(c_407,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_398])).

tff(c_409,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_407])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:18:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.25  
% 2.03/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.25  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.03/1.25  
% 2.03/1.25  %Foreground sorts:
% 2.03/1.25  
% 2.03/1.25  
% 2.03/1.25  %Background operators:
% 2.03/1.25  
% 2.03/1.25  
% 2.03/1.25  %Foreground operators:
% 2.03/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.03/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.03/1.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.03/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.03/1.25  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.03/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.03/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.03/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.03/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.03/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.25  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.03/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.03/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.03/1.25  
% 2.03/1.26  tff(f_43, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.03/1.26  tff(f_54, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 2.03/1.26  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.03/1.26  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.03/1.26  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.03/1.26  tff(f_41, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.03/1.26  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.03/1.26  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.03/1.26  tff(c_16, plain, (![A_12]: (k1_subset_1(A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.03/1.26  tff(c_22, plain, (k1_subset_1('#skF_1')!='#skF_2' | ~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.03/1.26  tff(c_29, plain, (k1_xboole_0!='#skF_2' | ~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_22])).
% 2.03/1.26  tff(c_73, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_29])).
% 2.03/1.26  tff(c_28, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2')) | k1_subset_1('#skF_1')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.03/1.26  tff(c_30, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_28])).
% 2.03/1.26  tff(c_75, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_73, c_30])).
% 2.03/1.26  tff(c_12, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.03/1.26  tff(c_77, plain, (![A_9]: (r1_tarski('#skF_2', A_9))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_12])).
% 2.03/1.26  tff(c_91, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77, c_73])).
% 2.03/1.26  tff(c_92, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_29])).
% 2.03/1.26  tff(c_93, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_29])).
% 2.03/1.26  tff(c_97, plain, (![A_27, B_28]: (k3_xboole_0(A_27, B_28)=A_27 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.03/1.26  tff(c_104, plain, (k3_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_93, c_97])).
% 2.03/1.26  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.03/1.26  tff(c_390, plain, (![A_46, B_47]: (k4_xboole_0(A_46, B_47)=k3_subset_1(A_46, B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.03/1.26  tff(c_394, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_20, c_390])).
% 2.03/1.26  tff(c_14, plain, (![A_10, B_11]: (r1_xboole_0(k4_xboole_0(A_10, B_11), B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.03/1.26  tff(c_167, plain, (![A_31, B_32]: (k3_xboole_0(A_31, B_32)=k1_xboole_0 | ~r1_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.03/1.26  tff(c_176, plain, (![A_33, B_34]: (k3_xboole_0(k4_xboole_0(A_33, B_34), B_34)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_167])).
% 2.03/1.26  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.03/1.26  tff(c_184, plain, (![B_34, A_33]: (k3_xboole_0(B_34, k4_xboole_0(A_33, B_34))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_176, c_2])).
% 2.03/1.26  tff(c_398, plain, (k3_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_394, c_184])).
% 2.03/1.26  tff(c_407, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_398])).
% 2.03/1.26  tff(c_409, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_407])).
% 2.03/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.26  
% 2.03/1.26  Inference rules
% 2.03/1.26  ----------------------
% 2.03/1.26  #Ref     : 0
% 2.03/1.26  #Sup     : 108
% 2.03/1.26  #Fact    : 0
% 2.03/1.26  #Define  : 0
% 2.03/1.26  #Split   : 1
% 2.03/1.26  #Chain   : 0
% 2.03/1.26  #Close   : 0
% 2.03/1.26  
% 2.03/1.26  Ordering : KBO
% 2.03/1.26  
% 2.03/1.26  Simplification rules
% 2.03/1.26  ----------------------
% 2.03/1.26  #Subsume      : 12
% 2.03/1.26  #Demod        : 24
% 2.03/1.26  #Tautology    : 60
% 2.03/1.26  #SimpNegUnit  : 3
% 2.03/1.26  #BackRed      : 4
% 2.03/1.26  
% 2.03/1.26  #Partial instantiations: 0
% 2.03/1.26  #Strategies tried      : 1
% 2.03/1.26  
% 2.03/1.26  Timing (in seconds)
% 2.03/1.26  ----------------------
% 2.03/1.27  Preprocessing        : 0.29
% 2.03/1.27  Parsing              : 0.15
% 2.03/1.27  CNF conversion       : 0.02
% 2.03/1.27  Main loop            : 0.21
% 2.03/1.27  Inferencing          : 0.07
% 2.03/1.27  Reduction            : 0.07
% 2.03/1.27  Demodulation         : 0.06
% 2.03/1.27  BG Simplification    : 0.01
% 2.03/1.27  Subsumption          : 0.03
% 2.03/1.27  Abstraction          : 0.01
% 2.03/1.27  MUC search           : 0.00
% 2.03/1.27  Cooper               : 0.00
% 2.03/1.27  Total                : 0.53
% 2.03/1.27  Index Insertion      : 0.00
% 2.03/1.27  Index Deletion       : 0.00
% 2.03/1.27  Index Matching       : 0.00
% 2.03/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
