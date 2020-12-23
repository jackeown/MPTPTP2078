%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:43 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   39 (  59 expanded)
%              Number of leaves         :   17 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :   64 ( 133 expanded)
%              Number of equality atoms :    5 (  15 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ( r1_xboole_0(B,C)
                & r1_xboole_0(k3_subset_1(A,B),k3_subset_1(A,C)) )
             => B = k3_subset_1(A,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,C)
          <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,k3_subset_1(A,C))
          <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(k3_subset_1(A,B),C)
           => r1_tarski(k3_subset_1(A,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_14,plain,(
    ! [B_10,A_9,C_12] :
      ( r1_tarski(B_10,k3_subset_1(A_9,C_12))
      | ~ r1_xboole_0(B_10,C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_20,plain,(
    k3_subset_1('#skF_1','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k3_subset_1(A_3,B_4),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_22,plain,(
    r1_xboole_0(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_39,plain,(
    ! [B_23,C_24,A_25] :
      ( r1_tarski(B_23,C_24)
      | ~ r1_xboole_0(B_23,k3_subset_1(A_25,C_24))
      | ~ m1_subset_1(C_24,k1_zfmisc_1(A_25))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_42,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_22,c_39])).

tff(c_45,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_3')
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_42])).

tff(c_46,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_45])).

tff(c_49,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_8,c_46])).

tff(c_53,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_49])).

tff(c_54,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_45])).

tff(c_85,plain,(
    ! [A_35,C_36,B_37] :
      ( r1_tarski(k3_subset_1(A_35,C_36),B_37)
      | ~ r1_tarski(k3_subset_1(A_35,B_37),C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(A_35))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_90,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_54,c_85])).

tff(c_97,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_90])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_102,plain,
    ( k3_subset_1('#skF_1','#skF_3') = '#skF_2'
    | ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_97,c_2])).

tff(c_108,plain,(
    ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_102])).

tff(c_111,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_14,c_108])).

tff(c_115,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_111])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:22:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.63  
% 2.30/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.63  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.30/1.63  
% 2.30/1.63  %Foreground sorts:
% 2.30/1.63  
% 2.30/1.63  
% 2.30/1.63  %Background operators:
% 2.30/1.63  
% 2.30/1.63  
% 2.30/1.63  %Foreground operators:
% 2.30/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.30/1.63  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.30/1.63  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.30/1.63  tff('#skF_2', type, '#skF_2': $i).
% 2.30/1.63  tff('#skF_3', type, '#skF_3': $i).
% 2.30/1.63  tff('#skF_1', type, '#skF_1': $i).
% 2.30/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.30/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.30/1.63  
% 2.30/1.65  tff(f_74, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_xboole_0(B, C) & r1_xboole_0(k3_subset_1(A, B), k3_subset_1(A, C))) => (B = k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_subset_1)).
% 2.30/1.65  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_subset_1)).
% 2.30/1.65  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.30/1.65  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_subset_1)).
% 2.30/1.65  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), C) => r1_tarski(k3_subset_1(A, C), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_subset_1)).
% 2.30/1.65  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.30/1.65  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.30/1.65  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.30/1.65  tff(c_24, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.30/1.65  tff(c_14, plain, (![B_10, A_9, C_12]: (r1_tarski(B_10, k3_subset_1(A_9, C_12)) | ~r1_xboole_0(B_10, C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.30/1.65  tff(c_20, plain, (k3_subset_1('#skF_1', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.30/1.65  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(k3_subset_1(A_3, B_4), k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.30/1.65  tff(c_22, plain, (r1_xboole_0(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.30/1.65  tff(c_39, plain, (![B_23, C_24, A_25]: (r1_tarski(B_23, C_24) | ~r1_xboole_0(B_23, k3_subset_1(A_25, C_24)) | ~m1_subset_1(C_24, k1_zfmisc_1(A_25)) | ~m1_subset_1(B_23, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.30/1.65  tff(c_42, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_39])).
% 2.30/1.65  tff(c_45, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_3') | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_42])).
% 2.30/1.65  tff(c_46, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_45])).
% 2.30/1.65  tff(c_49, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_46])).
% 2.30/1.65  tff(c_53, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_49])).
% 2.30/1.65  tff(c_54, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_45])).
% 2.30/1.65  tff(c_85, plain, (![A_35, C_36, B_37]: (r1_tarski(k3_subset_1(A_35, C_36), B_37) | ~r1_tarski(k3_subset_1(A_35, B_37), C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(A_35)) | ~m1_subset_1(B_37, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.30/1.65  tff(c_90, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_54, c_85])).
% 2.30/1.65  tff(c_97, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_90])).
% 2.30/1.65  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.30/1.65  tff(c_102, plain, (k3_subset_1('#skF_1', '#skF_3')='#skF_2' | ~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_97, c_2])).
% 2.30/1.65  tff(c_108, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_20, c_102])).
% 2.30/1.65  tff(c_111, plain, (~r1_xboole_0('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_108])).
% 2.30/1.65  tff(c_115, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_111])).
% 2.30/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.65  
% 2.30/1.65  Inference rules
% 2.30/1.65  ----------------------
% 2.30/1.65  #Ref     : 0
% 2.30/1.65  #Sup     : 15
% 2.30/1.65  #Fact    : 0
% 2.30/1.65  #Define  : 0
% 2.30/1.65  #Split   : 2
% 2.30/1.65  #Chain   : 0
% 2.30/1.65  #Close   : 0
% 2.30/1.65  
% 2.30/1.65  Ordering : KBO
% 2.30/1.65  
% 2.30/1.65  Simplification rules
% 2.30/1.65  ----------------------
% 2.30/1.65  #Subsume      : 0
% 2.30/1.65  #Demod        : 14
% 2.30/1.65  #Tautology    : 5
% 2.30/1.65  #SimpNegUnit  : 1
% 2.51/1.65  #BackRed      : 0
% 2.51/1.65  
% 2.51/1.65  #Partial instantiations: 0
% 2.51/1.65  #Strategies tried      : 1
% 2.51/1.65  
% 2.51/1.65  Timing (in seconds)
% 2.51/1.65  ----------------------
% 2.51/1.66  Preprocessing        : 0.45
% 2.51/1.66  Parsing              : 0.24
% 2.51/1.66  CNF conversion       : 0.03
% 2.51/1.66  Main loop            : 0.26
% 2.51/1.66  Inferencing          : 0.10
% 2.51/1.66  Reduction            : 0.07
% 2.51/1.66  Demodulation         : 0.05
% 2.51/1.66  BG Simplification    : 0.02
% 2.51/1.66  Subsumption          : 0.06
% 2.51/1.66  Abstraction          : 0.01
% 2.51/1.66  MUC search           : 0.00
% 2.51/1.66  Cooper               : 0.00
% 2.51/1.66  Total                : 0.75
% 2.51/1.66  Index Insertion      : 0.00
% 2.51/1.66  Index Deletion       : 0.00
% 2.51/1.66  Index Matching       : 0.00
% 2.51/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
