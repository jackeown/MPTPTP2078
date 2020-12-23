%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:20 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   45 (  48 expanded)
%              Number of leaves         :   24 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :   46 (  58 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_66,plain,(
    ! [A_24,B_25] :
      ( k3_xboole_0(A_24,B_25) = A_24
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_73,plain,(
    k3_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_26,c_66])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_481,plain,(
    ! [A_60,B_61] :
      ( k4_xboole_0(A_60,B_61) = k3_subset_1(A_60,B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_485,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_481])).

tff(c_28,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_102,plain,(
    ! [A_26,B_27] :
      ( k2_xboole_0(A_26,B_27) = B_27
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_110,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_28,c_102])).

tff(c_20,plain,(
    ! [A_14,B_15] : r1_xboole_0(k4_xboole_0(A_14,B_15),B_15) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_159,plain,(
    ! [A_34,B_35,C_36] :
      ( r1_xboole_0(A_34,B_35)
      | ~ r1_xboole_0(A_34,k2_xboole_0(B_35,C_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_198,plain,(
    ! [A_41,B_42,C_43] : r1_xboole_0(k4_xboole_0(A_41,k2_xboole_0(B_42,C_43)),B_42) ),
    inference(resolution,[status(thm)],[c_20,c_159])).

tff(c_219,plain,(
    ! [A_44] : r1_xboole_0(k4_xboole_0(A_44,'#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_198])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_224,plain,(
    ! [A_45] : k3_xboole_0(k4_xboole_0(A_45,'#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_219,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_229,plain,(
    ! [A_45] : k3_xboole_0('#skF_2',k4_xboole_0(A_45,'#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_2])).

tff(c_488,plain,(
    k3_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_485,c_229])).

tff(c_504,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_488])).

tff(c_506,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_504])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:26:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.27  
% 2.18/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.27  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.18/1.27  
% 2.18/1.27  %Foreground sorts:
% 2.18/1.27  
% 2.18/1.27  
% 2.18/1.27  %Background operators:
% 2.18/1.27  
% 2.18/1.27  
% 2.18/1.27  %Foreground operators:
% 2.18/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.18/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.27  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.18/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.27  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.18/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.18/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.18/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.18/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.27  
% 2.18/1.28  tff(f_72, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 2.18/1.28  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.18/1.28  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.18/1.28  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.18/1.28  tff(f_59, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.18/1.28  tff(f_57, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 2.18/1.28  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.18/1.28  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.18/1.28  tff(c_24, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.18/1.28  tff(c_26, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.18/1.28  tff(c_66, plain, (![A_24, B_25]: (k3_xboole_0(A_24, B_25)=A_24 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.18/1.28  tff(c_73, plain, (k3_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))='#skF_2'), inference(resolution, [status(thm)], [c_26, c_66])).
% 2.18/1.28  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.18/1.28  tff(c_481, plain, (![A_60, B_61]: (k4_xboole_0(A_60, B_61)=k3_subset_1(A_60, B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.18/1.28  tff(c_485, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_481])).
% 2.18/1.28  tff(c_28, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.18/1.28  tff(c_102, plain, (![A_26, B_27]: (k2_xboole_0(A_26, B_27)=B_27 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.18/1.28  tff(c_110, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_28, c_102])).
% 2.18/1.28  tff(c_20, plain, (![A_14, B_15]: (r1_xboole_0(k4_xboole_0(A_14, B_15), B_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.18/1.28  tff(c_159, plain, (![A_34, B_35, C_36]: (r1_xboole_0(A_34, B_35) | ~r1_xboole_0(A_34, k2_xboole_0(B_35, C_36)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.18/1.28  tff(c_198, plain, (![A_41, B_42, C_43]: (r1_xboole_0(k4_xboole_0(A_41, k2_xboole_0(B_42, C_43)), B_42))), inference(resolution, [status(thm)], [c_20, c_159])).
% 2.18/1.28  tff(c_219, plain, (![A_44]: (r1_xboole_0(k4_xboole_0(A_44, '#skF_3'), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_110, c_198])).
% 2.18/1.28  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.18/1.28  tff(c_224, plain, (![A_45]: (k3_xboole_0(k4_xboole_0(A_45, '#skF_3'), '#skF_2')=k1_xboole_0)), inference(resolution, [status(thm)], [c_219, c_4])).
% 2.18/1.28  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.18/1.28  tff(c_229, plain, (![A_45]: (k3_xboole_0('#skF_2', k4_xboole_0(A_45, '#skF_3'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_224, c_2])).
% 2.18/1.28  tff(c_488, plain, (k3_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_485, c_229])).
% 2.18/1.28  tff(c_504, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_73, c_488])).
% 2.18/1.28  tff(c_506, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_504])).
% 2.18/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.28  
% 2.18/1.28  Inference rules
% 2.18/1.28  ----------------------
% 2.18/1.28  #Ref     : 0
% 2.18/1.29  #Sup     : 128
% 2.18/1.29  #Fact    : 0
% 2.18/1.29  #Define  : 0
% 2.18/1.29  #Split   : 0
% 2.18/1.29  #Chain   : 0
% 2.18/1.29  #Close   : 0
% 2.18/1.29  
% 2.18/1.29  Ordering : KBO
% 2.18/1.29  
% 2.18/1.29  Simplification rules
% 2.18/1.29  ----------------------
% 2.18/1.29  #Subsume      : 0
% 2.18/1.29  #Demod        : 24
% 2.18/1.29  #Tautology    : 66
% 2.18/1.29  #SimpNegUnit  : 1
% 2.18/1.29  #BackRed      : 0
% 2.18/1.29  
% 2.18/1.29  #Partial instantiations: 0
% 2.18/1.29  #Strategies tried      : 1
% 2.18/1.29  
% 2.18/1.29  Timing (in seconds)
% 2.18/1.29  ----------------------
% 2.18/1.29  Preprocessing        : 0.28
% 2.18/1.29  Parsing              : 0.15
% 2.18/1.29  CNF conversion       : 0.02
% 2.18/1.29  Main loop            : 0.24
% 2.18/1.29  Inferencing          : 0.09
% 2.18/1.29  Reduction            : 0.08
% 2.18/1.29  Demodulation         : 0.07
% 2.18/1.29  BG Simplification    : 0.01
% 2.18/1.29  Subsumption          : 0.04
% 2.18/1.29  Abstraction          : 0.01
% 2.18/1.29  MUC search           : 0.00
% 2.18/1.29  Cooper               : 0.00
% 2.18/1.29  Total                : 0.55
% 2.18/1.29  Index Insertion      : 0.00
% 2.18/1.29  Index Deletion       : 0.00
% 2.18/1.29  Index Matching       : 0.00
% 2.18/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
