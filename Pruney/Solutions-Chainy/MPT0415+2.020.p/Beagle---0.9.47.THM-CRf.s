%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:48 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   42 (  59 expanded)
%              Number of leaves         :   22 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :   50 (  81 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ~ ( B != k1_xboole_0
            & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_32,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6,plain,(
    ! [A_2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_95,plain,(
    ! [C_36,B_37,A_38] :
      ( ~ v1_xboole_0(C_36)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(C_36))
      | ~ r2_hidden(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_107,plain,(
    ! [A_2,A_38] :
      ( ~ v1_xboole_0(A_2)
      | ~ r2_hidden(A_38,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_95])).

tff(c_108,plain,(
    ! [A_38] : ~ r2_hidden(A_38,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_537,plain,(
    ! [A_97,B_98,C_99] :
      ( r2_hidden('#skF_1'(A_97,B_98,C_99),C_99)
      | r2_hidden(k3_subset_1(A_97,'#skF_1'(A_97,B_98,C_99)),B_98)
      | k7_setfam_1(A_97,B_98) = C_99
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k1_zfmisc_1(A_97)))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(k1_zfmisc_1(A_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_577,plain,(
    ! [A_97,C_99] :
      ( r2_hidden('#skF_1'(A_97,k1_xboole_0,C_99),C_99)
      | k7_setfam_1(A_97,k1_xboole_0) = C_99
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k1_zfmisc_1(A_97)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_97))) ) ),
    inference(resolution,[status(thm)],[c_537,c_108])).

tff(c_625,plain,(
    ! [A_101,C_102] :
      ( r2_hidden('#skF_1'(A_101,k1_xboole_0,C_102),C_102)
      | k7_setfam_1(A_101,k1_xboole_0) = C_102
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k1_zfmisc_1(A_101))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_577])).

tff(c_639,plain,(
    ! [A_101] :
      ( r2_hidden('#skF_1'(A_101,k1_xboole_0,k1_xboole_0),k1_xboole_0)
      | k7_setfam_1(A_101,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_625])).

tff(c_654,plain,(
    ! [A_103] : k7_setfam_1(A_103,k1_xboole_0) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_639])).

tff(c_36,plain,(
    k7_setfam_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_143,plain,(
    ! [A_50,B_51] :
      ( k7_setfam_1(A_50,k7_setfam_1(A_50,B_51)) = B_51
      | ~ m1_subset_1(B_51,k1_zfmisc_1(k1_zfmisc_1(A_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_148,plain,(
    k7_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_143])).

tff(c_157,plain,(
    k7_setfam_1('#skF_3',k1_xboole_0) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_148])).

tff(c_660,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_654,c_157])).

tff(c_670,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_660])).

tff(c_671,plain,(
    ! [A_2] : ~ v1_xboole_0(A_2) ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_673,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_671,c_2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:44:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.47  
% 2.84/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.47  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.84/1.47  
% 2.84/1.47  %Foreground sorts:
% 2.84/1.47  
% 2.84/1.47  
% 2.84/1.47  %Background operators:
% 2.84/1.47  
% 2.84/1.47  
% 2.84/1.47  %Foreground operators:
% 2.84/1.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.84/1.47  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.84/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.84/1.47  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.84/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.84/1.47  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.84/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.84/1.47  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.84/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.84/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.84/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.47  tff('#skF_4', type, '#skF_4': $i).
% 2.84/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.84/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.84/1.47  
% 2.84/1.48  tff(f_82, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_setfam_1)).
% 2.84/1.48  tff(f_32, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.84/1.48  tff(f_73, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.84/1.48  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_setfam_1)).
% 2.84/1.48  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 2.84/1.48  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.84/1.48  tff(c_38, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.84/1.48  tff(c_6, plain, (![A_2]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.84/1.48  tff(c_95, plain, (![C_36, B_37, A_38]: (~v1_xboole_0(C_36) | ~m1_subset_1(B_37, k1_zfmisc_1(C_36)) | ~r2_hidden(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.84/1.48  tff(c_107, plain, (![A_2, A_38]: (~v1_xboole_0(A_2) | ~r2_hidden(A_38, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_95])).
% 2.84/1.48  tff(c_108, plain, (![A_38]: (~r2_hidden(A_38, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_107])).
% 2.84/1.48  tff(c_537, plain, (![A_97, B_98, C_99]: (r2_hidden('#skF_1'(A_97, B_98, C_99), C_99) | r2_hidden(k3_subset_1(A_97, '#skF_1'(A_97, B_98, C_99)), B_98) | k7_setfam_1(A_97, B_98)=C_99 | ~m1_subset_1(C_99, k1_zfmisc_1(k1_zfmisc_1(A_97))) | ~m1_subset_1(B_98, k1_zfmisc_1(k1_zfmisc_1(A_97))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.84/1.48  tff(c_577, plain, (![A_97, C_99]: (r2_hidden('#skF_1'(A_97, k1_xboole_0, C_99), C_99) | k7_setfam_1(A_97, k1_xboole_0)=C_99 | ~m1_subset_1(C_99, k1_zfmisc_1(k1_zfmisc_1(A_97))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_97))))), inference(resolution, [status(thm)], [c_537, c_108])).
% 2.84/1.48  tff(c_625, plain, (![A_101, C_102]: (r2_hidden('#skF_1'(A_101, k1_xboole_0, C_102), C_102) | k7_setfam_1(A_101, k1_xboole_0)=C_102 | ~m1_subset_1(C_102, k1_zfmisc_1(k1_zfmisc_1(A_101))))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_577])).
% 2.84/1.48  tff(c_639, plain, (![A_101]: (r2_hidden('#skF_1'(A_101, k1_xboole_0, k1_xboole_0), k1_xboole_0) | k7_setfam_1(A_101, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_625])).
% 2.84/1.48  tff(c_654, plain, (![A_103]: (k7_setfam_1(A_103, k1_xboole_0)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_108, c_639])).
% 2.84/1.48  tff(c_36, plain, (k7_setfam_1('#skF_3', '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.84/1.48  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.84/1.48  tff(c_143, plain, (![A_50, B_51]: (k7_setfam_1(A_50, k7_setfam_1(A_50, B_51))=B_51 | ~m1_subset_1(B_51, k1_zfmisc_1(k1_zfmisc_1(A_50))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.84/1.48  tff(c_148, plain, (k7_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_40, c_143])).
% 2.84/1.48  tff(c_157, plain, (k7_setfam_1('#skF_3', k1_xboole_0)='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_148])).
% 2.84/1.48  tff(c_660, plain, (k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_654, c_157])).
% 2.84/1.48  tff(c_670, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_660])).
% 2.84/1.48  tff(c_671, plain, (![A_2]: (~v1_xboole_0(A_2))), inference(splitRight, [status(thm)], [c_107])).
% 2.84/1.48  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.84/1.48  tff(c_673, plain, $false, inference(negUnitSimplification, [status(thm)], [c_671, c_2])).
% 2.84/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.48  
% 2.84/1.48  Inference rules
% 2.84/1.48  ----------------------
% 2.84/1.48  #Ref     : 0
% 2.84/1.48  #Sup     : 145
% 2.84/1.48  #Fact    : 0
% 2.84/1.48  #Define  : 0
% 2.84/1.48  #Split   : 6
% 2.84/1.48  #Chain   : 0
% 2.84/1.48  #Close   : 0
% 2.84/1.48  
% 2.84/1.48  Ordering : KBO
% 2.84/1.48  
% 2.84/1.48  Simplification rules
% 2.84/1.48  ----------------------
% 2.84/1.48  #Subsume      : 21
% 2.84/1.48  #Demod        : 67
% 2.84/1.48  #Tautology    : 52
% 2.84/1.48  #SimpNegUnit  : 9
% 2.84/1.48  #BackRed      : 5
% 2.84/1.48  
% 2.84/1.48  #Partial instantiations: 0
% 2.84/1.48  #Strategies tried      : 1
% 2.84/1.48  
% 2.84/1.48  Timing (in seconds)
% 2.84/1.48  ----------------------
% 2.84/1.48  Preprocessing        : 0.38
% 2.84/1.48  Parsing              : 0.19
% 2.84/1.48  CNF conversion       : 0.02
% 2.84/1.48  Main loop            : 0.34
% 2.84/1.48  Inferencing          : 0.12
% 2.84/1.48  Reduction            : 0.10
% 2.84/1.48  Demodulation         : 0.07
% 2.84/1.48  BG Simplification    : 0.02
% 2.84/1.48  Subsumption          : 0.07
% 2.84/1.48  Abstraction          : 0.02
% 2.84/1.48  MUC search           : 0.00
% 2.84/1.48  Cooper               : 0.00
% 2.84/1.48  Total                : 0.75
% 2.84/1.48  Index Insertion      : 0.00
% 2.84/1.48  Index Deletion       : 0.00
% 2.84/1.48  Index Matching       : 0.00
% 2.84/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
