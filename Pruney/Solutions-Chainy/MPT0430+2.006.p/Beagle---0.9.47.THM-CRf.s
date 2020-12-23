%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:12 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   35 (  40 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   40 (  63 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_setfam_1 > r2_hidden > r1_tarski > m1_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v3_setfam_1,type,(
    v3_setfam_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( ( v3_setfam_1(B,A)
                & r1_tarski(C,B) )
             => v3_setfam_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_setfam_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v3_setfam_1(B,A)
      <=> ~ r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_setfam_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_30,plain,(
    v3_setfam_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_65,plain,(
    ! [A_24,B_25] :
      ( ~ r2_hidden(A_24,B_25)
      | ~ v3_setfam_1(B_25,A_24)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(k1_zfmisc_1(A_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_68,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | ~ v3_setfam_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_65])).

tff(c_74,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_68])).

tff(c_26,plain,(
    ~ v3_setfam_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_76,plain,(
    ! [B_26,A_27] :
      ( v3_setfam_1(B_26,A_27)
      | r2_hidden(A_27,B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(k1_zfmisc_1(A_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_82,plain,
    ( v3_setfam_1('#skF_5','#skF_3')
    | r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_76])).

tff(c_88,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_82])).

tff(c_28,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_35,plain,(
    ! [A_12,B_13] :
      ( k2_xboole_0(A_12,B_13) = B_13
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_39,plain,(
    k2_xboole_0('#skF_5','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_28,c_35])).

tff(c_48,plain,(
    ! [D_17,A_18,B_19] :
      ( ~ r2_hidden(D_17,A_18)
      | r2_hidden(D_17,k2_xboole_0(A_18,B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_51,plain,(
    ! [D_17] :
      ( ~ r2_hidden(D_17,'#skF_5')
      | r2_hidden(D_17,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_48])).

tff(c_91,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_51])).

tff(c_95,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_91])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:04:46 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.12  
% 1.65/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.12  %$ v3_setfam_1 > r2_hidden > r1_tarski > m1_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 1.65/1.12  
% 1.65/1.12  %Foreground sorts:
% 1.65/1.12  
% 1.65/1.12  
% 1.65/1.12  %Background operators:
% 1.65/1.12  
% 1.65/1.12  
% 1.65/1.12  %Foreground operators:
% 1.65/1.12  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.65/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.65/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.65/1.12  tff('#skF_5', type, '#skF_5': $i).
% 1.65/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.65/1.12  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.65/1.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.65/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.12  tff('#skF_4', type, '#skF_4': $i).
% 1.65/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.12  tff(v3_setfam_1, type, v3_setfam_1: ($i * $i) > $o).
% 1.65/1.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.65/1.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.65/1.12  
% 1.65/1.13  tff(f_57, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((v3_setfam_1(B, A) & r1_tarski(C, B)) => v3_setfam_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_setfam_1)).
% 1.65/1.13  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v3_setfam_1(B, A) <=> ~r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_setfam_1)).
% 1.65/1.13  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.65/1.13  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 1.65/1.13  tff(c_30, plain, (v3_setfam_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.65/1.13  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.65/1.13  tff(c_65, plain, (![A_24, B_25]: (~r2_hidden(A_24, B_25) | ~v3_setfam_1(B_25, A_24) | ~m1_subset_1(B_25, k1_zfmisc_1(k1_zfmisc_1(A_24))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.65/1.13  tff(c_68, plain, (~r2_hidden('#skF_3', '#skF_4') | ~v3_setfam_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_65])).
% 1.65/1.13  tff(c_74, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_68])).
% 1.65/1.13  tff(c_26, plain, (~v3_setfam_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.65/1.13  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.65/1.13  tff(c_76, plain, (![B_26, A_27]: (v3_setfam_1(B_26, A_27) | r2_hidden(A_27, B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(k1_zfmisc_1(A_27))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.65/1.13  tff(c_82, plain, (v3_setfam_1('#skF_5', '#skF_3') | r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_32, c_76])).
% 1.65/1.13  tff(c_88, plain, (r2_hidden('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_26, c_82])).
% 1.65/1.13  tff(c_28, plain, (r1_tarski('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.65/1.13  tff(c_35, plain, (![A_12, B_13]: (k2_xboole_0(A_12, B_13)=B_13 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.65/1.13  tff(c_39, plain, (k2_xboole_0('#skF_5', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_28, c_35])).
% 1.65/1.13  tff(c_48, plain, (![D_17, A_18, B_19]: (~r2_hidden(D_17, A_18) | r2_hidden(D_17, k2_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.65/1.13  tff(c_51, plain, (![D_17]: (~r2_hidden(D_17, '#skF_5') | r2_hidden(D_17, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_39, c_48])).
% 1.65/1.13  tff(c_91, plain, (r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_88, c_51])).
% 1.65/1.13  tff(c_95, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_91])).
% 1.65/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.13  
% 1.65/1.13  Inference rules
% 1.65/1.13  ----------------------
% 1.65/1.13  #Ref     : 0
% 1.65/1.13  #Sup     : 13
% 1.65/1.13  #Fact    : 0
% 1.65/1.13  #Define  : 0
% 1.65/1.13  #Split   : 0
% 1.65/1.13  #Chain   : 0
% 1.65/1.13  #Close   : 0
% 1.65/1.13  
% 1.65/1.13  Ordering : KBO
% 1.65/1.13  
% 1.65/1.13  Simplification rules
% 1.65/1.13  ----------------------
% 1.65/1.13  #Subsume      : 1
% 1.65/1.13  #Demod        : 2
% 1.65/1.13  #Tautology    : 7
% 1.65/1.13  #SimpNegUnit  : 3
% 1.65/1.13  #BackRed      : 0
% 1.65/1.13  
% 1.65/1.13  #Partial instantiations: 0
% 1.65/1.13  #Strategies tried      : 1
% 1.65/1.13  
% 1.65/1.13  Timing (in seconds)
% 1.65/1.13  ----------------------
% 1.65/1.13  Preprocessing        : 0.27
% 1.65/1.13  Parsing              : 0.15
% 1.65/1.13  CNF conversion       : 0.02
% 1.65/1.13  Main loop            : 0.11
% 1.65/1.13  Inferencing          : 0.04
% 1.65/1.13  Reduction            : 0.03
% 1.65/1.13  Demodulation         : 0.02
% 1.65/1.13  BG Simplification    : 0.01
% 1.65/1.13  Subsumption          : 0.02
% 1.65/1.13  Abstraction          : 0.00
% 1.65/1.13  MUC search           : 0.00
% 1.65/1.13  Cooper               : 0.00
% 1.65/1.13  Total                : 0.41
% 1.65/1.13  Index Insertion      : 0.00
% 1.65/1.13  Index Deletion       : 0.00
% 1.65/1.13  Index Matching       : 0.00
% 1.65/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
