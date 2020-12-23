%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:11 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   42 (  59 expanded)
%              Number of leaves         :   18 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   66 ( 120 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_setfam_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v3_setfam_1,type,(
    v3_setfam_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,negated_conjecture,(
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

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(c_24,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_22,plain,(
    ~ v3_setfam_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_125,plain,(
    ! [B_40,A_41] :
      ( v3_setfam_1(B_40,A_41)
      | r2_hidden(A_41,B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(k1_zfmisc_1(A_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_139,plain,
    ( v3_setfam_1('#skF_3','#skF_1')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_125])).

tff(c_146,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_139])).

tff(c_16,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_77,plain,(
    ! [C_30,B_31,A_32] :
      ( ~ v1_xboole_0(C_30)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(C_30))
      | ~ r2_hidden(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_87,plain,(
    ! [B_6,A_32,A_5] :
      ( ~ v1_xboole_0(B_6)
      | ~ r2_hidden(A_32,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_16,c_77])).

tff(c_154,plain,(
    ! [B_42] :
      ( ~ v1_xboole_0(B_42)
      | ~ r1_tarski('#skF_3',B_42) ) ),
    inference(resolution,[status(thm)],[c_146,c_87])).

tff(c_162,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_154])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r2_hidden(B_2,A_1)
      | ~ m1_subset_1(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_26,plain,(
    v3_setfam_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_198,plain,(
    ! [A_46,B_47] :
      ( ~ r2_hidden(A_46,B_47)
      | ~ v3_setfam_1(B_47,A_46)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(k1_zfmisc_1(A_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_209,plain,
    ( ~ r2_hidden('#skF_1','#skF_2')
    | ~ v3_setfam_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_198])).

tff(c_217,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_209])).

tff(c_223,plain,
    ( ~ m1_subset_1('#skF_1','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_217])).

tff(c_226,plain,(
    ~ m1_subset_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_223])).

tff(c_96,plain,(
    ! [A_36,C_37,B_38] :
      ( m1_subset_1(A_36,C_37)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(C_37))
      | ~ r2_hidden(A_36,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_238,plain,(
    ! [A_49,B_50,A_51] :
      ( m1_subset_1(A_49,B_50)
      | ~ r2_hidden(A_49,A_51)
      | ~ r1_tarski(A_51,B_50) ) ),
    inference(resolution,[status(thm)],[c_16,c_96])).

tff(c_245,plain,(
    ! [B_52] :
      ( m1_subset_1('#skF_1',B_52)
      | ~ r1_tarski('#skF_3',B_52) ) ),
    inference(resolution,[status(thm)],[c_146,c_238])).

tff(c_255,plain,(
    m1_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_245])).

tff(c_261,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_226,c_255])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:25:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.29  
% 2.06/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.30  %$ v3_setfam_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.06/1.30  
% 2.06/1.30  %Foreground sorts:
% 2.06/1.30  
% 2.06/1.30  
% 2.06/1.30  %Background operators:
% 2.06/1.30  
% 2.06/1.30  
% 2.06/1.30  %Foreground operators:
% 2.06/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.06/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.06/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.30  tff(v3_setfam_1, type, v3_setfam_1: ($i * $i) > $o).
% 2.06/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.06/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.06/1.30  
% 2.06/1.31  tff(f_74, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((v3_setfam_1(B, A) & r1_tarski(C, B)) => v3_setfam_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_setfam_1)).
% 2.06/1.31  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v3_setfam_1(B, A) <=> ~r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_setfam_1)).
% 2.06/1.31  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.06/1.31  tff(f_62, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.06/1.31  tff(f_38, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.06/1.31  tff(f_55, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.06/1.31  tff(c_24, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.06/1.31  tff(c_22, plain, (~v3_setfam_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.06/1.31  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.06/1.31  tff(c_125, plain, (![B_40, A_41]: (v3_setfam_1(B_40, A_41) | r2_hidden(A_41, B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(k1_zfmisc_1(A_41))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.06/1.31  tff(c_139, plain, (v3_setfam_1('#skF_3', '#skF_1') | r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_125])).
% 2.06/1.31  tff(c_146, plain, (r2_hidden('#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_22, c_139])).
% 2.06/1.31  tff(c_16, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.06/1.31  tff(c_77, plain, (![C_30, B_31, A_32]: (~v1_xboole_0(C_30) | ~m1_subset_1(B_31, k1_zfmisc_1(C_30)) | ~r2_hidden(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.06/1.31  tff(c_87, plain, (![B_6, A_32, A_5]: (~v1_xboole_0(B_6) | ~r2_hidden(A_32, A_5) | ~r1_tarski(A_5, B_6))), inference(resolution, [status(thm)], [c_16, c_77])).
% 2.06/1.31  tff(c_154, plain, (![B_42]: (~v1_xboole_0(B_42) | ~r1_tarski('#skF_3', B_42))), inference(resolution, [status(thm)], [c_146, c_87])).
% 2.06/1.31  tff(c_162, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_24, c_154])).
% 2.06/1.31  tff(c_4, plain, (![B_2, A_1]: (r2_hidden(B_2, A_1) | ~m1_subset_1(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.06/1.31  tff(c_26, plain, (v3_setfam_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.06/1.31  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.06/1.31  tff(c_198, plain, (![A_46, B_47]: (~r2_hidden(A_46, B_47) | ~v3_setfam_1(B_47, A_46) | ~m1_subset_1(B_47, k1_zfmisc_1(k1_zfmisc_1(A_46))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.06/1.31  tff(c_209, plain, (~r2_hidden('#skF_1', '#skF_2') | ~v3_setfam_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_198])).
% 2.06/1.31  tff(c_217, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_209])).
% 2.06/1.31  tff(c_223, plain, (~m1_subset_1('#skF_1', '#skF_2') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_4, c_217])).
% 2.06/1.31  tff(c_226, plain, (~m1_subset_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_162, c_223])).
% 2.06/1.31  tff(c_96, plain, (![A_36, C_37, B_38]: (m1_subset_1(A_36, C_37) | ~m1_subset_1(B_38, k1_zfmisc_1(C_37)) | ~r2_hidden(A_36, B_38))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.06/1.31  tff(c_238, plain, (![A_49, B_50, A_51]: (m1_subset_1(A_49, B_50) | ~r2_hidden(A_49, A_51) | ~r1_tarski(A_51, B_50))), inference(resolution, [status(thm)], [c_16, c_96])).
% 2.06/1.31  tff(c_245, plain, (![B_52]: (m1_subset_1('#skF_1', B_52) | ~r1_tarski('#skF_3', B_52))), inference(resolution, [status(thm)], [c_146, c_238])).
% 2.06/1.31  tff(c_255, plain, (m1_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_245])).
% 2.06/1.31  tff(c_261, plain, $false, inference(negUnitSimplification, [status(thm)], [c_226, c_255])).
% 2.06/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.31  
% 2.06/1.31  Inference rules
% 2.06/1.31  ----------------------
% 2.06/1.31  #Ref     : 0
% 2.06/1.31  #Sup     : 49
% 2.06/1.31  #Fact    : 0
% 2.06/1.31  #Define  : 0
% 2.06/1.31  #Split   : 4
% 2.06/1.31  #Chain   : 0
% 2.06/1.31  #Close   : 0
% 2.06/1.31  
% 2.06/1.31  Ordering : KBO
% 2.06/1.31  
% 2.06/1.31  Simplification rules
% 2.06/1.31  ----------------------
% 2.06/1.31  #Subsume      : 9
% 2.06/1.31  #Demod        : 4
% 2.06/1.31  #Tautology    : 5
% 2.06/1.31  #SimpNegUnit  : 4
% 2.06/1.31  #BackRed      : 0
% 2.06/1.31  
% 2.06/1.31  #Partial instantiations: 0
% 2.06/1.31  #Strategies tried      : 1
% 2.06/1.31  
% 2.06/1.31  Timing (in seconds)
% 2.06/1.31  ----------------------
% 2.06/1.31  Preprocessing        : 0.30
% 2.06/1.31  Parsing              : 0.17
% 2.06/1.31  CNF conversion       : 0.02
% 2.06/1.31  Main loop            : 0.21
% 2.06/1.31  Inferencing          : 0.09
% 2.06/1.31  Reduction            : 0.05
% 2.06/1.31  Demodulation         : 0.04
% 2.06/1.31  BG Simplification    : 0.01
% 2.06/1.31  Subsumption          : 0.03
% 2.06/1.31  Abstraction          : 0.01
% 2.06/1.31  MUC search           : 0.00
% 2.06/1.31  Cooper               : 0.00
% 2.06/1.31  Total                : 0.54
% 2.06/1.31  Index Insertion      : 0.00
% 2.06/1.31  Index Deletion       : 0.00
% 2.06/1.31  Index Matching       : 0.00
% 2.06/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
