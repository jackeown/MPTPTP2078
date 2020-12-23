%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:12 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   39 (  45 expanded)
%              Number of leaves         :   18 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   50 (  75 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_setfam_1 > r2_hidden > r1_tarski > m1_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( ( v3_setfam_1(B,A)
                & r1_tarski(C,B) )
             => v3_setfam_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_setfam_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v3_setfam_1(B,A)
      <=> ~ r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_setfam_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_14,plain,(
    ~ v3_setfam_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_79,plain,(
    ! [B_28,A_29] :
      ( v3_setfam_1(B_28,A_29)
      | r2_hidden(A_29,B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(k1_zfmisc_1(A_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_85,plain,
    ( v3_setfam_1('#skF_3','#skF_1')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_79])).

tff(c_90,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_85])).

tff(c_16,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_33,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(k1_tarski(A_15),B_16)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_47,plain,(
    ! [A_21,B_22] :
      ( k2_xboole_0(k1_tarski(A_21),B_22) = B_22
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(resolution,[status(thm)],[c_33,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_59,plain,(
    ! [A_23,C_24,B_25] :
      ( r1_tarski(k1_tarski(A_23),C_24)
      | ~ r1_tarski(B_25,C_24)
      | ~ r2_hidden(A_23,B_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_2])).

tff(c_66,plain,(
    ! [A_26] :
      ( r1_tarski(k1_tarski(A_26),'#skF_2')
      | ~ r2_hidden(A_26,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_16,c_59])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | ~ r1_tarski(k1_tarski(A_6),B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_77,plain,(
    ! [A_26] :
      ( r2_hidden(A_26,'#skF_2')
      | ~ r2_hidden(A_26,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_66,c_6])).

tff(c_18,plain,(
    v3_setfam_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_139,plain,(
    ! [A_38,B_39] :
      ( ~ r2_hidden(A_38,B_39)
      | ~ v3_setfam_1(B_39,A_38)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k1_zfmisc_1(A_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_142,plain,
    ( ~ r2_hidden('#skF_1','#skF_2')
    | ~ v3_setfam_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_139])).

tff(c_148,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_142])).

tff(c_157,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_77,c_148])).

tff(c_162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_157])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:12:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.14  
% 1.67/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.14  %$ v3_setfam_1 > r2_hidden > r1_tarski > m1_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.67/1.14  
% 1.67/1.14  %Foreground sorts:
% 1.67/1.14  
% 1.67/1.14  
% 1.67/1.14  %Background operators:
% 1.67/1.14  
% 1.67/1.14  
% 1.67/1.14  %Foreground operators:
% 1.67/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.67/1.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.67/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.67/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.67/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.67/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.14  tff(v3_setfam_1, type, v3_setfam_1: ($i * $i) > $o).
% 1.67/1.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.67/1.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.67/1.14  
% 1.86/1.16  tff(f_56, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((v3_setfam_1(B, A) & r1_tarski(C, B)) => v3_setfam_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_setfam_1)).
% 1.86/1.16  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v3_setfam_1(B, A) <=> ~r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_setfam_1)).
% 1.86/1.16  tff(f_37, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.86/1.16  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.86/1.16  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.86/1.16  tff(c_14, plain, (~v3_setfam_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.86/1.16  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.86/1.16  tff(c_79, plain, (![B_28, A_29]: (v3_setfam_1(B_28, A_29) | r2_hidden(A_29, B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(k1_zfmisc_1(A_29))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.86/1.16  tff(c_85, plain, (v3_setfam_1('#skF_3', '#skF_1') | r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_79])).
% 1.86/1.16  tff(c_90, plain, (r2_hidden('#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_14, c_85])).
% 1.86/1.16  tff(c_16, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.86/1.16  tff(c_33, plain, (![A_15, B_16]: (r1_tarski(k1_tarski(A_15), B_16) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.86/1.16  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.86/1.16  tff(c_47, plain, (![A_21, B_22]: (k2_xboole_0(k1_tarski(A_21), B_22)=B_22 | ~r2_hidden(A_21, B_22))), inference(resolution, [status(thm)], [c_33, c_4])).
% 1.86/1.16  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.86/1.16  tff(c_59, plain, (![A_23, C_24, B_25]: (r1_tarski(k1_tarski(A_23), C_24) | ~r1_tarski(B_25, C_24) | ~r2_hidden(A_23, B_25))), inference(superposition, [status(thm), theory('equality')], [c_47, c_2])).
% 1.86/1.16  tff(c_66, plain, (![A_26]: (r1_tarski(k1_tarski(A_26), '#skF_2') | ~r2_hidden(A_26, '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_59])).
% 1.86/1.16  tff(c_6, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | ~r1_tarski(k1_tarski(A_6), B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.86/1.16  tff(c_77, plain, (![A_26]: (r2_hidden(A_26, '#skF_2') | ~r2_hidden(A_26, '#skF_3'))), inference(resolution, [status(thm)], [c_66, c_6])).
% 1.86/1.16  tff(c_18, plain, (v3_setfam_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.86/1.16  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.86/1.16  tff(c_139, plain, (![A_38, B_39]: (~r2_hidden(A_38, B_39) | ~v3_setfam_1(B_39, A_38) | ~m1_subset_1(B_39, k1_zfmisc_1(k1_zfmisc_1(A_38))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.86/1.16  tff(c_142, plain, (~r2_hidden('#skF_1', '#skF_2') | ~v3_setfam_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_22, c_139])).
% 1.86/1.16  tff(c_148, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_142])).
% 1.86/1.16  tff(c_157, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_77, c_148])).
% 1.86/1.16  tff(c_162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_157])).
% 1.86/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.16  
% 1.86/1.16  Inference rules
% 1.86/1.16  ----------------------
% 1.86/1.16  #Ref     : 0
% 1.86/1.16  #Sup     : 31
% 1.86/1.16  #Fact    : 0
% 1.86/1.16  #Define  : 0
% 1.86/1.16  #Split   : 0
% 1.86/1.16  #Chain   : 0
% 1.86/1.16  #Close   : 0
% 1.86/1.16  
% 1.86/1.16  Ordering : KBO
% 1.86/1.16  
% 1.86/1.16  Simplification rules
% 1.86/1.16  ----------------------
% 1.86/1.16  #Subsume      : 2
% 1.86/1.16  #Demod        : 4
% 1.86/1.16  #Tautology    : 10
% 1.86/1.16  #SimpNegUnit  : 1
% 1.86/1.16  #BackRed      : 0
% 1.86/1.16  
% 1.86/1.16  #Partial instantiations: 0
% 1.86/1.16  #Strategies tried      : 1
% 1.86/1.16  
% 1.86/1.16  Timing (in seconds)
% 1.86/1.16  ----------------------
% 1.86/1.16  Preprocessing        : 0.25
% 1.86/1.16  Parsing              : 0.14
% 1.86/1.16  CNF conversion       : 0.02
% 1.86/1.16  Main loop            : 0.16
% 1.86/1.16  Inferencing          : 0.07
% 1.86/1.16  Reduction            : 0.04
% 1.86/1.16  Demodulation         : 0.03
% 1.86/1.16  BG Simplification    : 0.01
% 1.86/1.16  Subsumption          : 0.03
% 1.86/1.16  Abstraction          : 0.01
% 1.86/1.16  MUC search           : 0.00
% 1.86/1.16  Cooper               : 0.00
% 1.86/1.16  Total                : 0.44
% 1.86/1.16  Index Insertion      : 0.00
% 1.86/1.16  Index Deletion       : 0.00
% 1.86/1.16  Index Matching       : 0.00
% 1.86/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
