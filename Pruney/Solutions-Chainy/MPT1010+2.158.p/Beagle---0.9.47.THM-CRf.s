%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:26 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   43 (  47 expanded)
%              Number of leaves         :   27 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   46 (  66 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_26,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_45,plain,(
    ! [A_22,B_23] : k2_xboole_0(k1_tarski(A_22),B_23) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_49,plain,(
    ! [A_22] : k1_tarski(A_22) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_45])).

tff(c_34,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_32,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_30,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_28,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_122,plain,(
    ! [D_45,C_46,B_47,A_48] :
      ( r2_hidden(k1_funct_1(D_45,C_46),B_47)
      | k1_xboole_0 = B_47
      | ~ r2_hidden(C_46,A_48)
      | ~ m1_subset_1(D_45,k1_zfmisc_1(k2_zfmisc_1(A_48,B_47)))
      | ~ v1_funct_2(D_45,A_48,B_47)
      | ~ v1_funct_1(D_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_135,plain,(
    ! [D_49,B_50] :
      ( r2_hidden(k1_funct_1(D_49,'#skF_5'),B_50)
      | k1_xboole_0 = B_50
      | ~ m1_subset_1(D_49,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_50)))
      | ~ v1_funct_2(D_49,'#skF_3',B_50)
      | ~ v1_funct_1(D_49) ) ),
    inference(resolution,[status(thm)],[c_28,c_122])).

tff(c_138,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_30,c_135])).

tff(c_141,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_138])).

tff(c_142,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_141])).

tff(c_4,plain,(
    ! [C_7,A_3] :
      ( C_7 = A_3
      | ~ r2_hidden(C_7,k1_tarski(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_147,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_142,c_4])).

tff(c_152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_147])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:24:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.22  
% 1.89/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.22  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.89/1.22  
% 1.89/1.22  %Foreground sorts:
% 1.89/1.22  
% 1.89/1.22  
% 1.89/1.22  %Background operators:
% 1.89/1.22  
% 1.89/1.22  
% 1.89/1.22  %Foreground operators:
% 1.89/1.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.89/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.89/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.89/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.89/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.89/1.22  tff('#skF_5', type, '#skF_5': $i).
% 1.89/1.22  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.89/1.22  tff('#skF_6', type, '#skF_6': $i).
% 1.89/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.89/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.89/1.22  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.89/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.89/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.89/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.89/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.89/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.89/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.89/1.22  
% 1.89/1.23  tff(f_66, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 1.89/1.23  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 1.89/1.23  tff(f_43, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.89/1.23  tff(f_55, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 1.89/1.23  tff(f_34, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.89/1.23  tff(c_26, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.89/1.23  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.89/1.23  tff(c_45, plain, (![A_22, B_23]: (k2_xboole_0(k1_tarski(A_22), B_23)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.89/1.23  tff(c_49, plain, (![A_22]: (k1_tarski(A_22)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_45])).
% 1.89/1.23  tff(c_34, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.89/1.23  tff(c_32, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.89/1.23  tff(c_30, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.89/1.23  tff(c_28, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.89/1.23  tff(c_122, plain, (![D_45, C_46, B_47, A_48]: (r2_hidden(k1_funct_1(D_45, C_46), B_47) | k1_xboole_0=B_47 | ~r2_hidden(C_46, A_48) | ~m1_subset_1(D_45, k1_zfmisc_1(k2_zfmisc_1(A_48, B_47))) | ~v1_funct_2(D_45, A_48, B_47) | ~v1_funct_1(D_45))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.89/1.23  tff(c_135, plain, (![D_49, B_50]: (r2_hidden(k1_funct_1(D_49, '#skF_5'), B_50) | k1_xboole_0=B_50 | ~m1_subset_1(D_49, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_50))) | ~v1_funct_2(D_49, '#skF_3', B_50) | ~v1_funct_1(D_49))), inference(resolution, [status(thm)], [c_28, c_122])).
% 1.89/1.23  tff(c_138, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_30, c_135])).
% 1.89/1.23  tff(c_141, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_138])).
% 1.89/1.23  tff(c_142, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_49, c_141])).
% 1.89/1.23  tff(c_4, plain, (![C_7, A_3]: (C_7=A_3 | ~r2_hidden(C_7, k1_tarski(A_3)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.89/1.23  tff(c_147, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_142, c_4])).
% 1.89/1.23  tff(c_152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_147])).
% 1.89/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.23  
% 1.89/1.23  Inference rules
% 1.89/1.23  ----------------------
% 1.89/1.23  #Ref     : 0
% 1.89/1.23  #Sup     : 24
% 1.89/1.23  #Fact    : 0
% 1.89/1.23  #Define  : 0
% 1.89/1.23  #Split   : 0
% 1.89/1.23  #Chain   : 0
% 1.89/1.23  #Close   : 0
% 1.89/1.23  
% 1.89/1.23  Ordering : KBO
% 1.89/1.23  
% 1.89/1.23  Simplification rules
% 1.89/1.23  ----------------------
% 1.89/1.23  #Subsume      : 0
% 1.89/1.23  #Demod        : 4
% 1.89/1.23  #Tautology    : 14
% 1.89/1.23  #SimpNegUnit  : 2
% 1.89/1.23  #BackRed      : 0
% 1.89/1.23  
% 1.89/1.23  #Partial instantiations: 0
% 1.89/1.23  #Strategies tried      : 1
% 1.89/1.23  
% 1.89/1.23  Timing (in seconds)
% 1.89/1.23  ----------------------
% 1.89/1.23  Preprocessing        : 0.30
% 1.89/1.23  Parsing              : 0.15
% 1.89/1.23  CNF conversion       : 0.02
% 1.89/1.23  Main loop            : 0.15
% 1.89/1.23  Inferencing          : 0.05
% 1.89/1.23  Reduction            : 0.04
% 1.89/1.23  Demodulation         : 0.03
% 1.89/1.23  BG Simplification    : 0.01
% 1.89/1.23  Subsumption          : 0.03
% 1.89/1.23  Abstraction          : 0.01
% 1.89/1.23  MUC search           : 0.00
% 1.89/1.23  Cooper               : 0.00
% 1.89/1.23  Total                : 0.47
% 1.89/1.23  Index Insertion      : 0.00
% 1.89/1.23  Index Deletion       : 0.00
% 1.89/1.23  Index Matching       : 0.00
% 1.89/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
