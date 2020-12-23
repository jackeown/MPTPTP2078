%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:25 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   47 (  58 expanded)
%              Number of leaves         :   26 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   50 (  81 expanded)
%              Number of equality atoms :   16 (  26 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_52,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_38,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_5'(A_13),A_13)
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_50,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_54,plain,(
    ! [A_22,B_23] :
      ( k3_xboole_0(A_22,B_23) = A_22
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_62,plain,(
    k3_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_50,c_54])).

tff(c_108,plain,(
    ! [D_32,B_33,A_34] :
      ( r2_hidden(D_32,B_33)
      | ~ r2_hidden(D_32,k3_xboole_0(A_34,B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_120,plain,(
    ! [D_35] :
      ( r2_hidden(D_35,'#skF_8')
      | ~ r2_hidden(D_35,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_108])).

tff(c_124,plain,
    ( r2_hidden('#skF_5'('#skF_7'),'#skF_8')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_38,c_120])).

tff(c_127,plain,(
    r2_hidden('#skF_5'('#skF_7'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_124])).

tff(c_48,plain,(
    r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_61,plain,(
    k3_xboole_0('#skF_7',k3_subset_1('#skF_6','#skF_8')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_48,c_54])).

tff(c_111,plain,(
    ! [D_32] :
      ( r2_hidden(D_32,k3_subset_1('#skF_6','#skF_8'))
      | ~ r2_hidden(D_32,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_108])).

tff(c_52,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_146,plain,(
    ! [A_40,B_41] :
      ( k4_xboole_0(A_40,B_41) = k3_subset_1(A_40,B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_150,plain,(
    k4_xboole_0('#skF_6','#skF_8') = k3_subset_1('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_52,c_146])).

tff(c_22,plain,(
    ! [D_12,B_8,A_7] :
      ( ~ r2_hidden(D_12,B_8)
      | ~ r2_hidden(D_12,k4_xboole_0(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_179,plain,(
    ! [D_44] :
      ( ~ r2_hidden(D_44,'#skF_8')
      | ~ r2_hidden(D_44,k3_subset_1('#skF_6','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_22])).

tff(c_189,plain,(
    ! [D_45] :
      ( ~ r2_hidden(D_45,'#skF_8')
      | ~ r2_hidden(D_45,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_111,c_179])).

tff(c_193,plain,
    ( ~ r2_hidden('#skF_5'('#skF_7'),'#skF_8')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_38,c_189])).

tff(c_196,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_193])).

tff(c_198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_196])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n022.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 16:42:26 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.28  
% 2.05/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.28  %$ r2_hidden > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3
% 2.05/1.28  
% 2.05/1.28  %Foreground sorts:
% 2.05/1.28  
% 2.05/1.28  
% 2.05/1.28  %Background operators:
% 2.05/1.28  
% 2.05/1.28  
% 2.05/1.28  %Foreground operators:
% 2.05/1.28  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.05/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.05/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.05/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.05/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.05/1.28  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.05/1.28  tff('#skF_7', type, '#skF_7': $i).
% 2.05/1.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.05/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.28  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.05/1.28  tff('#skF_6', type, '#skF_6': $i).
% 2.05/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.05/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.05/1.28  tff('#skF_8', type, '#skF_8': $i).
% 2.05/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.28  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.05/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.05/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.05/1.28  
% 2.05/1.29  tff(f_71, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 2.05/1.29  tff(f_52, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.05/1.29  tff(f_58, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.05/1.29  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.05/1.29  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.05/1.29  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.05/1.29  tff(c_46, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.05/1.29  tff(c_38, plain, (![A_13]: (r2_hidden('#skF_5'(A_13), A_13) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.05/1.29  tff(c_50, plain, (r1_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.05/1.29  tff(c_54, plain, (![A_22, B_23]: (k3_xboole_0(A_22, B_23)=A_22 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.05/1.29  tff(c_62, plain, (k3_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_50, c_54])).
% 2.05/1.29  tff(c_108, plain, (![D_32, B_33, A_34]: (r2_hidden(D_32, B_33) | ~r2_hidden(D_32, k3_xboole_0(A_34, B_33)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.05/1.29  tff(c_120, plain, (![D_35]: (r2_hidden(D_35, '#skF_8') | ~r2_hidden(D_35, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_108])).
% 2.05/1.29  tff(c_124, plain, (r2_hidden('#skF_5'('#skF_7'), '#skF_8') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_38, c_120])).
% 2.05/1.29  tff(c_127, plain, (r2_hidden('#skF_5'('#skF_7'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_46, c_124])).
% 2.05/1.29  tff(c_48, plain, (r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.05/1.29  tff(c_61, plain, (k3_xboole_0('#skF_7', k3_subset_1('#skF_6', '#skF_8'))='#skF_7'), inference(resolution, [status(thm)], [c_48, c_54])).
% 2.05/1.29  tff(c_111, plain, (![D_32]: (r2_hidden(D_32, k3_subset_1('#skF_6', '#skF_8')) | ~r2_hidden(D_32, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_108])).
% 2.05/1.29  tff(c_52, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.05/1.29  tff(c_146, plain, (![A_40, B_41]: (k4_xboole_0(A_40, B_41)=k3_subset_1(A_40, B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.05/1.29  tff(c_150, plain, (k4_xboole_0('#skF_6', '#skF_8')=k3_subset_1('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_52, c_146])).
% 2.05/1.29  tff(c_22, plain, (![D_12, B_8, A_7]: (~r2_hidden(D_12, B_8) | ~r2_hidden(D_12, k4_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.05/1.29  tff(c_179, plain, (![D_44]: (~r2_hidden(D_44, '#skF_8') | ~r2_hidden(D_44, k3_subset_1('#skF_6', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_150, c_22])).
% 2.05/1.29  tff(c_189, plain, (![D_45]: (~r2_hidden(D_45, '#skF_8') | ~r2_hidden(D_45, '#skF_7'))), inference(resolution, [status(thm)], [c_111, c_179])).
% 2.05/1.29  tff(c_193, plain, (~r2_hidden('#skF_5'('#skF_7'), '#skF_8') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_38, c_189])).
% 2.05/1.29  tff(c_196, plain, (k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_127, c_193])).
% 2.05/1.29  tff(c_198, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_196])).
% 2.05/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.29  
% 2.05/1.29  Inference rules
% 2.05/1.29  ----------------------
% 2.05/1.29  #Ref     : 0
% 2.05/1.29  #Sup     : 36
% 2.05/1.29  #Fact    : 0
% 2.05/1.29  #Define  : 0
% 2.05/1.29  #Split   : 0
% 2.05/1.29  #Chain   : 0
% 2.05/1.29  #Close   : 0
% 2.05/1.29  
% 2.05/1.29  Ordering : KBO
% 2.05/1.29  
% 2.05/1.29  Simplification rules
% 2.05/1.29  ----------------------
% 2.05/1.29  #Subsume      : 1
% 2.05/1.29  #Demod        : 2
% 2.05/1.29  #Tautology    : 14
% 2.05/1.29  #SimpNegUnit  : 3
% 2.05/1.29  #BackRed      : 0
% 2.05/1.29  
% 2.05/1.29  #Partial instantiations: 0
% 2.05/1.29  #Strategies tried      : 1
% 2.05/1.29  
% 2.05/1.29  Timing (in seconds)
% 2.05/1.29  ----------------------
% 2.05/1.29  Preprocessing        : 0.33
% 2.05/1.29  Parsing              : 0.16
% 2.05/1.29  CNF conversion       : 0.03
% 2.05/1.29  Main loop            : 0.15
% 2.05/1.29  Inferencing          : 0.05
% 2.05/1.30  Reduction            : 0.04
% 2.05/1.30  Demodulation         : 0.03
% 2.05/1.30  BG Simplification    : 0.01
% 2.05/1.30  Subsumption          : 0.03
% 2.05/1.30  Abstraction          : 0.01
% 2.05/1.30  MUC search           : 0.00
% 2.05/1.30  Cooper               : 0.00
% 2.05/1.30  Total                : 0.50
% 2.05/1.30  Index Insertion      : 0.00
% 2.05/1.30  Index Deletion       : 0.00
% 2.05/1.30  Index Matching       : 0.00
% 2.05/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
