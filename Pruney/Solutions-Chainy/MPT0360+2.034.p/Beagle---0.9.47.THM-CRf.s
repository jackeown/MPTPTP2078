%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:23 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   40 (  43 expanded)
%              Number of leaves         :   23 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   44 (  56 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_39,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_14,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_18,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_39,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(A_24,B_25) = k3_subset_1(A_24,B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_43,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_39])).

tff(c_34,plain,(
    ! [A_21,C_22,B_23] :
      ( r1_xboole_0(A_21,k4_xboole_0(C_22,B_23))
      | ~ r1_tarski(A_21,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( ~ r1_xboole_0(B_8,A_7)
      | ~ r1_tarski(B_8,A_7)
      | v1_xboole_0(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_56,plain,(
    ! [A_27,C_28,B_29] :
      ( ~ r1_tarski(A_27,k4_xboole_0(C_28,B_29))
      | v1_xboole_0(A_27)
      | ~ r1_tarski(A_27,B_29) ) ),
    inference(resolution,[status(thm)],[c_34,c_8])).

tff(c_60,plain,(
    ! [A_30] :
      ( ~ r1_tarski(A_30,k3_subset_1('#skF_3','#skF_5'))
      | v1_xboole_0(A_30)
      | ~ r1_tarski(A_30,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_56])).

tff(c_63,plain,
    ( v1_xboole_0('#skF_4')
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_60])).

tff(c_66,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_63])).

tff(c_22,plain,(
    ! [A_16] :
      ( r2_hidden('#skF_2'(A_16),A_16)
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [A_16] :
      ( ~ v1_xboole_0(A_16)
      | k1_xboole_0 = A_16 ) ),
    inference(resolution,[status(thm)],[c_22,c_2])).

tff(c_69,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_66,c_26])).

tff(c_73,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_69])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:20:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.11  
% 1.67/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.11  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 1.67/1.11  
% 1.67/1.11  %Foreground sorts:
% 1.67/1.11  
% 1.67/1.11  
% 1.67/1.11  %Background operators:
% 1.67/1.11  
% 1.67/1.11  
% 1.67/1.11  %Foreground operators:
% 1.67/1.11  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.67/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.67/1.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.67/1.11  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.67/1.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.67/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.67/1.11  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.67/1.11  tff('#skF_5', type, '#skF_5': $i).
% 1.67/1.11  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.67/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.67/1.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.67/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.11  tff('#skF_4', type, '#skF_4': $i).
% 1.67/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.11  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.67/1.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.67/1.11  
% 1.67/1.12  tff(f_64, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 1.67/1.12  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 1.67/1.12  tff(f_51, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 1.67/1.12  tff(f_47, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 1.67/1.12  tff(f_39, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.67/1.12  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.67/1.12  tff(c_14, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.67/1.12  tff(c_18, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.67/1.12  tff(c_16, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.67/1.12  tff(c_20, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.67/1.12  tff(c_39, plain, (![A_24, B_25]: (k4_xboole_0(A_24, B_25)=k3_subset_1(A_24, B_25) | ~m1_subset_1(B_25, k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.67/1.12  tff(c_43, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_20, c_39])).
% 1.67/1.12  tff(c_34, plain, (![A_21, C_22, B_23]: (r1_xboole_0(A_21, k4_xboole_0(C_22, B_23)) | ~r1_tarski(A_21, B_23))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.67/1.12  tff(c_8, plain, (![B_8, A_7]: (~r1_xboole_0(B_8, A_7) | ~r1_tarski(B_8, A_7) | v1_xboole_0(B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.67/1.12  tff(c_56, plain, (![A_27, C_28, B_29]: (~r1_tarski(A_27, k4_xboole_0(C_28, B_29)) | v1_xboole_0(A_27) | ~r1_tarski(A_27, B_29))), inference(resolution, [status(thm)], [c_34, c_8])).
% 1.67/1.12  tff(c_60, plain, (![A_30]: (~r1_tarski(A_30, k3_subset_1('#skF_3', '#skF_5')) | v1_xboole_0(A_30) | ~r1_tarski(A_30, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_43, c_56])).
% 1.67/1.12  tff(c_63, plain, (v1_xboole_0('#skF_4') | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_16, c_60])).
% 1.67/1.12  tff(c_66, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_63])).
% 1.67/1.12  tff(c_22, plain, (![A_16]: (r2_hidden('#skF_2'(A_16), A_16) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.67/1.12  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.67/1.12  tff(c_26, plain, (![A_16]: (~v1_xboole_0(A_16) | k1_xboole_0=A_16)), inference(resolution, [status(thm)], [c_22, c_2])).
% 1.67/1.12  tff(c_69, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_66, c_26])).
% 1.67/1.12  tff(c_73, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_69])).
% 1.67/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.12  
% 1.67/1.12  Inference rules
% 1.67/1.12  ----------------------
% 1.67/1.12  #Ref     : 0
% 1.67/1.12  #Sup     : 11
% 1.67/1.12  #Fact    : 0
% 1.67/1.12  #Define  : 0
% 1.67/1.12  #Split   : 0
% 1.67/1.12  #Chain   : 0
% 1.67/1.12  #Close   : 0
% 1.67/1.12  
% 1.67/1.12  Ordering : KBO
% 1.67/1.12  
% 1.67/1.12  Simplification rules
% 1.67/1.12  ----------------------
% 1.67/1.12  #Subsume      : 0
% 1.67/1.12  #Demod        : 1
% 1.67/1.12  #Tautology    : 3
% 1.67/1.12  #SimpNegUnit  : 1
% 1.67/1.12  #BackRed      : 0
% 1.67/1.12  
% 1.67/1.12  #Partial instantiations: 0
% 1.67/1.12  #Strategies tried      : 1
% 1.67/1.12  
% 1.67/1.12  Timing (in seconds)
% 1.67/1.12  ----------------------
% 1.67/1.12  Preprocessing        : 0.27
% 1.67/1.12  Parsing              : 0.15
% 1.67/1.12  CNF conversion       : 0.02
% 1.67/1.12  Main loop            : 0.09
% 1.67/1.12  Inferencing          : 0.04
% 1.67/1.12  Reduction            : 0.02
% 1.67/1.12  Demodulation         : 0.02
% 1.67/1.12  BG Simplification    : 0.01
% 1.67/1.12  Subsumption          : 0.01
% 1.67/1.12  Abstraction          : 0.00
% 1.67/1.12  MUC search           : 0.00
% 1.67/1.12  Cooper               : 0.00
% 1.67/1.12  Total                : 0.39
% 1.67/1.12  Index Insertion      : 0.00
% 1.67/1.12  Index Deletion       : 0.00
% 1.67/1.12  Index Matching       : 0.00
% 1.67/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
