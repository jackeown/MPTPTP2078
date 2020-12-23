%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:43 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   42 (  61 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   64 ( 126 expanded)
%              Number of equality atoms :    6 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_xboole_0 > r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ( r1_xboole_0(B,C)
                & r1_xboole_0(k3_subset_1(A,B),k3_subset_1(A,C)) )
             => B = k3_subset_1(A,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,C)
          <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,k3_subset_1(A,C))
          <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_26,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_16,plain,(
    ! [B_10,A_9,C_12] :
      ( r1_tarski(B_10,k3_subset_1(A_9,C_12))
      | ~ r1_xboole_0(B_10,C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_22,plain,(
    k3_subset_1('#skF_1','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(k3_subset_1(A_7,B_8),k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    r1_xboole_0(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_44,plain,(
    r1_xboole_0(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_8])).

tff(c_71,plain,(
    ! [B_37,C_38,A_39] :
      ( r1_tarski(B_37,C_38)
      | ~ r1_xboole_0(B_37,k3_subset_1(A_39,C_38))
      | ~ m1_subset_1(C_38,k1_zfmisc_1(A_39))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_77,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_44,c_71])).

tff(c_84,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_77])).

tff(c_231,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_234,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_12,c_231])).

tff(c_238,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_234])).

tff(c_239,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_49,plain,(
    ! [A_25,B_26] :
      ( r2_xboole_0(A_25,B_26)
      | B_26 = A_25
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [B_6,A_5] :
      ( ~ r2_xboole_0(B_6,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_60,plain,(
    ! [B_26,A_25] :
      ( ~ r1_tarski(B_26,A_25)
      | B_26 = A_25
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(resolution,[status(thm)],[c_49,c_10])).

tff(c_242,plain,
    ( k3_subset_1('#skF_1','#skF_3') = '#skF_2'
    | ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_239,c_60])).

tff(c_245,plain,(
    ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_242])).

tff(c_248,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_16,c_245])).

tff(c_252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_248])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:49:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.27  
% 2.02/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.27  %$ r2_xboole_0 > r1_xboole_0 > r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.02/1.27  
% 2.02/1.27  %Foreground sorts:
% 2.02/1.27  
% 2.02/1.27  
% 2.02/1.27  %Background operators:
% 2.02/1.27  
% 2.02/1.27  
% 2.02/1.27  %Foreground operators:
% 2.02/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.27  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.02/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.02/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.02/1.27  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.02/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.02/1.27  
% 2.02/1.28  tff(f_75, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_xboole_0(B, C) & r1_xboole_0(k3_subset_1(A, B), k3_subset_1(A, C))) => (B = k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_subset_1)).
% 2.02/1.28  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_subset_1)).
% 2.02/1.28  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.02/1.28  tff(f_36, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.02/1.28  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_subset_1)).
% 2.02/1.28  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.02/1.28  tff(f_41, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_xboole_1)).
% 2.02/1.28  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.02/1.28  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.02/1.28  tff(c_26, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.02/1.28  tff(c_16, plain, (![B_10, A_9, C_12]: (r1_tarski(B_10, k3_subset_1(A_9, C_12)) | ~r1_xboole_0(B_10, C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.02/1.28  tff(c_22, plain, (k3_subset_1('#skF_1', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.02/1.28  tff(c_12, plain, (![A_7, B_8]: (m1_subset_1(k3_subset_1(A_7, B_8), k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.02/1.28  tff(c_24, plain, (r1_xboole_0(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.02/1.28  tff(c_8, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.02/1.28  tff(c_44, plain, (r1_xboole_0(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_8])).
% 2.02/1.28  tff(c_71, plain, (![B_37, C_38, A_39]: (r1_tarski(B_37, C_38) | ~r1_xboole_0(B_37, k3_subset_1(A_39, C_38)) | ~m1_subset_1(C_38, k1_zfmisc_1(A_39)) | ~m1_subset_1(B_37, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.02/1.28  tff(c_77, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_71])).
% 2.02/1.28  tff(c_84, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_2') | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_77])).
% 2.02/1.28  tff(c_231, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_84])).
% 2.02/1.28  tff(c_234, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_12, c_231])).
% 2.02/1.28  tff(c_238, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_234])).
% 2.02/1.28  tff(c_239, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_84])).
% 2.02/1.28  tff(c_49, plain, (![A_25, B_26]: (r2_xboole_0(A_25, B_26) | B_26=A_25 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.02/1.28  tff(c_10, plain, (![B_6, A_5]: (~r2_xboole_0(B_6, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.02/1.28  tff(c_60, plain, (![B_26, A_25]: (~r1_tarski(B_26, A_25) | B_26=A_25 | ~r1_tarski(A_25, B_26))), inference(resolution, [status(thm)], [c_49, c_10])).
% 2.02/1.28  tff(c_242, plain, (k3_subset_1('#skF_1', '#skF_3')='#skF_2' | ~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_239, c_60])).
% 2.02/1.28  tff(c_245, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_22, c_242])).
% 2.02/1.28  tff(c_248, plain, (~r1_xboole_0('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_16, c_245])).
% 2.02/1.28  tff(c_252, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_248])).
% 2.02/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.28  
% 2.02/1.28  Inference rules
% 2.02/1.28  ----------------------
% 2.02/1.28  #Ref     : 0
% 2.02/1.28  #Sup     : 40
% 2.02/1.28  #Fact    : 0
% 2.02/1.28  #Define  : 0
% 2.02/1.28  #Split   : 5
% 2.02/1.28  #Chain   : 0
% 2.02/1.28  #Close   : 0
% 2.02/1.28  
% 2.02/1.28  Ordering : KBO
% 2.02/1.28  
% 2.02/1.28  Simplification rules
% 2.02/1.28  ----------------------
% 2.02/1.28  #Subsume      : 0
% 2.02/1.28  #Demod        : 35
% 2.02/1.28  #Tautology    : 17
% 2.02/1.28  #SimpNegUnit  : 2
% 2.02/1.28  #BackRed      : 4
% 2.02/1.28  
% 2.02/1.28  #Partial instantiations: 0
% 2.02/1.28  #Strategies tried      : 1
% 2.02/1.28  
% 2.02/1.29  Timing (in seconds)
% 2.02/1.29  ----------------------
% 2.02/1.29  Preprocessing        : 0.28
% 2.02/1.29  Parsing              : 0.16
% 2.02/1.29  CNF conversion       : 0.02
% 2.02/1.29  Main loop            : 0.20
% 2.02/1.29  Inferencing          : 0.08
% 2.02/1.29  Reduction            : 0.06
% 2.02/1.29  Demodulation         : 0.04
% 2.02/1.29  BG Simplification    : 0.01
% 2.02/1.29  Subsumption          : 0.05
% 2.02/1.29  Abstraction          : 0.01
% 2.02/1.29  MUC search           : 0.00
% 2.02/1.29  Cooper               : 0.00
% 2.02/1.29  Total                : 0.50
% 2.02/1.29  Index Insertion      : 0.00
% 2.02/1.29  Index Deletion       : 0.00
% 2.02/1.29  Index Matching       : 0.00
% 2.02/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
