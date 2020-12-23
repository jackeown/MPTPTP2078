%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:04 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   42 (  53 expanded)
%              Number of leaves         :   24 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  63 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_65,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_39,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(c_32,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_35,plain,(
    ! [B_25,A_26] :
      ( ~ r2_hidden(B_25,A_26)
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_39,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_35])).

tff(c_104,plain,(
    ! [B_39,A_40] :
      ( m1_subset_1(B_39,A_40)
      | ~ r2_hidden(B_39,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_113,plain,
    ( m1_subset_1('#skF_4','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_104])).

tff(c_118,plain,(
    m1_subset_1('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_113])).

tff(c_151,plain,(
    ! [B_48,A_49] :
      ( m1_subset_1(k1_tarski(B_48),k1_zfmisc_1(A_49))
      | k1_xboole_0 = A_49
      | ~ m1_subset_1(B_48,A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_30,plain,(
    ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_157,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_151,c_30])).

tff(c_161,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_157])).

tff(c_24,plain,(
    ! [A_19] : v1_xboole_0('#skF_3'(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_49,plain,(
    ! [A_28] :
      ( r2_hidden('#skF_2'(A_28),A_28)
      | k1_xboole_0 = A_28 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    ! [A_29] :
      ( ~ v1_xboole_0(A_29)
      | k1_xboole_0 = A_29 ) ),
    inference(resolution,[status(thm)],[c_49,c_2])).

tff(c_58,plain,(
    ! [A_19] : '#skF_3'(A_19) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_54])).

tff(c_65,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_24])).

tff(c_174,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_65])).

tff(c_179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_174])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n009.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 19:47:41 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.19  
% 1.91/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.19  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_4 > #skF_3
% 1.91/1.19  
% 1.91/1.19  %Foreground sorts:
% 1.91/1.19  
% 1.91/1.19  
% 1.91/1.19  %Background operators:
% 1.91/1.19  
% 1.91/1.19  
% 1.91/1.19  %Foreground operators:
% 1.91/1.19  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.91/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.91/1.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.91/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.91/1.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.91/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.91/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.91/1.19  tff('#skF_5', type, '#skF_5': $i).
% 1.91/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.91/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.91/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.91/1.19  tff('#skF_3', type, '#skF_3': $i > $i).
% 1.91/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.91/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.91/1.19  
% 1.91/1.20  tff(f_77, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 1.91/1.20  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.91/1.20  tff(f_60, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 1.91/1.20  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 1.91/1.20  tff(f_65, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_subset_1)).
% 1.91/1.20  tff(f_39, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.91/1.20  tff(c_32, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.91/1.20  tff(c_35, plain, (![B_25, A_26]: (~r2_hidden(B_25, A_26) | ~v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.91/1.20  tff(c_39, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_32, c_35])).
% 1.91/1.20  tff(c_104, plain, (![B_39, A_40]: (m1_subset_1(B_39, A_40) | ~r2_hidden(B_39, A_40) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.91/1.20  tff(c_113, plain, (m1_subset_1('#skF_4', '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_32, c_104])).
% 1.91/1.20  tff(c_118, plain, (m1_subset_1('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_39, c_113])).
% 1.91/1.20  tff(c_151, plain, (![B_48, A_49]: (m1_subset_1(k1_tarski(B_48), k1_zfmisc_1(A_49)) | k1_xboole_0=A_49 | ~m1_subset_1(B_48, A_49))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.91/1.20  tff(c_30, plain, (~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.91/1.20  tff(c_157, plain, (k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_151, c_30])).
% 1.91/1.20  tff(c_161, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_157])).
% 1.91/1.20  tff(c_24, plain, (![A_19]: (v1_xboole_0('#skF_3'(A_19)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.91/1.20  tff(c_49, plain, (![A_28]: (r2_hidden('#skF_2'(A_28), A_28) | k1_xboole_0=A_28)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.91/1.20  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.91/1.20  tff(c_54, plain, (![A_29]: (~v1_xboole_0(A_29) | k1_xboole_0=A_29)), inference(resolution, [status(thm)], [c_49, c_2])).
% 1.91/1.20  tff(c_58, plain, (![A_19]: ('#skF_3'(A_19)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_54])).
% 1.91/1.20  tff(c_65, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_24])).
% 1.91/1.20  tff(c_174, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_161, c_65])).
% 1.91/1.20  tff(c_179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39, c_174])).
% 1.91/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.20  
% 1.91/1.20  Inference rules
% 1.91/1.20  ----------------------
% 1.91/1.20  #Ref     : 0
% 1.91/1.20  #Sup     : 28
% 1.91/1.20  #Fact    : 0
% 1.91/1.20  #Define  : 0
% 1.91/1.20  #Split   : 1
% 1.91/1.20  #Chain   : 0
% 1.91/1.20  #Close   : 0
% 1.91/1.20  
% 1.91/1.20  Ordering : KBO
% 1.91/1.20  
% 1.91/1.20  Simplification rules
% 1.91/1.20  ----------------------
% 1.91/1.20  #Subsume      : 2
% 1.91/1.20  #Demod        : 11
% 1.91/1.20  #Tautology    : 17
% 1.91/1.20  #SimpNegUnit  : 2
% 1.91/1.20  #BackRed      : 9
% 1.91/1.20  
% 1.91/1.20  #Partial instantiations: 0
% 1.91/1.20  #Strategies tried      : 1
% 1.91/1.20  
% 1.91/1.20  Timing (in seconds)
% 1.91/1.20  ----------------------
% 1.91/1.20  Preprocessing        : 0.31
% 1.91/1.20  Parsing              : 0.16
% 1.91/1.20  CNF conversion       : 0.02
% 1.91/1.20  Main loop            : 0.16
% 1.91/1.20  Inferencing          : 0.06
% 1.91/1.20  Reduction            : 0.05
% 1.91/1.20  Demodulation         : 0.03
% 1.91/1.20  BG Simplification    : 0.02
% 1.91/1.20  Subsumption          : 0.03
% 1.91/1.20  Abstraction          : 0.01
% 1.91/1.20  MUC search           : 0.00
% 1.91/1.20  Cooper               : 0.00
% 1.91/1.20  Total                : 0.50
% 1.91/1.20  Index Insertion      : 0.00
% 1.91/1.20  Index Deletion       : 0.00
% 1.91/1.20  Index Matching       : 0.00
% 1.91/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
