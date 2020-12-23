%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:02 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   45 (  49 expanded)
%              Number of leaves         :   25 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :   58 (  68 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_72,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_67,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_69,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_40,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(k1_tarski(A_16),B_17)
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_36,plain,(
    ! [A_24] : ~ v1_xboole_0(k1_zfmisc_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_32,plain,(
    ! [A_22] : k2_subset_1(A_22) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_34,plain,(
    ! [A_23] : m1_subset_1(k2_subset_1(A_23),k1_zfmisc_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_41,plain,(
    ! [A_23] : m1_subset_1(A_23,k1_zfmisc_1(A_23)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(k1_zfmisc_1(A_18),k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_26,plain,(
    ! [B_21,A_20] :
      ( r2_hidden(B_21,A_20)
      | ~ m1_subset_1(B_21,A_20)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_173,plain,(
    ! [C_58,B_59,A_60] :
      ( r2_hidden(C_58,B_59)
      | ~ r2_hidden(C_58,A_60)
      | ~ r1_tarski(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_306,plain,(
    ! [B_80,B_81,A_82] :
      ( r2_hidden(B_80,B_81)
      | ~ r1_tarski(A_82,B_81)
      | ~ m1_subset_1(B_80,A_82)
      | v1_xboole_0(A_82) ) ),
    inference(resolution,[status(thm)],[c_26,c_173])).

tff(c_312,plain,(
    ! [B_80,B_19,A_18] :
      ( r2_hidden(B_80,k1_zfmisc_1(B_19))
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_18))
      | v1_xboole_0(k1_zfmisc_1(A_18))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(resolution,[status(thm)],[c_22,c_306])).

tff(c_401,plain,(
    ! [B_98,B_99,A_100] :
      ( r2_hidden(B_98,k1_zfmisc_1(B_99))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(A_100))
      | ~ r1_tarski(A_100,B_99) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_312])).

tff(c_444,plain,(
    ! [A_103,B_104] :
      ( r2_hidden(A_103,k1_zfmisc_1(B_104))
      | ~ r1_tarski(A_103,B_104) ) ),
    inference(resolution,[status(thm)],[c_41,c_401])).

tff(c_24,plain,(
    ! [B_21,A_20] :
      ( m1_subset_1(B_21,A_20)
      | ~ r2_hidden(B_21,A_20)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_449,plain,(
    ! [A_103,B_104] :
      ( m1_subset_1(A_103,k1_zfmisc_1(B_104))
      | v1_xboole_0(k1_zfmisc_1(B_104))
      | ~ r1_tarski(A_103,B_104) ) ),
    inference(resolution,[status(thm)],[c_444,c_24])).

tff(c_463,plain,(
    ! [A_105,B_106] :
      ( m1_subset_1(A_105,k1_zfmisc_1(B_106))
      | ~ r1_tarski(A_105,B_106) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_449])).

tff(c_38,plain,(
    ~ m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_481,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_463,c_38])).

tff(c_487,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_481])).

tff(c_492,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_487])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:12:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.30  
% 2.34/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.30  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.34/1.30  
% 2.34/1.30  %Foreground sorts:
% 2.34/1.30  
% 2.34/1.30  
% 2.34/1.30  %Background operators:
% 2.34/1.30  
% 2.34/1.30  
% 2.34/1.30  %Foreground operators:
% 2.34/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.34/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.34/1.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.34/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.34/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.34/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.34/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.34/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.34/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.34/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.34/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.34/1.30  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.34/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.34/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.34/1.30  
% 2.34/1.31  tff(f_77, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 2.34/1.31  tff(f_48, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.34/1.31  tff(f_72, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.34/1.31  tff(f_67, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.34/1.31  tff(f_69, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.34/1.31  tff(f_52, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.34/1.31  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.34/1.31  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.34/1.31  tff(c_40, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.34/1.31  tff(c_20, plain, (![A_16, B_17]: (r1_tarski(k1_tarski(A_16), B_17) | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.34/1.31  tff(c_36, plain, (![A_24]: (~v1_xboole_0(k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.34/1.31  tff(c_32, plain, (![A_22]: (k2_subset_1(A_22)=A_22)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.34/1.31  tff(c_34, plain, (![A_23]: (m1_subset_1(k2_subset_1(A_23), k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.34/1.31  tff(c_41, plain, (![A_23]: (m1_subset_1(A_23, k1_zfmisc_1(A_23)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34])).
% 2.34/1.31  tff(c_22, plain, (![A_18, B_19]: (r1_tarski(k1_zfmisc_1(A_18), k1_zfmisc_1(B_19)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.34/1.31  tff(c_26, plain, (![B_21, A_20]: (r2_hidden(B_21, A_20) | ~m1_subset_1(B_21, A_20) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.34/1.31  tff(c_173, plain, (![C_58, B_59, A_60]: (r2_hidden(C_58, B_59) | ~r2_hidden(C_58, A_60) | ~r1_tarski(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.34/1.31  tff(c_306, plain, (![B_80, B_81, A_82]: (r2_hidden(B_80, B_81) | ~r1_tarski(A_82, B_81) | ~m1_subset_1(B_80, A_82) | v1_xboole_0(A_82))), inference(resolution, [status(thm)], [c_26, c_173])).
% 2.34/1.31  tff(c_312, plain, (![B_80, B_19, A_18]: (r2_hidden(B_80, k1_zfmisc_1(B_19)) | ~m1_subset_1(B_80, k1_zfmisc_1(A_18)) | v1_xboole_0(k1_zfmisc_1(A_18)) | ~r1_tarski(A_18, B_19))), inference(resolution, [status(thm)], [c_22, c_306])).
% 2.34/1.31  tff(c_401, plain, (![B_98, B_99, A_100]: (r2_hidden(B_98, k1_zfmisc_1(B_99)) | ~m1_subset_1(B_98, k1_zfmisc_1(A_100)) | ~r1_tarski(A_100, B_99))), inference(negUnitSimplification, [status(thm)], [c_36, c_312])).
% 2.34/1.31  tff(c_444, plain, (![A_103, B_104]: (r2_hidden(A_103, k1_zfmisc_1(B_104)) | ~r1_tarski(A_103, B_104))), inference(resolution, [status(thm)], [c_41, c_401])).
% 2.34/1.31  tff(c_24, plain, (![B_21, A_20]: (m1_subset_1(B_21, A_20) | ~r2_hidden(B_21, A_20) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.34/1.31  tff(c_449, plain, (![A_103, B_104]: (m1_subset_1(A_103, k1_zfmisc_1(B_104)) | v1_xboole_0(k1_zfmisc_1(B_104)) | ~r1_tarski(A_103, B_104))), inference(resolution, [status(thm)], [c_444, c_24])).
% 2.34/1.31  tff(c_463, plain, (![A_105, B_106]: (m1_subset_1(A_105, k1_zfmisc_1(B_106)) | ~r1_tarski(A_105, B_106))), inference(negUnitSimplification, [status(thm)], [c_36, c_449])).
% 2.34/1.31  tff(c_38, plain, (~m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.34/1.31  tff(c_481, plain, (~r1_tarski(k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_463, c_38])).
% 2.34/1.31  tff(c_487, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_20, c_481])).
% 2.34/1.31  tff(c_492, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_487])).
% 2.34/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.31  
% 2.34/1.31  Inference rules
% 2.34/1.31  ----------------------
% 2.34/1.31  #Ref     : 0
% 2.34/1.31  #Sup     : 96
% 2.34/1.31  #Fact    : 0
% 2.34/1.31  #Define  : 0
% 2.34/1.31  #Split   : 0
% 2.34/1.31  #Chain   : 0
% 2.34/1.31  #Close   : 0
% 2.34/1.31  
% 2.34/1.31  Ordering : KBO
% 2.34/1.31  
% 2.34/1.31  Simplification rules
% 2.34/1.31  ----------------------
% 2.34/1.31  #Subsume      : 29
% 2.34/1.31  #Demod        : 4
% 2.34/1.31  #Tautology    : 22
% 2.34/1.31  #SimpNegUnit  : 17
% 2.34/1.31  #BackRed      : 0
% 2.34/1.31  
% 2.34/1.31  #Partial instantiations: 0
% 2.34/1.31  #Strategies tried      : 1
% 2.34/1.31  
% 2.34/1.31  Timing (in seconds)
% 2.34/1.31  ----------------------
% 2.34/1.31  Preprocessing        : 0.29
% 2.34/1.31  Parsing              : 0.15
% 2.34/1.31  CNF conversion       : 0.02
% 2.34/1.31  Main loop            : 0.26
% 2.34/1.31  Inferencing          : 0.11
% 2.34/1.31  Reduction            : 0.07
% 2.34/1.31  Demodulation         : 0.05
% 2.34/1.31  BG Simplification    : 0.02
% 2.34/1.31  Subsumption          : 0.05
% 2.34/1.31  Abstraction          : 0.01
% 2.34/1.31  MUC search           : 0.00
% 2.34/1.31  Cooper               : 0.00
% 2.34/1.31  Total                : 0.57
% 2.34/1.31  Index Insertion      : 0.00
% 2.34/1.31  Index Deletion       : 0.00
% 2.34/1.31  Index Matching       : 0.00
% 2.34/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
