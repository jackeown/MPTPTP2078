%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:06 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   36 (  44 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   34 (  47 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_32,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_42,plain,(
    ! [B_36,A_37] :
      ( ~ v1_xboole_0(B_36)
      | ~ r2_hidden(A_37,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_42])).

tff(c_67,plain,(
    ! [B_44,A_45] :
      ( m1_subset_1(B_44,A_45)
      | ~ r2_hidden(B_44,A_45)
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_70,plain,
    ( m1_subset_1('#skF_1','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_67])).

tff(c_73,plain,(
    m1_subset_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_70])).

tff(c_96,plain,(
    ! [B_51,A_52] :
      ( m1_subset_1(k1_tarski(B_51),k1_zfmisc_1(A_52))
      | k1_xboole_0 = A_52
      | ~ m1_subset_1(B_51,A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,(
    ~ m1_subset_1(k1_tarski('#skF_1'),k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_102,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ m1_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_96,c_30])).

tff(c_106,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_102])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_108,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_2])).

tff(c_110,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:24:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.15  
% 1.74/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.15  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.74/1.15  
% 1.74/1.15  %Foreground sorts:
% 1.74/1.15  
% 1.74/1.15  
% 1.74/1.15  %Background operators:
% 1.74/1.15  
% 1.74/1.15  
% 1.74/1.15  %Foreground operators:
% 1.74/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.74/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.74/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.74/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.74/1.15  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.74/1.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.74/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.74/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.74/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.74/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.74/1.15  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.74/1.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.74/1.15  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.74/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.74/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.74/1.15  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.74/1.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.74/1.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.74/1.15  
% 1.74/1.16  tff(f_70, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 1.74/1.16  tff(f_31, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 1.74/1.16  tff(f_58, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 1.74/1.16  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 1.74/1.16  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.74/1.16  tff(c_32, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.74/1.16  tff(c_42, plain, (![B_36, A_37]: (~v1_xboole_0(B_36) | ~r2_hidden(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.74/1.16  tff(c_46, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_42])).
% 1.74/1.16  tff(c_67, plain, (![B_44, A_45]: (m1_subset_1(B_44, A_45) | ~r2_hidden(B_44, A_45) | v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.74/1.16  tff(c_70, plain, (m1_subset_1('#skF_1', '#skF_2') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_67])).
% 1.74/1.16  tff(c_73, plain, (m1_subset_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_46, c_70])).
% 1.74/1.16  tff(c_96, plain, (![B_51, A_52]: (m1_subset_1(k1_tarski(B_51), k1_zfmisc_1(A_52)) | k1_xboole_0=A_52 | ~m1_subset_1(B_51, A_52))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.74/1.16  tff(c_30, plain, (~m1_subset_1(k1_tarski('#skF_1'), k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.74/1.16  tff(c_102, plain, (k1_xboole_0='#skF_2' | ~m1_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_96, c_30])).
% 1.74/1.16  tff(c_106, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_73, c_102])).
% 1.74/1.16  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.74/1.16  tff(c_108, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_2])).
% 1.74/1.16  tff(c_110, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_108])).
% 1.74/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.16  
% 1.74/1.16  Inference rules
% 1.74/1.16  ----------------------
% 1.74/1.16  #Ref     : 0
% 1.74/1.16  #Sup     : 15
% 1.74/1.16  #Fact    : 0
% 1.74/1.16  #Define  : 0
% 1.74/1.16  #Split   : 1
% 1.74/1.16  #Chain   : 0
% 1.74/1.16  #Close   : 0
% 1.74/1.16  
% 1.74/1.16  Ordering : KBO
% 1.74/1.16  
% 1.74/1.16  Simplification rules
% 1.74/1.16  ----------------------
% 1.74/1.16  #Subsume      : 1
% 1.74/1.16  #Demod        : 3
% 1.74/1.16  #Tautology    : 9
% 1.74/1.16  #SimpNegUnit  : 2
% 1.74/1.16  #BackRed      : 2
% 1.74/1.16  
% 1.74/1.16  #Partial instantiations: 0
% 1.74/1.16  #Strategies tried      : 1
% 1.74/1.16  
% 1.74/1.16  Timing (in seconds)
% 1.74/1.16  ----------------------
% 1.74/1.16  Preprocessing        : 0.30
% 1.74/1.16  Parsing              : 0.17
% 1.74/1.16  CNF conversion       : 0.02
% 1.74/1.16  Main loop            : 0.11
% 1.74/1.16  Inferencing          : 0.04
% 1.74/1.17  Reduction            : 0.03
% 1.74/1.17  Demodulation         : 0.02
% 1.74/1.17  BG Simplification    : 0.01
% 1.74/1.17  Subsumption          : 0.02
% 1.74/1.17  Abstraction          : 0.01
% 1.74/1.17  MUC search           : 0.00
% 1.74/1.17  Cooper               : 0.00
% 1.74/1.17  Total                : 0.43
% 1.74/1.17  Index Insertion      : 0.00
% 1.74/1.17  Index Deletion       : 0.00
% 1.74/1.17  Index Matching       : 0.00
% 1.74/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
