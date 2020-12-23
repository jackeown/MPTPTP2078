%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:05 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   48 (  61 expanded)
%              Number of leaves         :   27 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   54 (  77 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_55,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_53,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_34,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_36,plain,(
    ! [B_28,A_29] :
      ( ~ r2_hidden(B_28,A_29)
      | ~ v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_36])).

tff(c_86,plain,(
    ! [B_42,A_43] :
      ( m1_subset_1(B_42,A_43)
      | ~ r2_hidden(B_42,A_43)
      | v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_98,plain,
    ( m1_subset_1('#skF_4','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_86])).

tff(c_104,plain,(
    m1_subset_1('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_98])).

tff(c_190,plain,(
    ! [B_57,A_58] :
      ( m1_subset_1(k1_tarski(B_57),k1_zfmisc_1(A_58))
      | k1_xboole_0 = A_58
      | ~ m1_subset_1(B_57,A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_32,plain,(
    ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_196,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_190,c_32])).

tff(c_200,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_196])).

tff(c_12,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_3'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_114,plain,(
    ! [A_45,B_46,C_47] :
      ( ~ r1_xboole_0(A_45,B_46)
      | ~ r2_hidden(C_47,k3_xboole_0(A_45,B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_144,plain,(
    ! [A_53,B_54] :
      ( ~ r1_xboole_0(A_53,B_54)
      | k3_xboole_0(A_53,B_54) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_114])).

tff(c_149,plain,(
    ! [A_55] : k3_xboole_0(A_55,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_144])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_128,plain,(
    ! [A_45,B_46] :
      ( ~ r1_xboole_0(A_45,B_46)
      | v1_xboole_0(k3_xboole_0(A_45,B_46)) ) ),
    inference(resolution,[status(thm)],[c_4,c_114])).

tff(c_154,plain,(
    ! [A_55] :
      ( ~ r1_xboole_0(A_55,k1_xboole_0)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_128])).

tff(c_162,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_154])).

tff(c_203,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_162])).

tff(c_210,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_203])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:47:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.33  
% 2.08/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.33  %$ r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2
% 2.08/1.33  
% 2.08/1.33  %Foreground sorts:
% 2.08/1.33  
% 2.08/1.33  
% 2.08/1.33  %Background operators:
% 2.08/1.33  
% 2.08/1.33  
% 2.08/1.33  %Foreground operators:
% 2.08/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.08/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.08/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.08/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.08/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.08/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.08/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.08/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.08/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.08/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.08/1.33  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.08/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.08/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.08/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.08/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.08/1.33  
% 2.08/1.34  tff(f_88, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 2.08/1.34  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.08/1.34  tff(f_76, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.08/1.34  tff(f_83, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 2.08/1.34  tff(f_55, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.08/1.34  tff(f_53, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.08/1.34  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.08/1.34  tff(c_34, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.08/1.34  tff(c_36, plain, (![B_28, A_29]: (~r2_hidden(B_28, A_29) | ~v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.08/1.34  tff(c_40, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_34, c_36])).
% 2.08/1.34  tff(c_86, plain, (![B_42, A_43]: (m1_subset_1(B_42, A_43) | ~r2_hidden(B_42, A_43) | v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.08/1.34  tff(c_98, plain, (m1_subset_1('#skF_4', '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_34, c_86])).
% 2.08/1.34  tff(c_104, plain, (m1_subset_1('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_40, c_98])).
% 2.08/1.34  tff(c_190, plain, (![B_57, A_58]: (m1_subset_1(k1_tarski(B_57), k1_zfmisc_1(A_58)) | k1_xboole_0=A_58 | ~m1_subset_1(B_57, A_58))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.08/1.34  tff(c_32, plain, (~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.08/1.34  tff(c_196, plain, (k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_190, c_32])).
% 2.08/1.34  tff(c_200, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_196])).
% 2.08/1.34  tff(c_12, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.08/1.34  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_3'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.08/1.34  tff(c_114, plain, (![A_45, B_46, C_47]: (~r1_xboole_0(A_45, B_46) | ~r2_hidden(C_47, k3_xboole_0(A_45, B_46)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.08/1.34  tff(c_144, plain, (![A_53, B_54]: (~r1_xboole_0(A_53, B_54) | k3_xboole_0(A_53, B_54)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_114])).
% 2.08/1.34  tff(c_149, plain, (![A_55]: (k3_xboole_0(A_55, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_144])).
% 2.08/1.34  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.08/1.34  tff(c_128, plain, (![A_45, B_46]: (~r1_xboole_0(A_45, B_46) | v1_xboole_0(k3_xboole_0(A_45, B_46)))), inference(resolution, [status(thm)], [c_4, c_114])).
% 2.08/1.34  tff(c_154, plain, (![A_55]: (~r1_xboole_0(A_55, k1_xboole_0) | v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_149, c_128])).
% 2.08/1.34  tff(c_162, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_154])).
% 2.08/1.34  tff(c_203, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_200, c_162])).
% 2.08/1.34  tff(c_210, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_203])).
% 2.08/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.34  
% 2.08/1.34  Inference rules
% 2.08/1.34  ----------------------
% 2.08/1.34  #Ref     : 0
% 2.08/1.34  #Sup     : 33
% 2.08/1.34  #Fact    : 0
% 2.08/1.34  #Define  : 0
% 2.08/1.34  #Split   : 1
% 2.08/1.34  #Chain   : 0
% 2.08/1.34  #Close   : 0
% 2.08/1.34  
% 2.08/1.34  Ordering : KBO
% 2.08/1.34  
% 2.08/1.34  Simplification rules
% 2.08/1.34  ----------------------
% 2.08/1.34  #Subsume      : 1
% 2.08/1.34  #Demod        : 14
% 2.08/1.34  #Tautology    : 17
% 2.08/1.34  #SimpNegUnit  : 2
% 2.08/1.34  #BackRed      : 8
% 2.08/1.34  
% 2.08/1.34  #Partial instantiations: 0
% 2.08/1.34  #Strategies tried      : 1
% 2.08/1.34  
% 2.08/1.34  Timing (in seconds)
% 2.08/1.34  ----------------------
% 2.08/1.34  Preprocessing        : 0.32
% 2.08/1.34  Parsing              : 0.17
% 2.08/1.34  CNF conversion       : 0.02
% 2.08/1.34  Main loop            : 0.16
% 2.08/1.34  Inferencing          : 0.06
% 2.08/1.34  Reduction            : 0.04
% 2.08/1.34  Demodulation         : 0.03
% 2.08/1.34  BG Simplification    : 0.02
% 2.08/1.34  Subsumption          : 0.03
% 2.08/1.34  Abstraction          : 0.01
% 2.08/1.34  MUC search           : 0.00
% 2.08/1.34  Cooper               : 0.00
% 2.08/1.34  Total                : 0.50
% 2.08/1.34  Index Insertion      : 0.00
% 2.08/1.34  Index Deletion       : 0.00
% 2.08/1.34  Index Matching       : 0.00
% 2.08/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
