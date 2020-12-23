%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:50 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   37 (  52 expanded)
%              Number of leaves         :   19 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :   43 (  84 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_64,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & ~ v1_zfmisc_1(A) )
       => ! [B] :
            ( m1_subset_1(B,A)
           => v1_subset_1(k6_domain_1(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_31,axiom,(
    ! [A] : v1_zfmisc_1(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_zfmisc_1)).

tff(c_20,plain,(
    ~ v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_18,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_44,plain,(
    ! [A_19,B_20] :
      ( k6_domain_1(A_19,B_20) = k1_tarski(B_20)
      | ~ m1_subset_1(B_20,A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_47,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_44])).

tff(c_50,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_47])).

tff(c_16,plain,(
    ~ v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_51,plain,(
    ~ v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_16])).

tff(c_56,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(k6_domain_1(A_21,B_22),k1_zfmisc_1(A_21))
      | ~ m1_subset_1(B_22,A_21)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_65,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_56])).

tff(c_69,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_65])).

tff(c_70,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_69])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( v1_subset_1(B_10,A_9)
      | B_10 = A_9
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_76,plain,
    ( v1_subset_1(k1_tarski('#skF_2'),'#skF_1')
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_70,c_12])).

tff(c_80,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_76])).

tff(c_6,plain,(
    ! [A_4] : v1_zfmisc_1(k1_tarski(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_86,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_6])).

tff(c_90,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_86])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:35:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.14  
% 1.78/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.14  %$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1
% 1.78/1.14  
% 1.78/1.14  %Foreground sorts:
% 1.78/1.14  
% 1.78/1.14  
% 1.78/1.14  %Background operators:
% 1.78/1.14  
% 1.78/1.14  
% 1.78/1.14  %Foreground operators:
% 1.78/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.14  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.78/1.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.78/1.14  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 1.78/1.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.78/1.14  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.78/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.78/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.78/1.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.78/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.14  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.78/1.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.78/1.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.78/1.14  
% 1.78/1.15  tff(f_64, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & ~v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, A) => v1_subset_1(k6_domain_1(A, B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tex_2)).
% 1.78/1.15  tff(f_45, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 1.78/1.15  tff(f_38, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 1.78/1.15  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 1.78/1.15  tff(f_31, axiom, (![A]: v1_zfmisc_1(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_zfmisc_1)).
% 1.78/1.15  tff(c_20, plain, (~v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.78/1.15  tff(c_22, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.78/1.15  tff(c_18, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.78/1.15  tff(c_44, plain, (![A_19, B_20]: (k6_domain_1(A_19, B_20)=k1_tarski(B_20) | ~m1_subset_1(B_20, A_19) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.78/1.15  tff(c_47, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_44])).
% 1.78/1.15  tff(c_50, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_22, c_47])).
% 1.78/1.15  tff(c_16, plain, (~v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.78/1.15  tff(c_51, plain, (~v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_16])).
% 1.78/1.15  tff(c_56, plain, (![A_21, B_22]: (m1_subset_1(k6_domain_1(A_21, B_22), k1_zfmisc_1(A_21)) | ~m1_subset_1(B_22, A_21) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.78/1.15  tff(c_65, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_50, c_56])).
% 1.78/1.15  tff(c_69, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_65])).
% 1.78/1.15  tff(c_70, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_22, c_69])).
% 1.78/1.15  tff(c_12, plain, (![B_10, A_9]: (v1_subset_1(B_10, A_9) | B_10=A_9 | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.78/1.15  tff(c_76, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1') | k1_tarski('#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_70, c_12])).
% 1.78/1.15  tff(c_80, plain, (k1_tarski('#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_51, c_76])).
% 1.78/1.15  tff(c_6, plain, (![A_4]: (v1_zfmisc_1(k1_tarski(A_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.78/1.15  tff(c_86, plain, (v1_zfmisc_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_80, c_6])).
% 1.78/1.15  tff(c_90, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_86])).
% 1.78/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.15  
% 1.78/1.15  Inference rules
% 1.78/1.15  ----------------------
% 1.78/1.15  #Ref     : 0
% 1.78/1.15  #Sup     : 15
% 1.78/1.15  #Fact    : 0
% 1.78/1.15  #Define  : 0
% 1.78/1.15  #Split   : 0
% 1.78/1.15  #Chain   : 0
% 1.78/1.15  #Close   : 0
% 1.78/1.15  
% 1.78/1.15  Ordering : KBO
% 1.78/1.15  
% 1.78/1.15  Simplification rules
% 1.78/1.15  ----------------------
% 1.78/1.15  #Subsume      : 0
% 1.78/1.15  #Demod        : 5
% 1.78/1.15  #Tautology    : 7
% 1.78/1.15  #SimpNegUnit  : 4
% 1.78/1.15  #BackRed      : 4
% 1.78/1.15  
% 1.78/1.15  #Partial instantiations: 0
% 1.78/1.15  #Strategies tried      : 1
% 1.78/1.15  
% 1.78/1.15  Timing (in seconds)
% 1.78/1.15  ----------------------
% 1.78/1.15  Preprocessing        : 0.28
% 1.78/1.15  Parsing              : 0.15
% 1.78/1.15  CNF conversion       : 0.02
% 1.78/1.15  Main loop            : 0.10
% 1.78/1.15  Inferencing          : 0.04
% 1.78/1.15  Reduction            : 0.03
% 1.78/1.15  Demodulation         : 0.02
% 1.78/1.15  BG Simplification    : 0.01
% 1.78/1.15  Subsumption          : 0.01
% 1.78/1.15  Abstraction          : 0.01
% 1.78/1.15  MUC search           : 0.00
% 1.78/1.15  Cooper               : 0.00
% 1.78/1.15  Total                : 0.41
% 1.78/1.15  Index Insertion      : 0.00
% 1.78/1.15  Index Deletion       : 0.00
% 1.78/1.15  Index Matching       : 0.00
% 1.78/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
