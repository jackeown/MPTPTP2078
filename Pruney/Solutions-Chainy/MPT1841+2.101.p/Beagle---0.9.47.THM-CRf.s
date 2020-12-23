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
% DateTime   : Thu Dec  3 10:28:41 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   38 (  55 expanded)
%              Number of leaves         :   19 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :   52 (  98 expanded)
%              Number of equality atoms :    6 (  10 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1

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

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_30,axiom,(
    ! [A,B] : ~ v1_xboole_0(k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

tff(c_20,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_22,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : ~ v1_xboole_0(k2_tarski(A_2,B_3)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_27,plain,(
    ! [A_17] : ~ v1_xboole_0(k1_tarski(A_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_4])).

tff(c_14,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_18,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_35,plain,(
    ! [A_21,B_22] :
      ( k6_domain_1(A_21,B_22) = k1_tarski(B_22)
      | ~ m1_subset_1(B_22,A_21)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_38,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_35])).

tff(c_41,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_38])).

tff(c_16,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_42,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_16])).

tff(c_47,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(k6_domain_1(A_23,B_24),k1_zfmisc_1(A_23))
      | ~ m1_subset_1(B_24,A_23)
      | v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_56,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_47])).

tff(c_60,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_56])).

tff(c_61,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_60])).

tff(c_73,plain,(
    ! [B_25,A_26] :
      ( ~ v1_subset_1(B_25,A_26)
      | v1_xboole_0(B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_26))
      | ~ v1_zfmisc_1(A_26)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_76,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_2'),'#skF_1')
    | v1_xboole_0(k1_tarski('#skF_2'))
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_61,c_73])).

tff(c_82,plain,
    ( v1_xboole_0(k1_tarski('#skF_2'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_42,c_76])).

tff(c_84,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_27,c_82])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:44:08 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.10  
% 1.67/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.10  %$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1
% 1.67/1.10  
% 1.67/1.10  %Foreground sorts:
% 1.67/1.10  
% 1.67/1.10  
% 1.67/1.10  %Background operators:
% 1.67/1.10  
% 1.67/1.10  
% 1.67/1.10  %Foreground operators:
% 1.67/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.10  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.67/1.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.67/1.10  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 1.67/1.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.67/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.67/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.10  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.67/1.10  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.67/1.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.67/1.10  
% 1.67/1.11  tff(f_78, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 1.67/1.11  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.67/1.11  tff(f_30, axiom, (![A, B]: ~v1_xboole_0(k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_xboole_0)).
% 1.67/1.11  tff(f_52, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 1.67/1.11  tff(f_45, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 1.67/1.11  tff(f_66, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 1.67/1.11  tff(c_20, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.67/1.11  tff(c_22, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.67/1.11  tff(c_4, plain, (![A_2, B_3]: (~v1_xboole_0(k2_tarski(A_2, B_3)))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.67/1.11  tff(c_27, plain, (![A_17]: (~v1_xboole_0(k1_tarski(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_4])).
% 1.67/1.11  tff(c_14, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.67/1.11  tff(c_18, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.67/1.11  tff(c_35, plain, (![A_21, B_22]: (k6_domain_1(A_21, B_22)=k1_tarski(B_22) | ~m1_subset_1(B_22, A_21) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.67/1.11  tff(c_38, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_35])).
% 1.67/1.11  tff(c_41, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_20, c_38])).
% 1.67/1.11  tff(c_16, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.67/1.11  tff(c_42, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_41, c_16])).
% 1.67/1.11  tff(c_47, plain, (![A_23, B_24]: (m1_subset_1(k6_domain_1(A_23, B_24), k1_zfmisc_1(A_23)) | ~m1_subset_1(B_24, A_23) | v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.67/1.11  tff(c_56, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_41, c_47])).
% 1.67/1.11  tff(c_60, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_56])).
% 1.67/1.11  tff(c_61, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_20, c_60])).
% 1.67/1.11  tff(c_73, plain, (![B_25, A_26]: (~v1_subset_1(B_25, A_26) | v1_xboole_0(B_25) | ~m1_subset_1(B_25, k1_zfmisc_1(A_26)) | ~v1_zfmisc_1(A_26) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.67/1.11  tff(c_76, plain, (~v1_subset_1(k1_tarski('#skF_2'), '#skF_1') | v1_xboole_0(k1_tarski('#skF_2')) | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_61, c_73])).
% 1.67/1.11  tff(c_82, plain, (v1_xboole_0(k1_tarski('#skF_2')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_42, c_76])).
% 1.67/1.11  tff(c_84, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_27, c_82])).
% 1.67/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.11  
% 1.67/1.11  Inference rules
% 1.67/1.11  ----------------------
% 1.67/1.11  #Ref     : 0
% 1.67/1.11  #Sup     : 13
% 1.67/1.11  #Fact    : 0
% 1.67/1.11  #Define  : 0
% 1.67/1.11  #Split   : 1
% 1.67/1.11  #Chain   : 0
% 1.67/1.11  #Close   : 0
% 1.67/1.11  
% 1.67/1.11  Ordering : KBO
% 1.67/1.11  
% 1.67/1.11  Simplification rules
% 1.67/1.11  ----------------------
% 1.67/1.11  #Subsume      : 1
% 1.67/1.11  #Demod        : 5
% 1.67/1.11  #Tautology    : 5
% 1.67/1.11  #SimpNegUnit  : 3
% 1.67/1.11  #BackRed      : 1
% 1.67/1.11  
% 1.67/1.12  #Partial instantiations: 0
% 1.67/1.12  #Strategies tried      : 1
% 1.67/1.12  
% 1.67/1.12  Timing (in seconds)
% 1.67/1.12  ----------------------
% 1.67/1.12  Preprocessing        : 0.27
% 1.67/1.12  Parsing              : 0.14
% 1.67/1.12  CNF conversion       : 0.02
% 1.67/1.12  Main loop            : 0.11
% 1.67/1.12  Inferencing          : 0.04
% 1.67/1.12  Reduction            : 0.03
% 1.67/1.12  Demodulation         : 0.02
% 1.67/1.12  BG Simplification    : 0.01
% 1.67/1.12  Subsumption          : 0.02
% 1.67/1.12  Abstraction          : 0.01
% 1.67/1.12  MUC search           : 0.00
% 1.67/1.12  Cooper               : 0.00
% 1.67/1.12  Total                : 0.40
% 1.67/1.12  Index Insertion      : 0.00
% 1.67/1.12  Index Deletion       : 0.00
% 1.67/1.12  Index Matching       : 0.00
% 1.67/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
