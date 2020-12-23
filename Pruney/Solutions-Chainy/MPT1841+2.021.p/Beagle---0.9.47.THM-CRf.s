%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:30 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   43 (  60 expanded)
%              Number of leaves         :   22 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   55 ( 101 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1

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

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] : ~ v1_xboole_0(k1_enumset1(A,B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

tff(c_24,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_35,plain,(
    ! [A_25,B_26] : k1_enumset1(A_25,A_25,B_26) = k2_tarski(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] : ~ v1_xboole_0(k1_enumset1(A_7,B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_46,plain,(
    ! [A_27,B_28] : ~ v1_xboole_0(k2_tarski(A_27,B_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_8])).

tff(c_48,plain,(
    ! [A_1] : ~ v1_xboole_0(k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_46])).

tff(c_18,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_22,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_60,plain,(
    ! [A_35,B_36] :
      ( k6_domain_1(A_35,B_36) = k1_tarski(B_36)
      | ~ m1_subset_1(B_36,A_35)
      | v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_63,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_60])).

tff(c_66,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_63])).

tff(c_20,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_67,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_20])).

tff(c_72,plain,(
    ! [A_37,B_38] :
      ( m1_subset_1(k6_domain_1(A_37,B_38),k1_zfmisc_1(A_37))
      | ~ m1_subset_1(B_38,A_37)
      | v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_81,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_72])).

tff(c_85,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_81])).

tff(c_86,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_85])).

tff(c_16,plain,(
    ! [B_19,A_17] :
      ( ~ v1_subset_1(B_19,A_17)
      | v1_xboole_0(B_19)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_17))
      | ~ v1_zfmisc_1(A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_94,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_2'),'#skF_1')
    | v1_xboole_0(k1_tarski('#skF_2'))
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_86,c_16])).

tff(c_103,plain,
    ( v1_xboole_0(k1_tarski('#skF_2'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_67,c_94])).

tff(c_105,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_48,c_103])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:22:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.43  
% 2.07/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.43  %$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1
% 2.07/1.43  
% 2.07/1.43  %Foreground sorts:
% 2.07/1.43  
% 2.07/1.43  
% 2.07/1.43  %Background operators:
% 2.07/1.43  
% 2.07/1.43  
% 2.07/1.43  %Foreground operators:
% 2.07/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.43  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.07/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.07/1.43  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.07/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.07/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.07/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.07/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.07/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.07/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.43  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.07/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.07/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.07/1.43  
% 2.24/1.45  tff(f_81, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.24/1.45  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.24/1.45  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.24/1.45  tff(f_34, axiom, (![A, B, C]: ~v1_xboole_0(k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_subset_1)).
% 2.24/1.45  tff(f_55, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.24/1.45  tff(f_48, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.24/1.45  tff(f_69, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.24/1.45  tff(c_24, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.24/1.45  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.24/1.45  tff(c_35, plain, (![A_25, B_26]: (k1_enumset1(A_25, A_25, B_26)=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.24/1.45  tff(c_8, plain, (![A_7, B_8, C_9]: (~v1_xboole_0(k1_enumset1(A_7, B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.24/1.45  tff(c_46, plain, (![A_27, B_28]: (~v1_xboole_0(k2_tarski(A_27, B_28)))), inference(superposition, [status(thm), theory('equality')], [c_35, c_8])).
% 2.24/1.45  tff(c_48, plain, (![A_1]: (~v1_xboole_0(k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_46])).
% 2.24/1.45  tff(c_18, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.24/1.45  tff(c_22, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.24/1.45  tff(c_60, plain, (![A_35, B_36]: (k6_domain_1(A_35, B_36)=k1_tarski(B_36) | ~m1_subset_1(B_36, A_35) | v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.24/1.45  tff(c_63, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_60])).
% 2.24/1.45  tff(c_66, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_24, c_63])).
% 2.24/1.45  tff(c_20, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.24/1.45  tff(c_67, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_20])).
% 2.24/1.45  tff(c_72, plain, (![A_37, B_38]: (m1_subset_1(k6_domain_1(A_37, B_38), k1_zfmisc_1(A_37)) | ~m1_subset_1(B_38, A_37) | v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.24/1.45  tff(c_81, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_66, c_72])).
% 2.24/1.45  tff(c_85, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_81])).
% 2.24/1.45  tff(c_86, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_24, c_85])).
% 2.24/1.45  tff(c_16, plain, (![B_19, A_17]: (~v1_subset_1(B_19, A_17) | v1_xboole_0(B_19) | ~m1_subset_1(B_19, k1_zfmisc_1(A_17)) | ~v1_zfmisc_1(A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.24/1.45  tff(c_94, plain, (~v1_subset_1(k1_tarski('#skF_2'), '#skF_1') | v1_xboole_0(k1_tarski('#skF_2')) | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_86, c_16])).
% 2.24/1.45  tff(c_103, plain, (v1_xboole_0(k1_tarski('#skF_2')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_67, c_94])).
% 2.24/1.45  tff(c_105, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_48, c_103])).
% 2.24/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.45  
% 2.24/1.45  Inference rules
% 2.24/1.45  ----------------------
% 2.24/1.45  #Ref     : 0
% 2.24/1.45  #Sup     : 18
% 2.24/1.45  #Fact    : 0
% 2.24/1.45  #Define  : 0
% 2.24/1.45  #Split   : 0
% 2.24/1.45  #Chain   : 0
% 2.24/1.45  #Close   : 0
% 2.24/1.45  
% 2.24/1.45  Ordering : KBO
% 2.24/1.45  
% 2.24/1.45  Simplification rules
% 2.24/1.45  ----------------------
% 2.24/1.45  #Subsume      : 0
% 2.24/1.45  #Demod        : 4
% 2.24/1.45  #Tautology    : 9
% 2.24/1.45  #SimpNegUnit  : 3
% 2.24/1.45  #BackRed      : 1
% 2.24/1.45  
% 2.24/1.45  #Partial instantiations: 0
% 2.24/1.45  #Strategies tried      : 1
% 2.24/1.45  
% 2.24/1.45  Timing (in seconds)
% 2.24/1.45  ----------------------
% 2.24/1.46  Preprocessing        : 0.46
% 2.24/1.46  Parsing              : 0.24
% 2.24/1.46  CNF conversion       : 0.03
% 2.24/1.46  Main loop            : 0.18
% 2.24/1.46  Inferencing          : 0.08
% 2.24/1.46  Reduction            : 0.05
% 2.24/1.46  Demodulation         : 0.03
% 2.24/1.46  BG Simplification    : 0.02
% 2.24/1.46  Subsumption          : 0.03
% 2.24/1.46  Abstraction          : 0.01
% 2.24/1.46  MUC search           : 0.00
% 2.24/1.46  Cooper               : 0.00
% 2.24/1.46  Total                : 0.69
% 2.24/1.46  Index Insertion      : 0.00
% 2.24/1.46  Index Deletion       : 0.00
% 2.24/1.46  Index Matching       : 0.00
% 2.24/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
