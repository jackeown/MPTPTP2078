%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:31 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   44 (  67 expanded)
%              Number of leaves         :   24 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   58 ( 118 expanded)
%              Number of equality atoms :   12 (  20 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_48,plain,(
    ! [A_25,B_26] : k2_xboole_0(k1_tarski(A_25),B_26) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_52,plain,(
    ! [A_25] : k1_tarski(A_25) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_48])).

tff(c_28,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_26,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_22,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_86,plain,(
    ! [A_35,B_36] :
      ( k6_domain_1(A_35,B_36) = k1_tarski(B_36)
      | ~ m1_subset_1(B_36,A_35)
      | v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_89,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_86])).

tff(c_92,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_89])).

tff(c_24,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_93,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_24])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k6_domain_1(A_14,B_15),k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,A_14)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_160,plain,(
    ! [B_40,A_41] :
      ( ~ v1_subset_1(B_40,A_41)
      | v1_xboole_0(B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41))
      | ~ v1_zfmisc_1(A_41)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_171,plain,(
    ! [A_42,B_43] :
      ( ~ v1_subset_1(k6_domain_1(A_42,B_43),A_42)
      | v1_xboole_0(k6_domain_1(A_42,B_43))
      | ~ v1_zfmisc_1(A_42)
      | ~ m1_subset_1(B_43,A_42)
      | v1_xboole_0(A_42) ) ),
    inference(resolution,[status(thm)],[c_16,c_160])).

tff(c_174,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_2'),'#skF_1')
    | v1_xboole_0(k6_domain_1('#skF_1','#skF_2'))
    | ~ v1_zfmisc_1('#skF_1')
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_171])).

tff(c_176,plain,
    ( v1_xboole_0(k1_tarski('#skF_2'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_92,c_93,c_174])).

tff(c_177,plain,(
    v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_176])).

tff(c_4,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_180,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_177,c_4])).

tff(c_184,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_180])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:27:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.19  
% 2.18/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.20  %$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.18/1.20  
% 2.18/1.20  %Foreground sorts:
% 2.18/1.20  
% 2.18/1.20  
% 2.18/1.20  %Background operators:
% 2.18/1.20  
% 2.18/1.20  
% 2.18/1.20  %Foreground operators:
% 2.18/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.20  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.18/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.18/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.20  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.18/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.18/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.18/1.20  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.20  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.20  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.18/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.20  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.18/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.18/1.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.18/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.20  
% 2.18/1.21  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.18/1.21  tff(f_40, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.18/1.21  tff(f_87, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.18/1.21  tff(f_61, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.18/1.21  tff(f_54, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.18/1.21  tff(f_75, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.18/1.21  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.18/1.21  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.18/1.21  tff(c_48, plain, (![A_25, B_26]: (k2_xboole_0(k1_tarski(A_25), B_26)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.18/1.21  tff(c_52, plain, (![A_25]: (k1_tarski(A_25)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_48])).
% 2.18/1.21  tff(c_28, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.18/1.21  tff(c_26, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.18/1.21  tff(c_22, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.18/1.21  tff(c_86, plain, (![A_35, B_36]: (k6_domain_1(A_35, B_36)=k1_tarski(B_36) | ~m1_subset_1(B_36, A_35) | v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.18/1.21  tff(c_89, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_86])).
% 2.18/1.21  tff(c_92, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_28, c_89])).
% 2.18/1.21  tff(c_24, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.18/1.21  tff(c_93, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_24])).
% 2.18/1.21  tff(c_16, plain, (![A_14, B_15]: (m1_subset_1(k6_domain_1(A_14, B_15), k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, A_14) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.18/1.21  tff(c_160, plain, (![B_40, A_41]: (~v1_subset_1(B_40, A_41) | v1_xboole_0(B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)) | ~v1_zfmisc_1(A_41) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.18/1.21  tff(c_171, plain, (![A_42, B_43]: (~v1_subset_1(k6_domain_1(A_42, B_43), A_42) | v1_xboole_0(k6_domain_1(A_42, B_43)) | ~v1_zfmisc_1(A_42) | ~m1_subset_1(B_43, A_42) | v1_xboole_0(A_42))), inference(resolution, [status(thm)], [c_16, c_160])).
% 2.18/1.21  tff(c_174, plain, (~v1_subset_1(k1_tarski('#skF_2'), '#skF_1') | v1_xboole_0(k6_domain_1('#skF_1', '#skF_2')) | ~v1_zfmisc_1('#skF_1') | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_92, c_171])).
% 2.18/1.21  tff(c_176, plain, (v1_xboole_0(k1_tarski('#skF_2')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_92, c_93, c_174])).
% 2.18/1.21  tff(c_177, plain, (v1_xboole_0(k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_28, c_176])).
% 2.18/1.21  tff(c_4, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.18/1.21  tff(c_180, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_177, c_4])).
% 2.18/1.21  tff(c_184, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_180])).
% 2.18/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.21  
% 2.18/1.21  Inference rules
% 2.18/1.21  ----------------------
% 2.18/1.21  #Ref     : 0
% 2.18/1.21  #Sup     : 33
% 2.18/1.21  #Fact    : 0
% 2.18/1.21  #Define  : 0
% 2.18/1.21  #Split   : 1
% 2.18/1.21  #Chain   : 0
% 2.18/1.21  #Close   : 0
% 2.18/1.21  
% 2.18/1.21  Ordering : KBO
% 2.18/1.21  
% 2.18/1.21  Simplification rules
% 2.18/1.21  ----------------------
% 2.18/1.21  #Subsume      : 2
% 2.18/1.21  #Demod        : 14
% 2.18/1.21  #Tautology    : 19
% 2.18/1.21  #SimpNegUnit  : 6
% 2.18/1.21  #BackRed      : 3
% 2.18/1.21  
% 2.18/1.21  #Partial instantiations: 0
% 2.18/1.21  #Strategies tried      : 1
% 2.18/1.21  
% 2.18/1.21  Timing (in seconds)
% 2.18/1.21  ----------------------
% 2.18/1.21  Preprocessing        : 0.30
% 2.18/1.21  Parsing              : 0.16
% 2.18/1.21  CNF conversion       : 0.02
% 2.18/1.21  Main loop            : 0.16
% 2.18/1.21  Inferencing          : 0.06
% 2.18/1.21  Reduction            : 0.05
% 2.18/1.21  Demodulation         : 0.03
% 2.18/1.21  BG Simplification    : 0.01
% 2.18/1.21  Subsumption          : 0.03
% 2.18/1.21  Abstraction          : 0.01
% 2.18/1.21  MUC search           : 0.00
% 2.18/1.21  Cooper               : 0.00
% 2.18/1.21  Total                : 0.48
% 2.18/1.21  Index Insertion      : 0.00
% 2.18/1.21  Index Deletion       : 0.00
% 2.18/1.21  Index Matching       : 0.00
% 2.18/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
