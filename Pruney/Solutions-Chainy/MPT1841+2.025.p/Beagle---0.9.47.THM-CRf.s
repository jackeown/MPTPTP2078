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

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   46 (  63 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :   58 ( 104 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    8 (   3 average)
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

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

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

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_4,plain,(
    ! [A_2] : k2_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [A_24,B_25] : k2_xboole_0(k1_tarski(A_24),B_25) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_52,plain,(
    ! [A_24] : k1_tarski(A_24) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_48])).

tff(c_28,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_22,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_26,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_98,plain,(
    ! [A_35,B_36] :
      ( k6_domain_1(A_35,B_36) = k1_tarski(B_36)
      | ~ m1_subset_1(B_36,A_35)
      | v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_101,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_98])).

tff(c_104,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_101])).

tff(c_24,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_114,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_24])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(k6_domain_1(A_13,B_14),k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_14,A_13)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_118,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_16])).

tff(c_122,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_118])).

tff(c_123,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_122])).

tff(c_217,plain,(
    ! [B_43,A_44] :
      ( ~ v1_subset_1(B_43,A_44)
      | v1_xboole_0(B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_44))
      | ~ v1_zfmisc_1(A_44)
      | v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_223,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_2'),'#skF_1')
    | v1_xboole_0(k1_tarski('#skF_2'))
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_123,c_217])).

tff(c_232,plain,
    ( v1_xboole_0(k1_tarski('#skF_2'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_114,c_223])).

tff(c_233,plain,(
    v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_232])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_237,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_233,c_2])).

tff(c_241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_237])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n020.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 18:18:52 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.17/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.19  
% 2.03/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.19  %$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.03/1.19  
% 2.03/1.19  %Foreground sorts:
% 2.03/1.19  
% 2.03/1.19  
% 2.03/1.19  %Background operators:
% 2.03/1.19  
% 2.03/1.19  
% 2.03/1.19  %Foreground operators:
% 2.03/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.19  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.03/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.03/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.03/1.19  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.03/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.03/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.03/1.19  tff('#skF_2', type, '#skF_2': $i).
% 2.03/1.19  tff('#skF_1', type, '#skF_1': $i).
% 2.03/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.03/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.19  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.03/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.19  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.03/1.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.03/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.03/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.03/1.19  
% 2.03/1.20  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.03/1.20  tff(f_40, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.03/1.20  tff(f_87, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.03/1.20  tff(f_61, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.03/1.20  tff(f_54, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.03/1.20  tff(f_75, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.03/1.20  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.03/1.20  tff(c_4, plain, (![A_2]: (k2_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.03/1.20  tff(c_48, plain, (![A_24, B_25]: (k2_xboole_0(k1_tarski(A_24), B_25)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.03/1.20  tff(c_52, plain, (![A_24]: (k1_tarski(A_24)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_48])).
% 2.03/1.20  tff(c_28, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.03/1.20  tff(c_22, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.03/1.20  tff(c_26, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.03/1.20  tff(c_98, plain, (![A_35, B_36]: (k6_domain_1(A_35, B_36)=k1_tarski(B_36) | ~m1_subset_1(B_36, A_35) | v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.03/1.20  tff(c_101, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_98])).
% 2.03/1.20  tff(c_104, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_28, c_101])).
% 2.03/1.20  tff(c_24, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.03/1.20  tff(c_114, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_24])).
% 2.03/1.20  tff(c_16, plain, (![A_13, B_14]: (m1_subset_1(k6_domain_1(A_13, B_14), k1_zfmisc_1(A_13)) | ~m1_subset_1(B_14, A_13) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.03/1.20  tff(c_118, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_104, c_16])).
% 2.03/1.20  tff(c_122, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_118])).
% 2.03/1.20  tff(c_123, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_28, c_122])).
% 2.03/1.20  tff(c_217, plain, (![B_43, A_44]: (~v1_subset_1(B_43, A_44) | v1_xboole_0(B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_44)) | ~v1_zfmisc_1(A_44) | v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.03/1.20  tff(c_223, plain, (~v1_subset_1(k1_tarski('#skF_2'), '#skF_1') | v1_xboole_0(k1_tarski('#skF_2')) | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_123, c_217])).
% 2.03/1.20  tff(c_232, plain, (v1_xboole_0(k1_tarski('#skF_2')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_114, c_223])).
% 2.03/1.20  tff(c_233, plain, (v1_xboole_0(k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_28, c_232])).
% 2.03/1.20  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.03/1.20  tff(c_237, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_233, c_2])).
% 2.03/1.20  tff(c_241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_237])).
% 2.03/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.20  
% 2.03/1.20  Inference rules
% 2.03/1.20  ----------------------
% 2.03/1.20  #Ref     : 0
% 2.03/1.20  #Sup     : 45
% 2.03/1.20  #Fact    : 0
% 2.03/1.20  #Define  : 0
% 2.03/1.20  #Split   : 1
% 2.03/1.20  #Chain   : 0
% 2.03/1.20  #Close   : 0
% 2.03/1.20  
% 2.03/1.20  Ordering : KBO
% 2.03/1.20  
% 2.03/1.20  Simplification rules
% 2.03/1.20  ----------------------
% 2.03/1.20  #Subsume      : 3
% 2.03/1.20  #Demod        : 13
% 2.03/1.20  #Tautology    : 23
% 2.03/1.20  #SimpNegUnit  : 9
% 2.03/1.20  #BackRed      : 3
% 2.03/1.20  
% 2.03/1.20  #Partial instantiations: 0
% 2.03/1.20  #Strategies tried      : 1
% 2.03/1.20  
% 2.03/1.20  Timing (in seconds)
% 2.03/1.20  ----------------------
% 2.03/1.20  Preprocessing        : 0.30
% 2.03/1.20  Parsing              : 0.16
% 2.03/1.20  CNF conversion       : 0.02
% 2.03/1.20  Main loop            : 0.17
% 2.03/1.20  Inferencing          : 0.07
% 2.03/1.20  Reduction            : 0.05
% 2.03/1.20  Demodulation         : 0.03
% 2.03/1.20  BG Simplification    : 0.01
% 2.03/1.20  Subsumption          : 0.03
% 2.03/1.20  Abstraction          : 0.01
% 2.03/1.20  MUC search           : 0.00
% 2.03/1.20  Cooper               : 0.00
% 2.03/1.20  Total                : 0.50
% 2.03/1.20  Index Insertion      : 0.00
% 2.03/1.20  Index Deletion       : 0.00
% 2.03/1.20  Index Matching       : 0.00
% 2.03/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
