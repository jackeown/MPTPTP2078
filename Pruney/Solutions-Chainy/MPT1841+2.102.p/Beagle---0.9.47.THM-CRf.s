%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:41 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   47 (  64 expanded)
%              Number of leaves         :   25 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :   58 ( 104 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_59,plain,(
    ! [A_28,B_29] : k2_xboole_0(k1_tarski(A_28),B_29) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_63,plain,(
    ! [A_28] : k1_tarski(A_28) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_59])).

tff(c_30,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_24,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_28,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_96,plain,(
    ! [A_38,B_39] :
      ( k6_domain_1(A_38,B_39) = k1_tarski(B_39)
      | ~ m1_subset_1(B_39,A_38)
      | v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_99,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_96])).

tff(c_102,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_99])).

tff(c_26,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_112,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_26])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k6_domain_1(A_16,B_17),k1_zfmisc_1(A_16))
      | ~ m1_subset_1(B_17,A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_116,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_18])).

tff(c_120,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_116])).

tff(c_121,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_120])).

tff(c_217,plain,(
    ! [B_46,A_47] :
      ( ~ v1_subset_1(B_46,A_47)
      | v1_xboole_0(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ v1_zfmisc_1(A_47)
      | v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_223,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_2'),'#skF_1')
    | v1_xboole_0(k1_tarski('#skF_2'))
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_121,c_217])).

tff(c_232,plain,
    ( v1_xboole_0(k1_tarski('#skF_2'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_112,c_223])).

tff(c_233,plain,(
    v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_232])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_237,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_233,c_6])).

tff(c_241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_237])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:04:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.19  
% 1.90/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.19  %$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.90/1.19  
% 1.90/1.19  %Foreground sorts:
% 1.90/1.19  
% 1.90/1.19  
% 1.90/1.19  %Background operators:
% 1.90/1.19  
% 1.90/1.19  
% 1.90/1.19  %Foreground operators:
% 1.90/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.19  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.90/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.90/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.90/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.90/1.19  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.90/1.19  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 1.90/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.90/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.90/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.90/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.90/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.19  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.90/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.90/1.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.90/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.90/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.90/1.19  
% 1.90/1.20  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 1.90/1.20  tff(f_42, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.90/1.20  tff(f_90, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 1.90/1.20  tff(f_64, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 1.90/1.20  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 1.90/1.20  tff(f_78, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 1.90/1.20  tff(f_33, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.90/1.20  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.90/1.20  tff(c_59, plain, (![A_28, B_29]: (k2_xboole_0(k1_tarski(A_28), B_29)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.90/1.20  tff(c_63, plain, (![A_28]: (k1_tarski(A_28)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_59])).
% 1.90/1.20  tff(c_30, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 1.90/1.20  tff(c_24, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 1.90/1.20  tff(c_28, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 1.90/1.20  tff(c_96, plain, (![A_38, B_39]: (k6_domain_1(A_38, B_39)=k1_tarski(B_39) | ~m1_subset_1(B_39, A_38) | v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.90/1.20  tff(c_99, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_96])).
% 1.90/1.20  tff(c_102, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_30, c_99])).
% 1.90/1.20  tff(c_26, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 1.90/1.20  tff(c_112, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_26])).
% 1.90/1.20  tff(c_18, plain, (![A_16, B_17]: (m1_subset_1(k6_domain_1(A_16, B_17), k1_zfmisc_1(A_16)) | ~m1_subset_1(B_17, A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.90/1.20  tff(c_116, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_102, c_18])).
% 1.90/1.20  tff(c_120, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_116])).
% 1.90/1.20  tff(c_121, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_30, c_120])).
% 1.90/1.20  tff(c_217, plain, (![B_46, A_47]: (~v1_subset_1(B_46, A_47) | v1_xboole_0(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~v1_zfmisc_1(A_47) | v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.90/1.20  tff(c_223, plain, (~v1_subset_1(k1_tarski('#skF_2'), '#skF_1') | v1_xboole_0(k1_tarski('#skF_2')) | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_121, c_217])).
% 1.90/1.20  tff(c_232, plain, (v1_xboole_0(k1_tarski('#skF_2')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_112, c_223])).
% 1.90/1.20  tff(c_233, plain, (v1_xboole_0(k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_30, c_232])).
% 1.90/1.20  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.90/1.20  tff(c_237, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_233, c_6])).
% 1.90/1.20  tff(c_241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_237])).
% 1.90/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.20  
% 1.90/1.20  Inference rules
% 1.90/1.20  ----------------------
% 1.90/1.20  #Ref     : 0
% 1.90/1.20  #Sup     : 44
% 1.90/1.20  #Fact    : 0
% 1.90/1.20  #Define  : 0
% 1.90/1.20  #Split   : 1
% 1.90/1.20  #Chain   : 0
% 1.90/1.20  #Close   : 0
% 1.90/1.20  
% 1.90/1.20  Ordering : KBO
% 1.90/1.20  
% 1.90/1.20  Simplification rules
% 1.90/1.20  ----------------------
% 1.90/1.20  #Subsume      : 3
% 1.90/1.20  #Demod        : 14
% 1.90/1.20  #Tautology    : 23
% 1.90/1.20  #SimpNegUnit  : 9
% 1.90/1.20  #BackRed      : 3
% 1.90/1.20  
% 1.90/1.20  #Partial instantiations: 0
% 1.90/1.20  #Strategies tried      : 1
% 1.90/1.20  
% 1.90/1.20  Timing (in seconds)
% 1.90/1.20  ----------------------
% 1.90/1.20  Preprocessing        : 0.29
% 1.90/1.20  Parsing              : 0.15
% 1.90/1.20  CNF conversion       : 0.02
% 1.90/1.20  Main loop            : 0.17
% 1.90/1.20  Inferencing          : 0.06
% 1.90/1.20  Reduction            : 0.05
% 1.90/1.20  Demodulation         : 0.03
% 1.90/1.20  BG Simplification    : 0.01
% 1.90/1.20  Subsumption          : 0.03
% 1.90/1.20  Abstraction          : 0.01
% 1.90/1.20  MUC search           : 0.00
% 1.90/1.21  Cooper               : 0.00
% 1.90/1.21  Total                : 0.48
% 1.90/1.21  Index Insertion      : 0.00
% 1.90/1.21  Index Deletion       : 0.00
% 1.90/1.21  Index Matching       : 0.00
% 1.90/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
