%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:41 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   46 (  69 expanded)
%              Number of leaves         :   24 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   64 ( 124 expanded)
%              Number of equality atoms :   13 (  21 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_28,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(c_4,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_36,plain,(
    ! [A_20,B_21] : k2_xboole_0(k1_tarski(A_20),B_21) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_40,plain,(
    ! [A_20] : k1_tarski(A_20) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_36])).

tff(c_26,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_24,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_20,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_62,plain,(
    ! [A_30,B_31] :
      ( k6_domain_1(A_30,B_31) = k1_tarski(B_31)
      | ~ m1_subset_1(B_31,A_30)
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_65,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_62])).

tff(c_68,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_65])).

tff(c_22,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_69,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_22])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k6_domain_1(A_11,B_12),k1_zfmisc_1(A_11))
      | ~ m1_subset_1(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_138,plain,(
    ! [B_35,A_36] :
      ( ~ v1_subset_1(B_35,A_36)
      | v1_xboole_0(B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_36))
      | ~ v1_zfmisc_1(A_36)
      | v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_156,plain,(
    ! [A_38,B_39] :
      ( ~ v1_subset_1(k6_domain_1(A_38,B_39),A_38)
      | v1_xboole_0(k6_domain_1(A_38,B_39))
      | ~ v1_zfmisc_1(A_38)
      | ~ m1_subset_1(B_39,A_38)
      | v1_xboole_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_14,c_138])).

tff(c_159,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_2'),'#skF_1')
    | v1_xboole_0(k6_domain_1('#skF_1','#skF_2'))
    | ~ v1_zfmisc_1('#skF_1')
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_156])).

tff(c_161,plain,
    ( v1_xboole_0(k1_tarski('#skF_2'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_68,c_69,c_159])).

tff(c_162,plain,(
    v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_161])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_42,plain,(
    ! [B_23,A_24] :
      ( ~ v1_xboole_0(B_23)
      | B_23 = A_24
      | ~ v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_45,plain,(
    ! [A_24] :
      ( k1_xboole_0 = A_24
      | ~ v1_xboole_0(A_24) ) ),
    inference(resolution,[status(thm)],[c_2,c_42])).

tff(c_165,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_162,c_45])).

tff(c_171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_165])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:57:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.18  
% 1.96/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.19  %$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.99/1.19  
% 1.99/1.19  %Foreground sorts:
% 1.99/1.19  
% 1.99/1.19  
% 1.99/1.19  %Background operators:
% 1.99/1.19  
% 1.99/1.19  
% 1.99/1.19  %Foreground operators:
% 1.99/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.19  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.99/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.99/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.99/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.99/1.19  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.99/1.19  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 1.99/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.99/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.19  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.99/1.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.99/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.99/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.99/1.19  
% 1.99/1.20  tff(f_28, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 1.99/1.20  tff(f_41, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.99/1.20  tff(f_89, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 1.99/1.20  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 1.99/1.20  tff(f_56, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 1.99/1.20  tff(f_77, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 1.99/1.20  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.99/1.20  tff(f_36, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 1.99/1.20  tff(c_4, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.99/1.20  tff(c_36, plain, (![A_20, B_21]: (k2_xboole_0(k1_tarski(A_20), B_21)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.99/1.20  tff(c_40, plain, (![A_20]: (k1_tarski(A_20)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_36])).
% 1.99/1.20  tff(c_26, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.99/1.20  tff(c_24, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.99/1.20  tff(c_20, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.99/1.20  tff(c_62, plain, (![A_30, B_31]: (k6_domain_1(A_30, B_31)=k1_tarski(B_31) | ~m1_subset_1(B_31, A_30) | v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.99/1.20  tff(c_65, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_24, c_62])).
% 1.99/1.20  tff(c_68, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_26, c_65])).
% 1.99/1.20  tff(c_22, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.99/1.20  tff(c_69, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_22])).
% 1.99/1.20  tff(c_14, plain, (![A_11, B_12]: (m1_subset_1(k6_domain_1(A_11, B_12), k1_zfmisc_1(A_11)) | ~m1_subset_1(B_12, A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.99/1.20  tff(c_138, plain, (![B_35, A_36]: (~v1_subset_1(B_35, A_36) | v1_xboole_0(B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(A_36)) | ~v1_zfmisc_1(A_36) | v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.99/1.20  tff(c_156, plain, (![A_38, B_39]: (~v1_subset_1(k6_domain_1(A_38, B_39), A_38) | v1_xboole_0(k6_domain_1(A_38, B_39)) | ~v1_zfmisc_1(A_38) | ~m1_subset_1(B_39, A_38) | v1_xboole_0(A_38))), inference(resolution, [status(thm)], [c_14, c_138])).
% 1.99/1.20  tff(c_159, plain, (~v1_subset_1(k1_tarski('#skF_2'), '#skF_1') | v1_xboole_0(k6_domain_1('#skF_1', '#skF_2')) | ~v1_zfmisc_1('#skF_1') | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_68, c_156])).
% 1.99/1.20  tff(c_161, plain, (v1_xboole_0(k1_tarski('#skF_2')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_68, c_69, c_159])).
% 1.99/1.20  tff(c_162, plain, (v1_xboole_0(k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_26, c_161])).
% 1.99/1.20  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.99/1.20  tff(c_42, plain, (![B_23, A_24]: (~v1_xboole_0(B_23) | B_23=A_24 | ~v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.99/1.20  tff(c_45, plain, (![A_24]: (k1_xboole_0=A_24 | ~v1_xboole_0(A_24))), inference(resolution, [status(thm)], [c_2, c_42])).
% 1.99/1.20  tff(c_165, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_162, c_45])).
% 1.99/1.20  tff(c_171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_165])).
% 1.99/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.20  
% 1.99/1.20  Inference rules
% 1.99/1.20  ----------------------
% 1.99/1.20  #Ref     : 0
% 1.99/1.20  #Sup     : 30
% 1.99/1.20  #Fact    : 0
% 1.99/1.20  #Define  : 0
% 1.99/1.20  #Split   : 1
% 1.99/1.20  #Chain   : 0
% 1.99/1.20  #Close   : 0
% 1.99/1.20  
% 1.99/1.20  Ordering : KBO
% 1.99/1.20  
% 1.99/1.20  Simplification rules
% 1.99/1.20  ----------------------
% 1.99/1.20  #Subsume      : 3
% 1.99/1.20  #Demod        : 17
% 1.99/1.20  #Tautology    : 14
% 1.99/1.20  #SimpNegUnit  : 6
% 1.99/1.20  #BackRed      : 3
% 1.99/1.20  
% 1.99/1.20  #Partial instantiations: 0
% 1.99/1.20  #Strategies tried      : 1
% 1.99/1.20  
% 1.99/1.20  Timing (in seconds)
% 1.99/1.20  ----------------------
% 1.99/1.20  Preprocessing        : 0.29
% 1.99/1.20  Parsing              : 0.16
% 1.99/1.20  CNF conversion       : 0.02
% 1.99/1.20  Main loop            : 0.14
% 1.99/1.20  Inferencing          : 0.06
% 1.99/1.20  Reduction            : 0.04
% 1.99/1.20  Demodulation         : 0.03
% 1.99/1.20  BG Simplification    : 0.01
% 1.99/1.20  Subsumption          : 0.03
% 1.99/1.20  Abstraction          : 0.01
% 1.99/1.20  MUC search           : 0.00
% 1.99/1.20  Cooper               : 0.00
% 1.99/1.20  Total                : 0.46
% 1.99/1.20  Index Insertion      : 0.00
% 1.99/1.20  Index Deletion       : 0.00
% 1.99/1.20  Index Matching       : 0.00
% 1.99/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
