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
% DateTime   : Thu Dec  3 10:28:41 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   45 (  68 expanded)
%              Number of leaves         :   23 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   64 ( 124 expanded)
%              Number of equality atoms :   13 (  21 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(c_45,plain,(
    ! [A_20,B_21] : k2_xboole_0(k1_tarski(A_20),B_21) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_49,plain,(
    ! [A_20] : k1_tarski(A_20) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_45])).

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
    ! [A_28,B_29] :
      ( k6_domain_1(A_28,B_29) = k1_tarski(B_29)
      | ~ m1_subset_1(B_29,A_28)
      | v1_xboole_0(A_28) ) ),
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
    ! [A_10,B_11] :
      ( m1_subset_1(k6_domain_1(A_10,B_11),k1_zfmisc_1(A_10))
      | ~ m1_subset_1(B_11,A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_138,plain,(
    ! [B_33,A_34] :
      ( ~ v1_subset_1(B_33,A_34)
      | v1_xboole_0(B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_34))
      | ~ v1_zfmisc_1(A_34)
      | v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_156,plain,(
    ! [A_36,B_37] :
      ( ~ v1_subset_1(k6_domain_1(A_36,B_37),A_36)
      | v1_xboole_0(k6_domain_1(A_36,B_37))
      | ~ v1_zfmisc_1(A_36)
      | ~ m1_subset_1(B_37,A_36)
      | v1_xboole_0(A_36) ) ),
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

tff(c_51,plain,(
    ! [B_23,A_24] :
      ( ~ v1_xboole_0(B_23)
      | B_23 = A_24
      | ~ v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_54,plain,(
    ! [A_24] :
      ( k1_xboole_0 = A_24
      | ~ v1_xboole_0(A_24) ) ),
    inference(resolution,[status(thm)],[c_2,c_51])).

tff(c_165,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_162,c_54])).

tff(c_171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_165])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:33:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.18  
% 1.85/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.18  %$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.85/1.18  
% 1.85/1.18  %Foreground sorts:
% 1.85/1.18  
% 1.85/1.18  
% 1.85/1.18  %Background operators:
% 1.85/1.18  
% 1.85/1.18  
% 1.85/1.18  %Foreground operators:
% 1.85/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.18  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.85/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.85/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.85/1.18  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 1.85/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.85/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.85/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.85/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.85/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.18  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.85/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.85/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.85/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.85/1.18  
% 1.94/1.19  tff(f_28, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 1.94/1.19  tff(f_41, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.94/1.19  tff(f_89, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 1.94/1.19  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 1.94/1.19  tff(f_56, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 1.94/1.19  tff(f_77, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 1.94/1.19  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.94/1.19  tff(f_36, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 1.94/1.19  tff(c_4, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.94/1.19  tff(c_45, plain, (![A_20, B_21]: (k2_xboole_0(k1_tarski(A_20), B_21)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.94/1.19  tff(c_49, plain, (![A_20]: (k1_tarski(A_20)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_45])).
% 1.94/1.19  tff(c_26, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.94/1.19  tff(c_24, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.94/1.19  tff(c_20, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.94/1.19  tff(c_62, plain, (![A_28, B_29]: (k6_domain_1(A_28, B_29)=k1_tarski(B_29) | ~m1_subset_1(B_29, A_28) | v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.94/1.19  tff(c_65, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_24, c_62])).
% 1.94/1.19  tff(c_68, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_26, c_65])).
% 1.94/1.19  tff(c_22, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.94/1.19  tff(c_69, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_22])).
% 1.94/1.19  tff(c_14, plain, (![A_10, B_11]: (m1_subset_1(k6_domain_1(A_10, B_11), k1_zfmisc_1(A_10)) | ~m1_subset_1(B_11, A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.94/1.19  tff(c_138, plain, (![B_33, A_34]: (~v1_subset_1(B_33, A_34) | v1_xboole_0(B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(A_34)) | ~v1_zfmisc_1(A_34) | v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.94/1.19  tff(c_156, plain, (![A_36, B_37]: (~v1_subset_1(k6_domain_1(A_36, B_37), A_36) | v1_xboole_0(k6_domain_1(A_36, B_37)) | ~v1_zfmisc_1(A_36) | ~m1_subset_1(B_37, A_36) | v1_xboole_0(A_36))), inference(resolution, [status(thm)], [c_14, c_138])).
% 1.94/1.19  tff(c_159, plain, (~v1_subset_1(k1_tarski('#skF_2'), '#skF_1') | v1_xboole_0(k6_domain_1('#skF_1', '#skF_2')) | ~v1_zfmisc_1('#skF_1') | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_68, c_156])).
% 1.94/1.19  tff(c_161, plain, (v1_xboole_0(k1_tarski('#skF_2')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_68, c_69, c_159])).
% 1.94/1.19  tff(c_162, plain, (v1_xboole_0(k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_26, c_161])).
% 1.94/1.19  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.94/1.19  tff(c_51, plain, (![B_23, A_24]: (~v1_xboole_0(B_23) | B_23=A_24 | ~v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.94/1.19  tff(c_54, plain, (![A_24]: (k1_xboole_0=A_24 | ~v1_xboole_0(A_24))), inference(resolution, [status(thm)], [c_2, c_51])).
% 1.94/1.19  tff(c_165, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_162, c_54])).
% 1.94/1.19  tff(c_171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_165])).
% 1.94/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.19  
% 1.94/1.19  Inference rules
% 1.94/1.19  ----------------------
% 1.94/1.19  #Ref     : 0
% 1.94/1.19  #Sup     : 30
% 1.94/1.19  #Fact    : 0
% 1.94/1.19  #Define  : 0
% 1.94/1.19  #Split   : 1
% 1.94/1.19  #Chain   : 0
% 1.94/1.19  #Close   : 0
% 1.94/1.19  
% 1.94/1.19  Ordering : KBO
% 1.94/1.19  
% 1.94/1.19  Simplification rules
% 1.94/1.19  ----------------------
% 1.94/1.19  #Subsume      : 3
% 1.94/1.19  #Demod        : 17
% 1.94/1.19  #Tautology    : 14
% 1.94/1.19  #SimpNegUnit  : 6
% 1.94/1.19  #BackRed      : 3
% 1.94/1.19  
% 1.94/1.19  #Partial instantiations: 0
% 1.94/1.19  #Strategies tried      : 1
% 1.94/1.19  
% 1.94/1.19  Timing (in seconds)
% 1.94/1.19  ----------------------
% 1.94/1.20  Preprocessing        : 0.29
% 1.94/1.20  Parsing              : 0.15
% 1.94/1.20  CNF conversion       : 0.02
% 1.94/1.20  Main loop            : 0.15
% 1.94/1.20  Inferencing          : 0.06
% 1.94/1.20  Reduction            : 0.04
% 1.94/1.20  Demodulation         : 0.03
% 1.94/1.20  BG Simplification    : 0.01
% 1.94/1.20  Subsumption          : 0.03
% 1.94/1.20  Abstraction          : 0.01
% 1.94/1.20  MUC search           : 0.00
% 1.94/1.20  Cooper               : 0.00
% 1.94/1.20  Total                : 0.46
% 1.94/1.20  Index Insertion      : 0.00
% 1.94/1.20  Index Deletion       : 0.00
% 1.94/1.20  Index Matching       : 0.00
% 1.94/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
