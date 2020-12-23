%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:50 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   41 (  65 expanded)
%              Number of leaves         :   20 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   49 ( 111 expanded)
%              Number of equality atoms :    9 (  17 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_65,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & ~ v1_zfmisc_1(A) )
       => ! [B] :
            ( m1_subset_1(B,A)
           => v1_subset_1(k6_domain_1(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_29,axiom,(
    ! [A] : v1_zfmisc_1(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_zfmisc_1)).

tff(c_20,plain,(
    ~ v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_22,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_18,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k1_tarski(A_3),k1_zfmisc_1(B_4))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_41,plain,(
    ! [B_19,A_20] :
      ( v1_subset_1(B_19,A_20)
      | B_19 = A_20
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_63,plain,(
    ! [A_24,B_25] :
      ( v1_subset_1(k1_tarski(A_24),B_25)
      | k1_tarski(A_24) = B_25
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(resolution,[status(thm)],[c_6,c_41])).

tff(c_47,plain,(
    ! [A_22,B_23] :
      ( k6_domain_1(A_22,B_23) = k1_tarski(B_23)
      | ~ m1_subset_1(B_23,A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_53,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_47])).

tff(c_57,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_53])).

tff(c_16,plain,(
    ~ v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_58,plain,(
    ~ v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_16])).

tff(c_71,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | ~ r2_hidden('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_63,c_58])).

tff(c_83,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_86,plain,
    ( v1_xboole_0('#skF_1')
    | ~ m1_subset_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_83])).

tff(c_89,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_86])).

tff(c_91,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_89])).

tff(c_92,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_4,plain,(
    ! [A_2] : v1_zfmisc_1(k1_tarski(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_113,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_4])).

tff(c_121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_113])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:25:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.18  
% 1.75/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.18  %$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1
% 1.75/1.18  
% 1.75/1.18  %Foreground sorts:
% 1.75/1.18  
% 1.75/1.18  
% 1.75/1.18  %Background operators:
% 1.75/1.18  
% 1.75/1.18  
% 1.75/1.18  %Foreground operators:
% 1.75/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.75/1.18  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.75/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.75/1.18  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 1.75/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.75/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.75/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.75/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.75/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.18  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.75/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.75/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.75/1.18  
% 1.86/1.19  tff(f_65, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & ~v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, A) => v1_subset_1(k6_domain_1(A, B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tex_2)).
% 1.86/1.19  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 1.86/1.19  tff(f_33, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 1.86/1.19  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 1.86/1.19  tff(f_46, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 1.86/1.19  tff(f_29, axiom, (![A]: v1_zfmisc_1(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_zfmisc_1)).
% 1.86/1.19  tff(c_20, plain, (~v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.86/1.19  tff(c_22, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.86/1.19  tff(c_18, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.86/1.19  tff(c_8, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.86/1.19  tff(c_6, plain, (![A_3, B_4]: (m1_subset_1(k1_tarski(A_3), k1_zfmisc_1(B_4)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.86/1.19  tff(c_41, plain, (![B_19, A_20]: (v1_subset_1(B_19, A_20) | B_19=A_20 | ~m1_subset_1(B_19, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.86/1.19  tff(c_63, plain, (![A_24, B_25]: (v1_subset_1(k1_tarski(A_24), B_25) | k1_tarski(A_24)=B_25 | ~r2_hidden(A_24, B_25))), inference(resolution, [status(thm)], [c_6, c_41])).
% 1.86/1.19  tff(c_47, plain, (![A_22, B_23]: (k6_domain_1(A_22, B_23)=k1_tarski(B_23) | ~m1_subset_1(B_23, A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.86/1.19  tff(c_53, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_47])).
% 1.86/1.19  tff(c_57, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_22, c_53])).
% 1.86/1.19  tff(c_16, plain, (~v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.86/1.19  tff(c_58, plain, (~v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_16])).
% 1.86/1.19  tff(c_71, plain, (k1_tarski('#skF_2')='#skF_1' | ~r2_hidden('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_63, c_58])).
% 1.86/1.19  tff(c_83, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_71])).
% 1.86/1.19  tff(c_86, plain, (v1_xboole_0('#skF_1') | ~m1_subset_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_8, c_83])).
% 1.86/1.19  tff(c_89, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_86])).
% 1.86/1.19  tff(c_91, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_89])).
% 1.86/1.19  tff(c_92, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_71])).
% 1.86/1.19  tff(c_4, plain, (![A_2]: (v1_zfmisc_1(k1_tarski(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.86/1.19  tff(c_113, plain, (v1_zfmisc_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_92, c_4])).
% 1.86/1.19  tff(c_121, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_113])).
% 1.86/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.19  
% 1.86/1.19  Inference rules
% 1.86/1.19  ----------------------
% 1.86/1.19  #Ref     : 0
% 1.86/1.19  #Sup     : 21
% 1.86/1.19  #Fact    : 0
% 1.86/1.19  #Define  : 0
% 1.86/1.19  #Split   : 1
% 1.86/1.19  #Chain   : 0
% 1.86/1.19  #Close   : 0
% 1.86/1.19  
% 1.86/1.19  Ordering : KBO
% 1.86/1.19  
% 1.86/1.19  Simplification rules
% 1.86/1.19  ----------------------
% 1.86/1.19  #Subsume      : 0
% 1.86/1.19  #Demod        : 10
% 1.86/1.19  #Tautology    : 8
% 1.86/1.19  #SimpNegUnit  : 3
% 1.86/1.19  #BackRed      : 3
% 1.86/1.19  
% 1.86/1.19  #Partial instantiations: 0
% 1.86/1.19  #Strategies tried      : 1
% 1.86/1.19  
% 1.86/1.19  Timing (in seconds)
% 1.86/1.19  ----------------------
% 1.86/1.19  Preprocessing        : 0.26
% 1.86/1.19  Parsing              : 0.14
% 1.86/1.19  CNF conversion       : 0.02
% 1.86/1.19  Main loop            : 0.12
% 1.86/1.19  Inferencing          : 0.05
% 1.86/1.19  Reduction            : 0.03
% 1.86/1.19  Demodulation         : 0.02
% 1.86/1.19  BG Simplification    : 0.01
% 1.86/1.19  Subsumption          : 0.01
% 1.86/1.19  Abstraction          : 0.01
% 1.86/1.19  MUC search           : 0.00
% 1.86/1.19  Cooper               : 0.00
% 1.86/1.19  Total                : 0.41
% 1.86/1.19  Index Insertion      : 0.00
% 1.86/1.19  Index Deletion       : 0.00
% 1.86/1.19  Index Matching       : 0.00
% 1.86/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
