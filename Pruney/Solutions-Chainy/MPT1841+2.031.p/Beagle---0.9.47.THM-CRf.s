%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:32 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   39 (  48 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :   62 (  89 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1

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

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_28,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( v1_subset_1(B,A)
           => v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tex_2)).

tff(c_26,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_24,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( r2_hidden(B_3,A_2)
      | ~ m1_subset_1(B_3,A_2)
      | v1_xboole_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_63,plain,(
    ! [A_32,B_33] :
      ( k6_domain_1(A_32,B_33) = k1_tarski(B_33)
      | ~ m1_subset_1(B_33,A_32)
      | v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_72,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_63])).

tff(c_77,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_72])).

tff(c_22,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_78,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_22])).

tff(c_2,plain,(
    ! [A_1] : ~ v1_xboole_0(k1_tarski(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(k1_tarski(A_4),k1_zfmisc_1(B_5))
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_83,plain,(
    ! [B_34,A_35] :
      ( v1_xboole_0(B_34)
      | ~ v1_subset_1(B_34,A_35)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_35))
      | ~ v1_zfmisc_1(A_35)
      | v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_86,plain,(
    ! [A_4,B_5] :
      ( v1_xboole_0(k1_tarski(A_4))
      | ~ v1_subset_1(k1_tarski(A_4),B_5)
      | ~ v1_zfmisc_1(B_5)
      | v1_xboole_0(B_5)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(resolution,[status(thm)],[c_12,c_83])).

tff(c_103,plain,(
    ! [A_38,B_39] :
      ( ~ v1_subset_1(k1_tarski(A_38),B_39)
      | ~ v1_zfmisc_1(B_39)
      | v1_xboole_0(B_39)
      | ~ r2_hidden(A_38,B_39) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2,c_86])).

tff(c_106,plain,
    ( ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1')
    | ~ r2_hidden('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_78,c_103])).

tff(c_109,plain,
    ( v1_xboole_0('#skF_1')
    | ~ r2_hidden('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_106])).

tff(c_110,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_109])).

tff(c_113,plain,
    ( ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_110])).

tff(c_116,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_113])).

tff(c_118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_116])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:08:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.29  
% 1.89/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.29  %$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1
% 1.89/1.29  
% 1.89/1.29  %Foreground sorts:
% 1.89/1.29  
% 1.89/1.29  
% 1.89/1.29  %Background operators:
% 1.89/1.29  
% 1.89/1.29  
% 1.89/1.29  %Foreground operators:
% 1.89/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.29  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.89/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.89/1.29  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 1.89/1.29  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.29  tff('#skF_1', type, '#skF_1': $i).
% 1.89/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.89/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.29  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.89/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.89/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.89/1.29  
% 1.89/1.30  tff(f_84, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 1.89/1.30  tff(f_41, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 1.89/1.30  tff(f_60, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 1.89/1.30  tff(f_28, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 1.89/1.30  tff(f_45, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 1.89/1.30  tff(f_72, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) => v1_xboole_0(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tex_2)).
% 1.89/1.30  tff(c_26, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.89/1.30  tff(c_24, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.89/1.30  tff(c_6, plain, (![B_3, A_2]: (r2_hidden(B_3, A_2) | ~m1_subset_1(B_3, A_2) | v1_xboole_0(A_2))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.89/1.30  tff(c_20, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.89/1.30  tff(c_63, plain, (![A_32, B_33]: (k6_domain_1(A_32, B_33)=k1_tarski(B_33) | ~m1_subset_1(B_33, A_32) | v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.89/1.30  tff(c_72, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_24, c_63])).
% 1.89/1.30  tff(c_77, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_26, c_72])).
% 1.89/1.30  tff(c_22, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.89/1.30  tff(c_78, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_22])).
% 1.89/1.30  tff(c_2, plain, (![A_1]: (~v1_xboole_0(k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.89/1.30  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(k1_tarski(A_4), k1_zfmisc_1(B_5)) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.89/1.30  tff(c_83, plain, (![B_34, A_35]: (v1_xboole_0(B_34) | ~v1_subset_1(B_34, A_35) | ~m1_subset_1(B_34, k1_zfmisc_1(A_35)) | ~v1_zfmisc_1(A_35) | v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.89/1.30  tff(c_86, plain, (![A_4, B_5]: (v1_xboole_0(k1_tarski(A_4)) | ~v1_subset_1(k1_tarski(A_4), B_5) | ~v1_zfmisc_1(B_5) | v1_xboole_0(B_5) | ~r2_hidden(A_4, B_5))), inference(resolution, [status(thm)], [c_12, c_83])).
% 1.89/1.30  tff(c_103, plain, (![A_38, B_39]: (~v1_subset_1(k1_tarski(A_38), B_39) | ~v1_zfmisc_1(B_39) | v1_xboole_0(B_39) | ~r2_hidden(A_38, B_39))), inference(negUnitSimplification, [status(thm)], [c_2, c_86])).
% 1.89/1.30  tff(c_106, plain, (~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1') | ~r2_hidden('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_78, c_103])).
% 1.89/1.30  tff(c_109, plain, (v1_xboole_0('#skF_1') | ~r2_hidden('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_106])).
% 1.89/1.30  tff(c_110, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_26, c_109])).
% 1.89/1.30  tff(c_113, plain, (~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_6, c_110])).
% 1.89/1.30  tff(c_116, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_113])).
% 1.89/1.30  tff(c_118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_116])).
% 1.89/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.30  
% 1.89/1.30  Inference rules
% 1.89/1.30  ----------------------
% 1.89/1.30  #Ref     : 0
% 1.89/1.30  #Sup     : 17
% 1.89/1.30  #Fact    : 0
% 1.89/1.30  #Define  : 0
% 1.89/1.30  #Split   : 0
% 1.89/1.30  #Chain   : 0
% 1.89/1.30  #Close   : 0
% 1.89/1.30  
% 1.89/1.30  Ordering : KBO
% 1.89/1.30  
% 1.89/1.30  Simplification rules
% 1.89/1.30  ----------------------
% 1.89/1.30  #Subsume      : 3
% 1.89/1.30  #Demod        : 3
% 1.89/1.30  #Tautology    : 6
% 1.89/1.30  #SimpNegUnit  : 5
% 1.89/1.30  #BackRed      : 1
% 1.89/1.30  
% 1.89/1.30  #Partial instantiations: 0
% 1.89/1.30  #Strategies tried      : 1
% 1.89/1.30  
% 1.89/1.30  Timing (in seconds)
% 1.89/1.30  ----------------------
% 1.89/1.30  Preprocessing        : 0.31
% 1.89/1.30  Parsing              : 0.17
% 1.89/1.30  CNF conversion       : 0.02
% 1.89/1.30  Main loop            : 0.12
% 1.89/1.30  Inferencing          : 0.05
% 1.89/1.30  Reduction            : 0.03
% 1.89/1.30  Demodulation         : 0.02
% 1.89/1.31  BG Simplification    : 0.01
% 1.89/1.31  Subsumption          : 0.02
% 1.89/1.31  Abstraction          : 0.01
% 1.89/1.31  MUC search           : 0.00
% 1.89/1.31  Cooper               : 0.00
% 1.89/1.31  Total                : 0.46
% 1.89/1.31  Index Insertion      : 0.00
% 1.89/1.31  Index Deletion       : 0.00
% 1.89/1.31  Index Matching       : 0.00
% 1.89/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
