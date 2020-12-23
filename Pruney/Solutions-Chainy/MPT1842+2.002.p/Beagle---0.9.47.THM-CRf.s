%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:49 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   41 (  60 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :   62 ( 113 expanded)
%              Number of equality atoms :   13 (  17 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_2 > #skF_3

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & ~ v1_zfmisc_1(A) )
       => ! [B] :
            ( m1_subset_1(B,A)
           => v1_subset_1(k6_domain_1(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tex_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(c_32,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_28,plain,(
    m1_subset_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r2_hidden(B_2,A_1)
      | ~ m1_subset_1(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_30,plain,(
    ~ v1_zfmisc_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_100,plain,(
    ! [A_32,B_33] :
      ( k6_domain_1(A_32,B_33) = k1_tarski(B_33)
      | ~ m1_subset_1(B_33,A_32)
      | v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_112,plain,
    ( k6_domain_1('#skF_2','#skF_3') = k1_tarski('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_100])).

tff(c_118,plain,(
    k6_domain_1('#skF_2','#skF_3') = k1_tarski('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_112])).

tff(c_125,plain,(
    ! [A_35,B_36] :
      ( v1_zfmisc_1(A_35)
      | k6_domain_1(A_35,B_36) != A_35
      | ~ m1_subset_1(B_36,A_35)
      | v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_137,plain,
    ( v1_zfmisc_1('#skF_2')
    | k6_domain_1('#skF_2','#skF_3') != '#skF_2'
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_125])).

tff(c_142,plain,
    ( v1_zfmisc_1('#skF_2')
    | k1_tarski('#skF_3') != '#skF_2'
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_137])).

tff(c_143,plain,(
    k1_tarski('#skF_3') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_142])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k1_tarski(A_3),k1_zfmisc_1(B_4))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_76,plain,(
    ! [B_29,A_30] :
      ( v1_subset_1(B_29,A_30)
      | B_29 = A_30
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_146,plain,(
    ! [A_41,B_42] :
      ( v1_subset_1(k1_tarski(A_41),B_42)
      | k1_tarski(A_41) = B_42
      | ~ r2_hidden(A_41,B_42) ) ),
    inference(resolution,[status(thm)],[c_10,c_76])).

tff(c_26,plain,(
    ~ v1_subset_1(k6_domain_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_119,plain,(
    ~ v1_subset_1(k1_tarski('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_26])).

tff(c_153,plain,
    ( k1_tarski('#skF_3') = '#skF_2'
    | ~ r2_hidden('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_146,c_119])).

tff(c_161,plain,(
    ~ r2_hidden('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_153])).

tff(c_166,plain,
    ( ~ m1_subset_1('#skF_3','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_161])).

tff(c_169,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_166])).

tff(c_171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_169])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:18:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.57  
% 2.67/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.58  %$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_2 > #skF_3
% 2.67/1.58  
% 2.67/1.58  %Foreground sorts:
% 2.67/1.58  
% 2.67/1.58  
% 2.67/1.58  %Background operators:
% 2.67/1.58  
% 2.67/1.58  
% 2.67/1.58  %Foreground operators:
% 2.67/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.58  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.67/1.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.67/1.58  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.67/1.58  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.67/1.58  tff('#skF_2', type, '#skF_2': $i).
% 2.67/1.58  tff('#skF_3', type, '#skF_3': $i).
% 2.67/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.67/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.58  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.67/1.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.67/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.67/1.58  
% 2.67/1.59  tff(f_82, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & ~v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, A) => v1_subset_1(k6_domain_1(A, B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tex_2)).
% 2.67/1.59  tff(f_38, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.67/1.59  tff(f_49, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.67/1.59  tff(f_63, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 2.67/1.59  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 2.67/1.59  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 2.67/1.59  tff(c_32, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.67/1.59  tff(c_28, plain, (m1_subset_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.67/1.59  tff(c_4, plain, (![B_2, A_1]: (r2_hidden(B_2, A_1) | ~m1_subset_1(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.67/1.59  tff(c_30, plain, (~v1_zfmisc_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.67/1.59  tff(c_100, plain, (![A_32, B_33]: (k6_domain_1(A_32, B_33)=k1_tarski(B_33) | ~m1_subset_1(B_33, A_32) | v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.67/1.59  tff(c_112, plain, (k6_domain_1('#skF_2', '#skF_3')=k1_tarski('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_100])).
% 2.67/1.59  tff(c_118, plain, (k6_domain_1('#skF_2', '#skF_3')=k1_tarski('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_32, c_112])).
% 2.67/1.59  tff(c_125, plain, (![A_35, B_36]: (v1_zfmisc_1(A_35) | k6_domain_1(A_35, B_36)!=A_35 | ~m1_subset_1(B_36, A_35) | v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.67/1.59  tff(c_137, plain, (v1_zfmisc_1('#skF_2') | k6_domain_1('#skF_2', '#skF_3')!='#skF_2' | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_125])).
% 2.67/1.59  tff(c_142, plain, (v1_zfmisc_1('#skF_2') | k1_tarski('#skF_3')!='#skF_2' | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_137])).
% 2.67/1.59  tff(c_143, plain, (k1_tarski('#skF_3')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_142])).
% 2.67/1.59  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(k1_tarski(A_3), k1_zfmisc_1(B_4)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.67/1.59  tff(c_76, plain, (![B_29, A_30]: (v1_subset_1(B_29, A_30) | B_29=A_30 | ~m1_subset_1(B_29, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.67/1.59  tff(c_146, plain, (![A_41, B_42]: (v1_subset_1(k1_tarski(A_41), B_42) | k1_tarski(A_41)=B_42 | ~r2_hidden(A_41, B_42))), inference(resolution, [status(thm)], [c_10, c_76])).
% 2.67/1.59  tff(c_26, plain, (~v1_subset_1(k6_domain_1('#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.67/1.59  tff(c_119, plain, (~v1_subset_1(k1_tarski('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_26])).
% 2.67/1.59  tff(c_153, plain, (k1_tarski('#skF_3')='#skF_2' | ~r2_hidden('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_146, c_119])).
% 2.67/1.59  tff(c_161, plain, (~r2_hidden('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_143, c_153])).
% 2.67/1.59  tff(c_166, plain, (~m1_subset_1('#skF_3', '#skF_2') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_4, c_161])).
% 2.67/1.59  tff(c_169, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_166])).
% 2.67/1.59  tff(c_171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_169])).
% 2.67/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.59  
% 2.67/1.59  Inference rules
% 2.67/1.59  ----------------------
% 2.67/1.60  #Ref     : 0
% 2.67/1.60  #Sup     : 27
% 2.67/1.60  #Fact    : 0
% 2.67/1.60  #Define  : 0
% 2.67/1.60  #Split   : 0
% 2.67/1.60  #Chain   : 0
% 2.67/1.60  #Close   : 0
% 2.67/1.60  
% 2.67/1.60  Ordering : KBO
% 2.67/1.60  
% 2.67/1.60  Simplification rules
% 2.67/1.60  ----------------------
% 2.67/1.60  #Subsume      : 3
% 2.67/1.60  #Demod        : 3
% 2.67/1.60  #Tautology    : 11
% 2.67/1.60  #SimpNegUnit  : 4
% 2.67/1.60  #BackRed      : 1
% 2.67/1.60  
% 2.67/1.60  #Partial instantiations: 0
% 2.67/1.60  #Strategies tried      : 1
% 2.67/1.60  
% 2.67/1.60  Timing (in seconds)
% 2.67/1.60  ----------------------
% 2.67/1.60  Preprocessing        : 0.47
% 2.67/1.60  Parsing              : 0.24
% 2.67/1.60  CNF conversion       : 0.03
% 2.67/1.60  Main loop            : 0.24
% 2.67/1.60  Inferencing          : 0.10
% 2.67/1.60  Reduction            : 0.06
% 2.67/1.60  Demodulation         : 0.04
% 2.67/1.60  BG Simplification    : 0.02
% 2.67/1.60  Subsumption          : 0.04
% 2.67/1.60  Abstraction          : 0.02
% 2.67/1.60  MUC search           : 0.00
% 2.67/1.60  Cooper               : 0.00
% 2.67/1.60  Total                : 0.76
% 2.67/1.60  Index Insertion      : 0.00
% 2.67/1.60  Index Deletion       : 0.00
% 2.67/1.60  Index Matching       : 0.00
% 2.67/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
