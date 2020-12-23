%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:19 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   42 (  80 expanded)
%              Number of leaves         :   18 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :   75 ( 208 expanded)
%              Number of equality atoms :   25 (  61 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_63,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_49,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_24,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_18,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_22,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_26,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_20,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_16,plain,(
    ! [A_5] :
      ( m1_subset_1('#skF_1'(A_5),A_5)
      | ~ v1_zfmisc_1(A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_50,plain,(
    ! [A_16,B_17] :
      ( k6_domain_1(A_16,B_17) = k1_tarski(B_17)
      | ~ m1_subset_1(B_17,A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_60,plain,(
    ! [A_20] :
      ( k6_domain_1(A_20,'#skF_1'(A_20)) = k1_tarski('#skF_1'(A_20))
      | ~ v1_zfmisc_1(A_20)
      | v1_xboole_0(A_20) ) ),
    inference(resolution,[status(thm)],[c_16,c_50])).

tff(c_14,plain,(
    ! [A_5] :
      ( k6_domain_1(A_5,'#skF_1'(A_5)) = A_5
      | ~ v1_zfmisc_1(A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_75,plain,(
    ! [A_21] :
      ( k1_tarski('#skF_1'(A_21)) = A_21
      | ~ v1_zfmisc_1(A_21)
      | v1_xboole_0(A_21)
      | ~ v1_zfmisc_1(A_21)
      | v1_xboole_0(A_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_14])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( k1_tarski(B_2) = A_1
      | k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_tarski(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_119,plain,(
    ! [A_25,A_26] :
      ( k1_tarski('#skF_1'(A_25)) = A_26
      | k1_xboole_0 = A_26
      | ~ r1_tarski(A_26,A_25)
      | ~ v1_zfmisc_1(A_25)
      | v1_xboole_0(A_25)
      | ~ v1_zfmisc_1(A_25)
      | v1_xboole_0(A_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_4])).

tff(c_131,plain,
    ( k1_tarski('#skF_1'('#skF_3')) = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_119])).

tff(c_142,plain,
    ( k1_tarski('#skF_1'('#skF_3')) = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_131])).

tff(c_143,plain,
    ( k1_tarski('#skF_1'('#skF_3')) = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_142])).

tff(c_144,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_143])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_149,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_2])).

tff(c_151,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_149])).

tff(c_152,plain,(
    k1_tarski('#skF_1'('#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_66,plain,(
    ! [A_20] :
      ( k1_tarski('#skF_1'(A_20)) = A_20
      | ~ v1_zfmisc_1(A_20)
      | v1_xboole_0(A_20)
      | ~ v1_zfmisc_1(A_20)
      | v1_xboole_0(A_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_14])).

tff(c_163,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_66])).

tff(c_187,plain,
    ( '#skF_2' = '#skF_3'
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_163])).

tff(c_189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_18,c_187])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:46:09 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.16  
% 1.87/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.16  %$ r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 1.87/1.16  
% 1.87/1.16  %Foreground sorts:
% 1.87/1.16  
% 1.87/1.16  
% 1.87/1.16  %Background operators:
% 1.87/1.16  
% 1.87/1.16  
% 1.87/1.16  %Foreground operators:
% 1.87/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.87/1.16  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.87/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.87/1.16  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 1.87/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.16  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.87/1.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.87/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.87/1.16  
% 1.87/1.17  tff(f_63, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 1.87/1.17  tff(f_49, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 1.87/1.17  tff(f_39, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 1.87/1.17  tff(f_32, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 1.87/1.17  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.87/1.17  tff(c_24, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.87/1.17  tff(c_18, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.87/1.17  tff(c_22, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.87/1.17  tff(c_26, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.87/1.17  tff(c_20, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.87/1.17  tff(c_16, plain, (![A_5]: (m1_subset_1('#skF_1'(A_5), A_5) | ~v1_zfmisc_1(A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.87/1.17  tff(c_50, plain, (![A_16, B_17]: (k6_domain_1(A_16, B_17)=k1_tarski(B_17) | ~m1_subset_1(B_17, A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.87/1.17  tff(c_60, plain, (![A_20]: (k6_domain_1(A_20, '#skF_1'(A_20))=k1_tarski('#skF_1'(A_20)) | ~v1_zfmisc_1(A_20) | v1_xboole_0(A_20))), inference(resolution, [status(thm)], [c_16, c_50])).
% 1.87/1.17  tff(c_14, plain, (![A_5]: (k6_domain_1(A_5, '#skF_1'(A_5))=A_5 | ~v1_zfmisc_1(A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.87/1.17  tff(c_75, plain, (![A_21]: (k1_tarski('#skF_1'(A_21))=A_21 | ~v1_zfmisc_1(A_21) | v1_xboole_0(A_21) | ~v1_zfmisc_1(A_21) | v1_xboole_0(A_21))), inference(superposition, [status(thm), theory('equality')], [c_60, c_14])).
% 1.87/1.17  tff(c_4, plain, (![B_2, A_1]: (k1_tarski(B_2)=A_1 | k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_tarski(B_2)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.87/1.17  tff(c_119, plain, (![A_25, A_26]: (k1_tarski('#skF_1'(A_25))=A_26 | k1_xboole_0=A_26 | ~r1_tarski(A_26, A_25) | ~v1_zfmisc_1(A_25) | v1_xboole_0(A_25) | ~v1_zfmisc_1(A_25) | v1_xboole_0(A_25))), inference(superposition, [status(thm), theory('equality')], [c_75, c_4])).
% 1.87/1.17  tff(c_131, plain, (k1_tarski('#skF_1'('#skF_3'))='#skF_2' | k1_xboole_0='#skF_2' | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_20, c_119])).
% 1.87/1.17  tff(c_142, plain, (k1_tarski('#skF_1'('#skF_3'))='#skF_2' | k1_xboole_0='#skF_2' | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_131])).
% 1.87/1.17  tff(c_143, plain, (k1_tarski('#skF_1'('#skF_3'))='#skF_2' | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_24, c_142])).
% 1.87/1.17  tff(c_144, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_143])).
% 1.87/1.17  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.87/1.17  tff(c_149, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_2])).
% 1.87/1.17  tff(c_151, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_149])).
% 1.87/1.17  tff(c_152, plain, (k1_tarski('#skF_1'('#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_143])).
% 1.87/1.17  tff(c_66, plain, (![A_20]: (k1_tarski('#skF_1'(A_20))=A_20 | ~v1_zfmisc_1(A_20) | v1_xboole_0(A_20) | ~v1_zfmisc_1(A_20) | v1_xboole_0(A_20))), inference(superposition, [status(thm), theory('equality')], [c_60, c_14])).
% 1.87/1.17  tff(c_163, plain, ('#skF_2'='#skF_3' | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_152, c_66])).
% 1.87/1.17  tff(c_187, plain, ('#skF_2'='#skF_3' | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_163])).
% 1.87/1.17  tff(c_189, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_18, c_187])).
% 1.87/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.17  
% 1.87/1.17  Inference rules
% 1.87/1.17  ----------------------
% 1.87/1.17  #Ref     : 0
% 1.87/1.17  #Sup     : 37
% 1.87/1.17  #Fact    : 0
% 1.87/1.17  #Define  : 0
% 1.87/1.17  #Split   : 1
% 1.87/1.17  #Chain   : 0
% 1.87/1.17  #Close   : 0
% 1.87/1.17  
% 1.87/1.17  Ordering : KBO
% 1.87/1.17  
% 1.87/1.17  Simplification rules
% 1.87/1.17  ----------------------
% 1.87/1.17  #Subsume      : 4
% 1.87/1.17  #Demod        : 13
% 1.87/1.17  #Tautology    : 15
% 1.87/1.17  #SimpNegUnit  : 5
% 1.87/1.17  #BackRed      : 5
% 1.87/1.17  
% 1.87/1.17  #Partial instantiations: 0
% 1.87/1.17  #Strategies tried      : 1
% 1.87/1.17  
% 1.87/1.17  Timing (in seconds)
% 1.87/1.17  ----------------------
% 1.87/1.17  Preprocessing        : 0.27
% 1.87/1.17  Parsing              : 0.14
% 1.87/1.17  CNF conversion       : 0.02
% 1.87/1.17  Main loop            : 0.15
% 1.87/1.17  Inferencing          : 0.06
% 1.87/1.17  Reduction            : 0.05
% 1.87/1.17  Demodulation         : 0.03
% 1.87/1.17  BG Simplification    : 0.01
% 1.87/1.17  Subsumption          : 0.03
% 1.87/1.17  Abstraction          : 0.01
% 1.87/1.17  MUC search           : 0.00
% 1.87/1.17  Cooper               : 0.00
% 1.87/1.17  Total                : 0.45
% 1.87/1.17  Index Insertion      : 0.00
% 1.87/1.17  Index Deletion       : 0.00
% 1.87/1.17  Index Matching       : 0.00
% 1.87/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
