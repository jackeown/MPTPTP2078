%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:19 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   48 (  82 expanded)
%              Number of leaves         :   20 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   74 ( 178 expanded)
%              Number of equality atoms :   32 (  83 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_73,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_59,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & B != C
        & B != k1_xboole_0
        & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_24,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_22,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_20,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_14,plain,(
    ! [A_8] :
      ( m1_subset_1('#skF_1'(A_8),A_8)
      | ~ v1_zfmisc_1(A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_44,plain,(
    ! [A_17,B_18] :
      ( k6_domain_1(A_17,B_18) = k1_tarski(B_18)
      | ~ m1_subset_1(B_18,A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_61,plain,(
    ! [A_25] :
      ( k6_domain_1(A_25,'#skF_1'(A_25)) = k1_tarski('#skF_1'(A_25))
      | ~ v1_zfmisc_1(A_25)
      | v1_xboole_0(A_25) ) ),
    inference(resolution,[status(thm)],[c_14,c_44])).

tff(c_12,plain,(
    ! [A_8] :
      ( k6_domain_1(A_8,'#skF_1'(A_8)) = A_8
      | ~ v1_zfmisc_1(A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_76,plain,(
    ! [A_26] :
      ( k1_tarski('#skF_1'(A_26)) = A_26
      | ~ v1_zfmisc_1(A_26)
      | v1_xboole_0(A_26)
      | ~ v1_zfmisc_1(A_26)
      | v1_xboole_0(A_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_12])).

tff(c_16,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_18,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_25,plain,(
    ! [A_13,B_14] :
      ( k2_xboole_0(A_13,B_14) = B_14
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_29,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_18,c_25])).

tff(c_54,plain,(
    ! [C_21,B_22,A_23] :
      ( k1_xboole_0 = C_21
      | k1_xboole_0 = B_22
      | C_21 = B_22
      | k2_xboole_0(B_22,C_21) != k1_tarski(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_57,plain,(
    ! [A_23] :
      ( k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | '#skF_2' = '#skF_3'
      | k1_tarski(A_23) != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29,c_54])).

tff(c_58,plain,(
    ! [A_23] :
      ( k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | k1_tarski(A_23) != '#skF_3' ) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_57])).

tff(c_59,plain,(
    ! [A_23] : k1_tarski(A_23) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_90,plain,(
    ! [A_27] :
      ( A_27 != '#skF_3'
      | ~ v1_zfmisc_1(A_27)
      | v1_xboole_0(A_27)
      | ~ v1_zfmisc_1(A_27)
      | v1_xboole_0(A_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_59])).

tff(c_92,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_90])).

tff(c_95,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_92])).

tff(c_97,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_95])).

tff(c_98,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_99,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_101,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_2])).

tff(c_103,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_101])).

tff(c_104,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_107,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_2])).

tff(c_109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_107])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:29:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.15  
% 1.84/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.15  %$ r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 1.84/1.15  
% 1.84/1.15  %Foreground sorts:
% 1.84/1.15  
% 1.84/1.15  
% 1.84/1.15  %Background operators:
% 1.84/1.15  
% 1.84/1.15  
% 1.84/1.15  %Foreground operators:
% 1.84/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.84/1.15  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.84/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.84/1.15  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 1.84/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.84/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.84/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.84/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.15  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.84/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.84/1.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.84/1.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.84/1.15  
% 1.84/1.17  tff(f_73, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 1.84/1.17  tff(f_59, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 1.84/1.17  tff(f_49, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 1.84/1.17  tff(f_30, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.84/1.17  tff(f_42, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 1.84/1.17  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.84/1.17  tff(c_24, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.84/1.17  tff(c_22, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.84/1.17  tff(c_20, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.84/1.17  tff(c_14, plain, (![A_8]: (m1_subset_1('#skF_1'(A_8), A_8) | ~v1_zfmisc_1(A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.84/1.17  tff(c_44, plain, (![A_17, B_18]: (k6_domain_1(A_17, B_18)=k1_tarski(B_18) | ~m1_subset_1(B_18, A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.84/1.17  tff(c_61, plain, (![A_25]: (k6_domain_1(A_25, '#skF_1'(A_25))=k1_tarski('#skF_1'(A_25)) | ~v1_zfmisc_1(A_25) | v1_xboole_0(A_25))), inference(resolution, [status(thm)], [c_14, c_44])).
% 1.84/1.17  tff(c_12, plain, (![A_8]: (k6_domain_1(A_8, '#skF_1'(A_8))=A_8 | ~v1_zfmisc_1(A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.84/1.17  tff(c_76, plain, (![A_26]: (k1_tarski('#skF_1'(A_26))=A_26 | ~v1_zfmisc_1(A_26) | v1_xboole_0(A_26) | ~v1_zfmisc_1(A_26) | v1_xboole_0(A_26))), inference(superposition, [status(thm), theory('equality')], [c_61, c_12])).
% 1.84/1.17  tff(c_16, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.84/1.17  tff(c_18, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.84/1.17  tff(c_25, plain, (![A_13, B_14]: (k2_xboole_0(A_13, B_14)=B_14 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.84/1.17  tff(c_29, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_18, c_25])).
% 1.84/1.17  tff(c_54, plain, (![C_21, B_22, A_23]: (k1_xboole_0=C_21 | k1_xboole_0=B_22 | C_21=B_22 | k2_xboole_0(B_22, C_21)!=k1_tarski(A_23))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.84/1.17  tff(c_57, plain, (![A_23]: (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | '#skF_2'='#skF_3' | k1_tarski(A_23)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_29, c_54])).
% 1.84/1.17  tff(c_58, plain, (![A_23]: (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_tarski(A_23)!='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_16, c_57])).
% 1.84/1.17  tff(c_59, plain, (![A_23]: (k1_tarski(A_23)!='#skF_3')), inference(splitLeft, [status(thm)], [c_58])).
% 1.84/1.17  tff(c_90, plain, (![A_27]: (A_27!='#skF_3' | ~v1_zfmisc_1(A_27) | v1_xboole_0(A_27) | ~v1_zfmisc_1(A_27) | v1_xboole_0(A_27))), inference(superposition, [status(thm), theory('equality')], [c_76, c_59])).
% 1.84/1.17  tff(c_92, plain, (~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_20, c_90])).
% 1.84/1.17  tff(c_95, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_92])).
% 1.84/1.17  tff(c_97, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_95])).
% 1.84/1.17  tff(c_98, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_58])).
% 1.84/1.17  tff(c_99, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_98])).
% 1.84/1.17  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.84/1.17  tff(c_101, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_2])).
% 1.84/1.17  tff(c_103, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_101])).
% 1.84/1.17  tff(c_104, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_98])).
% 1.84/1.17  tff(c_107, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_2])).
% 1.84/1.17  tff(c_109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_107])).
% 1.84/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.17  
% 1.84/1.17  Inference rules
% 1.84/1.17  ----------------------
% 1.84/1.17  #Ref     : 0
% 1.84/1.17  #Sup     : 17
% 1.84/1.17  #Fact    : 0
% 1.84/1.17  #Define  : 0
% 1.84/1.17  #Split   : 2
% 1.84/1.17  #Chain   : 0
% 1.84/1.17  #Close   : 0
% 1.84/1.17  
% 1.84/1.17  Ordering : KBO
% 1.84/1.17  
% 1.84/1.17  Simplification rules
% 1.84/1.17  ----------------------
% 1.84/1.17  #Subsume      : 0
% 1.84/1.17  #Demod        : 7
% 1.84/1.17  #Tautology    : 9
% 1.84/1.17  #SimpNegUnit  : 4
% 1.84/1.17  #BackRed      : 4
% 1.84/1.17  
% 1.84/1.17  #Partial instantiations: 0
% 1.84/1.17  #Strategies tried      : 1
% 1.84/1.17  
% 1.84/1.17  Timing (in seconds)
% 1.84/1.17  ----------------------
% 1.84/1.17  Preprocessing        : 0.28
% 1.84/1.17  Parsing              : 0.15
% 1.84/1.17  CNF conversion       : 0.02
% 1.84/1.17  Main loop            : 0.12
% 1.84/1.17  Inferencing          : 0.05
% 1.84/1.17  Reduction            : 0.04
% 1.84/1.17  Demodulation         : 0.02
% 1.84/1.17  BG Simplification    : 0.01
% 1.84/1.17  Subsumption          : 0.02
% 1.84/1.17  Abstraction          : 0.01
% 1.84/1.17  MUC search           : 0.00
% 1.84/1.17  Cooper               : 0.00
% 1.84/1.17  Total                : 0.44
% 1.84/1.17  Index Insertion      : 0.00
% 1.84/1.17  Index Deletion       : 0.00
% 1.84/1.17  Index Matching       : 0.00
% 1.84/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
