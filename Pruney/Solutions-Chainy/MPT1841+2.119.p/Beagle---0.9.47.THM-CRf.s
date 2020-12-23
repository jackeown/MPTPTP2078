%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:44 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   43 (  52 expanded)
%              Number of leaves         :   22 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :   66 (  93 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_33,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_28,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ! [C] :
          ( m1_subset_1(C,A)
         => ( A != k1_xboole_0
           => m1_subset_1(k2_tarski(B,C),k1_zfmisc_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_subset_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_24,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_22,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_18,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_45,plain,(
    ! [A_24,B_25] :
      ( k6_domain_1(A_24,B_25) = k1_tarski(B_25)
      | ~ m1_subset_1(B_25,A_24)
      | v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_48,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_45])).

tff(c_51,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_48])).

tff(c_20,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_52,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_20])).

tff(c_8,plain,(
    ! [A_4] : ~ v1_xboole_0(k1_tarski(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_58,plain,(
    ! [B_28,C_29,A_30] :
      ( m1_subset_1(k2_tarski(B_28,C_29),k1_zfmisc_1(A_30))
      | k1_xboole_0 = A_30
      | ~ m1_subset_1(C_29,A_30)
      | ~ m1_subset_1(B_28,A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_74,plain,(
    ! [A_31,A_32] :
      ( m1_subset_1(k1_tarski(A_31),k1_zfmisc_1(A_32))
      | k1_xboole_0 = A_32
      | ~ m1_subset_1(A_31,A_32)
      | ~ m1_subset_1(A_31,A_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_58])).

tff(c_16,plain,(
    ! [B_16,A_14] :
      ( ~ v1_subset_1(B_16,A_14)
      | v1_xboole_0(B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_14))
      | ~ v1_zfmisc_1(A_14)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_77,plain,(
    ! [A_31,A_32] :
      ( ~ v1_subset_1(k1_tarski(A_31),A_32)
      | v1_xboole_0(k1_tarski(A_31))
      | ~ v1_zfmisc_1(A_32)
      | v1_xboole_0(A_32)
      | k1_xboole_0 = A_32
      | ~ m1_subset_1(A_31,A_32) ) ),
    inference(resolution,[status(thm)],[c_74,c_16])).

tff(c_100,plain,(
    ! [A_38,A_39] :
      ( ~ v1_subset_1(k1_tarski(A_38),A_39)
      | ~ v1_zfmisc_1(A_39)
      | v1_xboole_0(A_39)
      | k1_xboole_0 = A_39
      | ~ m1_subset_1(A_38,A_39) ) ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_77])).

tff(c_103,plain,
    ( ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ m1_subset_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_100])).

tff(c_106,plain,
    ( v1_xboole_0('#skF_1')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_103])).

tff(c_107,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_106])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_113,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_2])).

tff(c_115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_113])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:05:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.14  
% 1.81/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.15  %$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.81/1.15  
% 1.81/1.15  %Foreground sorts:
% 1.81/1.15  
% 1.81/1.15  
% 1.81/1.15  %Background operators:
% 1.81/1.15  
% 1.81/1.15  
% 1.81/1.15  %Foreground operators:
% 1.81/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.15  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.81/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.81/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.81/1.15  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 1.81/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.81/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.81/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.81/1.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.81/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.15  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.81/1.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.81/1.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.81/1.15  
% 1.81/1.16  tff(f_84, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 1.81/1.16  tff(f_58, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 1.81/1.16  tff(f_33, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 1.81/1.16  tff(f_28, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.81/1.16  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, A) => (![C]: (m1_subset_1(C, A) => (~(A = k1_xboole_0) => m1_subset_1(k2_tarski(B, C), k1_zfmisc_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_subset_1)).
% 1.81/1.16  tff(f_72, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 1.81/1.16  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.81/1.16  tff(c_24, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.81/1.16  tff(c_22, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.81/1.16  tff(c_18, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.81/1.16  tff(c_45, plain, (![A_24, B_25]: (k6_domain_1(A_24, B_25)=k1_tarski(B_25) | ~m1_subset_1(B_25, A_24) | v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.81/1.16  tff(c_48, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_45])).
% 1.81/1.16  tff(c_51, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_24, c_48])).
% 1.81/1.16  tff(c_20, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.81/1.16  tff(c_52, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_51, c_20])).
% 1.81/1.16  tff(c_8, plain, (![A_4]: (~v1_xboole_0(k1_tarski(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.81/1.16  tff(c_4, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.81/1.16  tff(c_58, plain, (![B_28, C_29, A_30]: (m1_subset_1(k2_tarski(B_28, C_29), k1_zfmisc_1(A_30)) | k1_xboole_0=A_30 | ~m1_subset_1(C_29, A_30) | ~m1_subset_1(B_28, A_30))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.81/1.16  tff(c_74, plain, (![A_31, A_32]: (m1_subset_1(k1_tarski(A_31), k1_zfmisc_1(A_32)) | k1_xboole_0=A_32 | ~m1_subset_1(A_31, A_32) | ~m1_subset_1(A_31, A_32))), inference(superposition, [status(thm), theory('equality')], [c_4, c_58])).
% 1.81/1.16  tff(c_16, plain, (![B_16, A_14]: (~v1_subset_1(B_16, A_14) | v1_xboole_0(B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_14)) | ~v1_zfmisc_1(A_14) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.81/1.16  tff(c_77, plain, (![A_31, A_32]: (~v1_subset_1(k1_tarski(A_31), A_32) | v1_xboole_0(k1_tarski(A_31)) | ~v1_zfmisc_1(A_32) | v1_xboole_0(A_32) | k1_xboole_0=A_32 | ~m1_subset_1(A_31, A_32))), inference(resolution, [status(thm)], [c_74, c_16])).
% 1.81/1.16  tff(c_100, plain, (![A_38, A_39]: (~v1_subset_1(k1_tarski(A_38), A_39) | ~v1_zfmisc_1(A_39) | v1_xboole_0(A_39) | k1_xboole_0=A_39 | ~m1_subset_1(A_38, A_39))), inference(negUnitSimplification, [status(thm)], [c_8, c_77])).
% 1.81/1.16  tff(c_103, plain, (~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1') | k1_xboole_0='#skF_1' | ~m1_subset_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_52, c_100])).
% 1.81/1.16  tff(c_106, plain, (v1_xboole_0('#skF_1') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_103])).
% 1.81/1.16  tff(c_107, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_24, c_106])).
% 1.81/1.16  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.81/1.16  tff(c_113, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_2])).
% 1.81/1.16  tff(c_115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_113])).
% 1.81/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.16  
% 1.81/1.16  Inference rules
% 1.81/1.16  ----------------------
% 1.81/1.16  #Ref     : 0
% 1.81/1.16  #Sup     : 17
% 1.81/1.16  #Fact    : 0
% 1.81/1.16  #Define  : 0
% 1.81/1.16  #Split   : 0
% 1.81/1.16  #Chain   : 0
% 1.81/1.16  #Close   : 0
% 1.81/1.16  
% 1.81/1.16  Ordering : KBO
% 1.81/1.16  
% 1.81/1.16  Simplification rules
% 1.81/1.16  ----------------------
% 1.81/1.16  #Subsume      : 1
% 1.81/1.16  #Demod        : 10
% 1.81/1.16  #Tautology    : 6
% 1.81/1.16  #SimpNegUnit  : 4
% 1.81/1.16  #BackRed      : 7
% 1.81/1.16  
% 1.81/1.16  #Partial instantiations: 0
% 1.81/1.16  #Strategies tried      : 1
% 1.81/1.16  
% 1.81/1.16  Timing (in seconds)
% 1.81/1.16  ----------------------
% 1.81/1.16  Preprocessing        : 0.28
% 1.81/1.16  Parsing              : 0.15
% 1.81/1.16  CNF conversion       : 0.02
% 1.81/1.16  Main loop            : 0.12
% 1.81/1.16  Inferencing          : 0.05
% 1.81/1.16  Reduction            : 0.04
% 1.81/1.16  Demodulation         : 0.02
% 1.81/1.16  BG Simplification    : 0.01
% 1.81/1.16  Subsumption          : 0.02
% 1.81/1.16  Abstraction          : 0.01
% 1.81/1.16  MUC search           : 0.00
% 1.81/1.16  Cooper               : 0.00
% 1.81/1.16  Total                : 0.42
% 1.81/1.16  Index Insertion      : 0.00
% 1.81/1.16  Index Deletion       : 0.00
% 1.81/1.16  Index Matching       : 0.00
% 1.81/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
