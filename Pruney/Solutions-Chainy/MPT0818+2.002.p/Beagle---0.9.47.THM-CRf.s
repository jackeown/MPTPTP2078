%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:57 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   39 (  53 expanded)
%              Number of leaves         :   23 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 (  73 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => ( r1_tarski(k2_relat_1(D),B)
         => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(c_18,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_20,plain,(
    ! [C_16,A_17,B_18] :
      ( v1_relat_1(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_20])).

tff(c_31,plain,(
    ! [C_24,A_25,B_26] :
      ( v4_relat_1(C_24,A_25)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_35,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_31])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k7_relat_1(B_2,A_1) = B_2
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_35,c_2])).

tff(c_41,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_38])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_4,A_3)),A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_45,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_4])).

tff(c_49,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_45])).

tff(c_16,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_51,plain,(
    ! [C_27,A_28,B_29] :
      ( m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ r1_tarski(k2_relat_1(C_27),B_29)
      | ~ r1_tarski(k1_relat_1(C_27),A_28)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_63,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_51,c_14])).

tff(c_70,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_49,c_16,c_63])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:14:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.27  
% 1.82/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.27  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.82/1.27  
% 1.82/1.27  %Foreground sorts:
% 1.82/1.27  
% 1.82/1.27  
% 1.82/1.27  %Background operators:
% 1.82/1.27  
% 1.82/1.27  
% 1.82/1.27  %Foreground operators:
% 1.82/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.27  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.82/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.82/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.82/1.27  tff('#skF_2', type, '#skF_2': $i).
% 1.82/1.27  tff('#skF_3', type, '#skF_3': $i).
% 1.82/1.27  tff('#skF_1', type, '#skF_1': $i).
% 1.82/1.27  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.82/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.82/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.82/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.82/1.27  tff('#skF_4', type, '#skF_4': $i).
% 1.82/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.27  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.82/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.82/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.82/1.27  
% 1.82/1.28  tff(f_60, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 1.82/1.28  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.82/1.28  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.82/1.28  tff(f_31, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 1.82/1.28  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 1.82/1.28  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 1.82/1.28  tff(c_18, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.82/1.28  tff(c_20, plain, (![C_16, A_17, B_18]: (v1_relat_1(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.82/1.28  tff(c_24, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_20])).
% 1.82/1.28  tff(c_31, plain, (![C_24, A_25, B_26]: (v4_relat_1(C_24, A_25) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.82/1.28  tff(c_35, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_18, c_31])).
% 1.82/1.28  tff(c_2, plain, (![B_2, A_1]: (k7_relat_1(B_2, A_1)=B_2 | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.82/1.28  tff(c_38, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_35, c_2])).
% 1.82/1.28  tff(c_41, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_38])).
% 1.82/1.28  tff(c_4, plain, (![B_4, A_3]: (r1_tarski(k1_relat_1(k7_relat_1(B_4, A_3)), A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.82/1.28  tff(c_45, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_41, c_4])).
% 1.82/1.28  tff(c_49, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_45])).
% 1.82/1.28  tff(c_16, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.82/1.28  tff(c_51, plain, (![C_27, A_28, B_29]: (m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~r1_tarski(k2_relat_1(C_27), B_29) | ~r1_tarski(k1_relat_1(C_27), A_28) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.82/1.28  tff(c_14, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.82/1.28  tff(c_63, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_2') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_51, c_14])).
% 1.82/1.28  tff(c_70, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_49, c_16, c_63])).
% 1.82/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.28  
% 1.82/1.28  Inference rules
% 1.82/1.28  ----------------------
% 1.82/1.28  #Ref     : 0
% 1.82/1.28  #Sup     : 11
% 1.82/1.28  #Fact    : 0
% 1.82/1.28  #Define  : 0
% 1.82/1.28  #Split   : 0
% 1.82/1.28  #Chain   : 0
% 1.82/1.28  #Close   : 0
% 1.82/1.28  
% 1.82/1.28  Ordering : KBO
% 1.82/1.28  
% 1.82/1.28  Simplification rules
% 1.82/1.28  ----------------------
% 1.82/1.28  #Subsume      : 0
% 1.82/1.28  #Demod        : 5
% 1.82/1.28  #Tautology    : 3
% 1.82/1.28  #SimpNegUnit  : 0
% 1.82/1.28  #BackRed      : 0
% 1.82/1.28  
% 1.82/1.28  #Partial instantiations: 0
% 1.82/1.28  #Strategies tried      : 1
% 1.82/1.28  
% 1.82/1.28  Timing (in seconds)
% 1.82/1.28  ----------------------
% 1.82/1.28  Preprocessing        : 0.31
% 1.82/1.28  Parsing              : 0.17
% 1.82/1.28  CNF conversion       : 0.02
% 1.82/1.28  Main loop            : 0.11
% 1.82/1.28  Inferencing          : 0.05
% 1.82/1.28  Reduction            : 0.03
% 1.82/1.28  Demodulation         : 0.02
% 1.82/1.28  BG Simplification    : 0.01
% 1.82/1.28  Subsumption          : 0.02
% 1.82/1.28  Abstraction          : 0.00
% 1.82/1.28  MUC search           : 0.00
% 1.82/1.28  Cooper               : 0.00
% 1.82/1.28  Total                : 0.46
% 1.82/1.28  Index Insertion      : 0.00
% 1.82/1.28  Index Deletion       : 0.00
% 1.82/1.28  Index Matching       : 0.00
% 1.82/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
