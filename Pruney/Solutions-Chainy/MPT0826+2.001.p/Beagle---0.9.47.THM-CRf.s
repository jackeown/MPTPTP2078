%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:14 EST 2020

% Result     : Theorem 1.51s
% Output     : CNFRefutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   25 (  28 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :    3
%              Number of atoms          :   24 (  30 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(c_8,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_4] : k1_relat_1(k6_relat_1(A_4)) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_4] : k2_relat_1(k6_relat_1(A_4)) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_45,plain,(
    ! [C_14,A_15,B_16] :
      ( m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16)))
      | ~ r1_tarski(k2_relat_1(C_14),B_16)
      | ~ r1_tarski(k1_relat_1(C_14),A_15)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ~ m1_subset_1(k6_relat_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_48,plain,
    ( ~ r1_tarski(k2_relat_1(k6_relat_1('#skF_1')),'#skF_1')
    | ~ r1_tarski(k1_relat_1(k6_relat_1('#skF_1')),'#skF_1')
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_45,c_16])).

tff(c_52,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_6,c_10,c_6,c_12,c_48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:17:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.51/1.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.51/1.06  
% 1.51/1.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.51/1.07  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1
% 1.51/1.07  
% 1.51/1.07  %Foreground sorts:
% 1.51/1.07  
% 1.51/1.07  
% 1.51/1.07  %Background operators:
% 1.51/1.07  
% 1.51/1.07  
% 1.51/1.07  %Foreground operators:
% 1.51/1.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.51/1.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.51/1.07  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.51/1.07  tff('#skF_1', type, '#skF_1': $i).
% 1.51/1.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.51/1.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.51/1.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.51/1.07  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.51/1.07  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.51/1.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.51/1.07  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.51/1.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.51/1.07  
% 1.51/1.07  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.51/1.07  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.51/1.07  tff(f_37, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.51/1.07  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 1.51/1.07  tff(f_48, negated_conjecture, ~(![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 1.51/1.07  tff(c_8, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.51/1.07  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.51/1.07  tff(c_10, plain, (![A_4]: (k1_relat_1(k6_relat_1(A_4))=A_4)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.51/1.07  tff(c_12, plain, (![A_4]: (k2_relat_1(k6_relat_1(A_4))=A_4)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.51/1.07  tff(c_45, plain, (![C_14, A_15, B_16]: (m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))) | ~r1_tarski(k2_relat_1(C_14), B_16) | ~r1_tarski(k1_relat_1(C_14), A_15) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.51/1.07  tff(c_16, plain, (~m1_subset_1(k6_relat_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.51/1.07  tff(c_48, plain, (~r1_tarski(k2_relat_1(k6_relat_1('#skF_1')), '#skF_1') | ~r1_tarski(k1_relat_1(k6_relat_1('#skF_1')), '#skF_1') | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_45, c_16])).
% 1.51/1.07  tff(c_52, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_6, c_10, c_6, c_12, c_48])).
% 1.51/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.51/1.07  
% 1.51/1.07  Inference rules
% 1.51/1.07  ----------------------
% 1.51/1.07  #Ref     : 0
% 1.51/1.07  #Sup     : 6
% 1.51/1.07  #Fact    : 0
% 1.51/1.07  #Define  : 0
% 1.51/1.07  #Split   : 0
% 1.51/1.07  #Chain   : 0
% 1.51/1.07  #Close   : 0
% 1.51/1.07  
% 1.51/1.07  Ordering : KBO
% 1.51/1.07  
% 1.51/1.07  Simplification rules
% 1.51/1.07  ----------------------
% 1.51/1.07  #Subsume      : 0
% 1.51/1.07  #Demod        : 7
% 1.51/1.07  #Tautology    : 6
% 1.51/1.07  #SimpNegUnit  : 0
% 1.51/1.07  #BackRed      : 0
% 1.51/1.07  
% 1.51/1.07  #Partial instantiations: 0
% 1.51/1.08  #Strategies tried      : 1
% 1.51/1.08  
% 1.51/1.08  Timing (in seconds)
% 1.51/1.08  ----------------------
% 1.51/1.08  Preprocessing        : 0.25
% 1.51/1.08  Parsing              : 0.14
% 1.51/1.08  CNF conversion       : 0.01
% 1.51/1.08  Main loop            : 0.07
% 1.51/1.08  Inferencing          : 0.03
% 1.51/1.08  Reduction            : 0.02
% 1.51/1.08  Demodulation         : 0.02
% 1.51/1.08  BG Simplification    : 0.01
% 1.51/1.08  Subsumption          : 0.01
% 1.51/1.08  Abstraction          : 0.00
% 1.51/1.08  MUC search           : 0.00
% 1.51/1.08  Cooper               : 0.00
% 1.51/1.08  Total                : 0.35
% 1.51/1.08  Index Insertion      : 0.00
% 1.51/1.08  Index Deletion       : 0.00
% 1.51/1.08  Index Matching       : 0.00
% 1.51/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
