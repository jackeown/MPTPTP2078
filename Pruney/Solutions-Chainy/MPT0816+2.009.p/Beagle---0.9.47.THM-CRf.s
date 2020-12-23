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
% DateTime   : Thu Dec  3 10:06:56 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   31 (  34 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   42 (  54 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( ( r1_tarski(k1_relat_1(C),A)
            & r1_tarski(k2_relat_1(C),B) )
         => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ( r1_tarski(A,D)
       => m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_relset_1)).

tff(c_16,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_14,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r1_tarski(k2_zfmisc_1(A_1,C_3),k2_zfmisc_1(B_2,D_4))
      | ~ r1_tarski(C_3,D_4)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_7] :
      ( r1_tarski(A_7,k2_zfmisc_1(k1_relat_1(A_7),k2_relat_1(A_7)))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_31,plain,(
    ! [A_21,B_22,C_23,D_24] :
      ( m1_subset_1(A_21,k1_zfmisc_1(k2_zfmisc_1(B_22,C_23)))
      | ~ r1_tarski(A_21,D_24)
      | ~ m1_subset_1(D_24,k1_zfmisc_1(k2_zfmisc_1(B_22,C_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_62,plain,(
    ! [A_33,B_34,C_35] :
      ( m1_subset_1(A_33,k1_zfmisc_1(k2_zfmisc_1(B_34,C_35)))
      | ~ m1_subset_1(k2_zfmisc_1(k1_relat_1(A_33),k2_relat_1(A_33)),k1_zfmisc_1(k2_zfmisc_1(B_34,C_35)))
      | ~ v1_relat_1(A_33) ) ),
    inference(resolution,[status(thm)],[c_8,c_31])).

tff(c_72,plain,(
    ! [A_42,B_43,C_44] :
      ( m1_subset_1(A_42,k1_zfmisc_1(k2_zfmisc_1(B_43,C_44)))
      | ~ v1_relat_1(A_42)
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(A_42),k2_relat_1(A_42)),k2_zfmisc_1(B_43,C_44)) ) ),
    inference(resolution,[status(thm)],[c_6,c_62])).

tff(c_83,plain,(
    ! [A_45,B_46,D_47] :
      ( m1_subset_1(A_45,k1_zfmisc_1(k2_zfmisc_1(B_46,D_47)))
      | ~ v1_relat_1(A_45)
      | ~ r1_tarski(k2_relat_1(A_45),D_47)
      | ~ r1_tarski(k1_relat_1(A_45),B_46) ) ),
    inference(resolution,[status(thm)],[c_2,c_72])).

tff(c_12,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_96,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_83,c_12])).

tff(c_103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_18,c_96])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:58:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.22  
% 1.64/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.22  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.64/1.22  
% 1.64/1.22  %Foreground sorts:
% 1.64/1.22  
% 1.64/1.22  
% 1.64/1.22  %Background operators:
% 1.64/1.22  
% 1.64/1.22  
% 1.64/1.22  %Foreground operators:
% 1.64/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.64/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.64/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.64/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.64/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.64/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.64/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.64/1.22  
% 1.90/1.23  tff(f_54, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 1.90/1.23  tff(f_31, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_zfmisc_1)).
% 1.90/1.23  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.90/1.23  tff(f_39, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 1.90/1.23  tff(f_45, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => (r1_tarski(A, D) => m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_relset_1)).
% 1.90/1.23  tff(c_16, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.90/1.23  tff(c_14, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.90/1.23  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.90/1.23  tff(c_2, plain, (![A_1, C_3, B_2, D_4]: (r1_tarski(k2_zfmisc_1(A_1, C_3), k2_zfmisc_1(B_2, D_4)) | ~r1_tarski(C_3, D_4) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.90/1.23  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.90/1.23  tff(c_8, plain, (![A_7]: (r1_tarski(A_7, k2_zfmisc_1(k1_relat_1(A_7), k2_relat_1(A_7))) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.90/1.23  tff(c_31, plain, (![A_21, B_22, C_23, D_24]: (m1_subset_1(A_21, k1_zfmisc_1(k2_zfmisc_1(B_22, C_23))) | ~r1_tarski(A_21, D_24) | ~m1_subset_1(D_24, k1_zfmisc_1(k2_zfmisc_1(B_22, C_23))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.90/1.23  tff(c_62, plain, (![A_33, B_34, C_35]: (m1_subset_1(A_33, k1_zfmisc_1(k2_zfmisc_1(B_34, C_35))) | ~m1_subset_1(k2_zfmisc_1(k1_relat_1(A_33), k2_relat_1(A_33)), k1_zfmisc_1(k2_zfmisc_1(B_34, C_35))) | ~v1_relat_1(A_33))), inference(resolution, [status(thm)], [c_8, c_31])).
% 1.90/1.23  tff(c_72, plain, (![A_42, B_43, C_44]: (m1_subset_1(A_42, k1_zfmisc_1(k2_zfmisc_1(B_43, C_44))) | ~v1_relat_1(A_42) | ~r1_tarski(k2_zfmisc_1(k1_relat_1(A_42), k2_relat_1(A_42)), k2_zfmisc_1(B_43, C_44)))), inference(resolution, [status(thm)], [c_6, c_62])).
% 1.90/1.23  tff(c_83, plain, (![A_45, B_46, D_47]: (m1_subset_1(A_45, k1_zfmisc_1(k2_zfmisc_1(B_46, D_47))) | ~v1_relat_1(A_45) | ~r1_tarski(k2_relat_1(A_45), D_47) | ~r1_tarski(k1_relat_1(A_45), B_46))), inference(resolution, [status(thm)], [c_2, c_72])).
% 1.90/1.23  tff(c_12, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.90/1.23  tff(c_96, plain, (~v1_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_83, c_12])).
% 1.90/1.23  tff(c_103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_18, c_96])).
% 1.90/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.23  
% 1.90/1.23  Inference rules
% 1.90/1.23  ----------------------
% 1.90/1.23  #Ref     : 0
% 1.90/1.23  #Sup     : 18
% 1.90/1.23  #Fact    : 0
% 1.90/1.23  #Define  : 0
% 1.90/1.23  #Split   : 0
% 1.90/1.23  #Chain   : 0
% 1.90/1.23  #Close   : 0
% 1.90/1.23  
% 1.90/1.23  Ordering : KBO
% 1.90/1.23  
% 1.90/1.23  Simplification rules
% 1.90/1.23  ----------------------
% 1.90/1.23  #Subsume      : 0
% 1.90/1.23  #Demod        : 3
% 1.90/1.23  #Tautology    : 1
% 1.90/1.23  #SimpNegUnit  : 0
% 1.90/1.23  #BackRed      : 0
% 1.90/1.23  
% 1.90/1.23  #Partial instantiations: 0
% 1.90/1.23  #Strategies tried      : 1
% 1.90/1.23  
% 1.90/1.23  Timing (in seconds)
% 1.90/1.23  ----------------------
% 1.90/1.23  Preprocessing        : 0.23
% 1.90/1.23  Parsing              : 0.13
% 1.90/1.24  CNF conversion       : 0.02
% 1.90/1.24  Main loop            : 0.14
% 1.90/1.24  Inferencing          : 0.06
% 1.90/1.24  Reduction            : 0.03
% 1.90/1.24  Demodulation         : 0.03
% 1.90/1.24  BG Simplification    : 0.01
% 1.90/1.24  Subsumption          : 0.03
% 1.90/1.24  Abstraction          : 0.01
% 1.90/1.24  MUC search           : 0.00
% 1.90/1.24  Cooper               : 0.00
% 1.90/1.24  Total                : 0.40
% 1.90/1.24  Index Insertion      : 0.00
% 1.90/1.24  Index Deletion       : 0.00
% 1.90/1.24  Index Matching       : 0.00
% 1.90/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
