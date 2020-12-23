%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:57 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   37 (  49 expanded)
%              Number of leaves         :   22 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   44 (  69 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => ( r1_tarski(k2_relat_1(D),B)
         => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_20,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    ! [B_16,A_17] :
      ( v1_relat_1(B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_17))
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_25,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_20,c_22])).

tff(c_28,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_25])).

tff(c_35,plain,(
    ! [C_23,A_24,B_25] :
      ( v4_relat_1(C_23,A_24)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_39,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_35])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_18,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_45,plain,(
    ! [C_28,A_29,B_30] :
      ( m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30)))
      | ~ r1_tarski(k2_relat_1(C_28),B_30)
      | ~ r1_tarski(k1_relat_1(C_28),A_29)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_57,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_45,c_16])).

tff(c_65,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_18,c_57])).

tff(c_68,plain,
    ( ~ v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_65])).

tff(c_72,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_39,c_68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:35:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.13  
% 1.64/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.14  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.64/1.14  
% 1.64/1.14  %Foreground sorts:
% 1.64/1.14  
% 1.64/1.14  
% 1.64/1.14  %Background operators:
% 1.64/1.14  
% 1.64/1.14  
% 1.64/1.14  %Foreground operators:
% 1.64/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.64/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.64/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.14  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.64/1.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.64/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.64/1.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.64/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.64/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.14  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.64/1.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.64/1.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.64/1.14  
% 1.64/1.15  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.64/1.15  tff(f_61, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relset_1)).
% 1.64/1.15  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.64/1.15  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.64/1.15  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 1.64/1.15  tff(f_54, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 1.64/1.15  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.64/1.15  tff(c_20, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.64/1.15  tff(c_22, plain, (![B_16, A_17]: (v1_relat_1(B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_17)) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.64/1.15  tff(c_25, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_20, c_22])).
% 1.64/1.15  tff(c_28, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_25])).
% 1.64/1.15  tff(c_35, plain, (![C_23, A_24, B_25]: (v4_relat_1(C_23, A_24) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.64/1.15  tff(c_39, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_35])).
% 1.64/1.15  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.64/1.15  tff(c_18, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.64/1.15  tff(c_45, plain, (![C_28, A_29, B_30]: (m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))) | ~r1_tarski(k2_relat_1(C_28), B_30) | ~r1_tarski(k1_relat_1(C_28), A_29) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.64/1.15  tff(c_16, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.64/1.15  tff(c_57, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_2') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_45, c_16])).
% 1.64/1.15  tff(c_65, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_18, c_57])).
% 1.64/1.15  tff(c_68, plain, (~v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6, c_65])).
% 1.64/1.15  tff(c_72, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_39, c_68])).
% 1.64/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.15  
% 1.64/1.15  Inference rules
% 1.64/1.15  ----------------------
% 1.64/1.15  #Ref     : 0
% 1.64/1.15  #Sup     : 9
% 1.64/1.15  #Fact    : 0
% 1.64/1.15  #Define  : 0
% 1.64/1.15  #Split   : 0
% 1.64/1.15  #Chain   : 0
% 1.64/1.15  #Close   : 0
% 1.64/1.15  
% 1.64/1.15  Ordering : KBO
% 1.64/1.15  
% 1.64/1.15  Simplification rules
% 1.64/1.15  ----------------------
% 1.64/1.15  #Subsume      : 1
% 1.64/1.15  #Demod        : 6
% 1.64/1.15  #Tautology    : 2
% 1.64/1.15  #SimpNegUnit  : 0
% 1.64/1.15  #BackRed      : 0
% 1.64/1.15  
% 1.64/1.15  #Partial instantiations: 0
% 1.64/1.15  #Strategies tried      : 1
% 1.64/1.15  
% 1.64/1.15  Timing (in seconds)
% 1.64/1.15  ----------------------
% 1.64/1.15  Preprocessing        : 0.25
% 1.64/1.15  Parsing              : 0.14
% 1.64/1.15  CNF conversion       : 0.02
% 1.64/1.15  Main loop            : 0.10
% 1.64/1.15  Inferencing          : 0.05
% 1.64/1.15  Reduction            : 0.03
% 1.64/1.15  Demodulation         : 0.02
% 1.64/1.15  BG Simplification    : 0.01
% 1.64/1.15  Subsumption          : 0.01
% 1.64/1.15  Abstraction          : 0.00
% 1.64/1.15  MUC search           : 0.00
% 1.64/1.15  Cooper               : 0.00
% 1.64/1.15  Total                : 0.38
% 1.64/1.15  Index Insertion      : 0.00
% 1.64/1.15  Index Deletion       : 0.00
% 1.64/1.15  Index Matching       : 0.00
% 1.64/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
