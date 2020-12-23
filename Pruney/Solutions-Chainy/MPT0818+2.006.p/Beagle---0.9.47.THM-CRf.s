%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:57 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   42 (  62 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   51 (  91 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => ( r1_tarski(k2_relat_1(D),B)
         => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_20,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_22,plain,(
    ! [B_18,A_19] :
      ( v1_relat_1(B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_19))
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_25,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_20,c_22])).

tff(c_28,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_25])).

tff(c_36,plain,(
    ! [C_27,A_28,B_29] :
      ( v4_relat_1(C_27,A_28)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_40,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_36])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( k7_relat_1(B_7,A_6) = B_7
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_43,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_6])).

tff(c_46,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_43])).

tff(c_8,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_9,A_8)),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_50,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_8])).

tff(c_54,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_50])).

tff(c_18,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_56,plain,(
    ! [C_30,A_31,B_32] :
      ( m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ r1_tarski(k2_relat_1(C_30),B_32)
      | ~ r1_tarski(k1_relat_1(C_30),A_31)
      | ~ v1_relat_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_16,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_68,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_16])).

tff(c_77,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_54,c_18,c_68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:19:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.11  
% 1.73/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.12  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.73/1.12  
% 1.73/1.12  %Foreground sorts:
% 1.73/1.12  
% 1.73/1.12  
% 1.73/1.12  %Background operators:
% 1.73/1.12  
% 1.73/1.12  
% 1.73/1.12  %Foreground operators:
% 1.73/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.12  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.73/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.73/1.12  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.73/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.73/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.73/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.73/1.12  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.73/1.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.73/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.73/1.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.73/1.12  tff('#skF_4', type, '#skF_4': $i).
% 1.73/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.12  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.73/1.12  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.73/1.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.73/1.12  
% 1.73/1.13  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.73/1.13  tff(f_65, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 1.73/1.13  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.73/1.13  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.73/1.13  tff(f_40, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 1.73/1.13  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 1.73/1.13  tff(f_58, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 1.73/1.13  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.73/1.13  tff(c_20, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.73/1.13  tff(c_22, plain, (![B_18, A_19]: (v1_relat_1(B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(A_19)) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.73/1.13  tff(c_25, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_20, c_22])).
% 1.73/1.13  tff(c_28, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_25])).
% 1.73/1.13  tff(c_36, plain, (![C_27, A_28, B_29]: (v4_relat_1(C_27, A_28) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.73/1.13  tff(c_40, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_36])).
% 1.73/1.13  tff(c_6, plain, (![B_7, A_6]: (k7_relat_1(B_7, A_6)=B_7 | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.73/1.13  tff(c_43, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_6])).
% 1.73/1.13  tff(c_46, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_43])).
% 1.73/1.13  tff(c_8, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(k7_relat_1(B_9, A_8)), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.73/1.13  tff(c_50, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_46, c_8])).
% 1.73/1.13  tff(c_54, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_50])).
% 1.73/1.13  tff(c_18, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.73/1.13  tff(c_56, plain, (![C_30, A_31, B_32]: (m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~r1_tarski(k2_relat_1(C_30), B_32) | ~r1_tarski(k1_relat_1(C_30), A_31) | ~v1_relat_1(C_30))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.73/1.13  tff(c_16, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.73/1.13  tff(c_68, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_2') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_16])).
% 1.73/1.13  tff(c_77, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_54, c_18, c_68])).
% 1.73/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.13  
% 1.73/1.13  Inference rules
% 1.73/1.13  ----------------------
% 1.73/1.13  #Ref     : 0
% 1.73/1.13  #Sup     : 11
% 1.73/1.13  #Fact    : 0
% 1.73/1.13  #Define  : 0
% 1.73/1.13  #Split   : 0
% 1.73/1.13  #Chain   : 0
% 1.73/1.13  #Close   : 0
% 1.73/1.13  
% 1.73/1.13  Ordering : KBO
% 1.73/1.13  
% 1.73/1.13  Simplification rules
% 1.73/1.13  ----------------------
% 1.73/1.13  #Subsume      : 0
% 1.73/1.13  #Demod        : 7
% 1.73/1.13  #Tautology    : 3
% 1.73/1.13  #SimpNegUnit  : 0
% 1.73/1.13  #BackRed      : 0
% 1.73/1.13  
% 1.73/1.13  #Partial instantiations: 0
% 1.73/1.13  #Strategies tried      : 1
% 1.73/1.13  
% 1.73/1.13  Timing (in seconds)
% 1.73/1.13  ----------------------
% 1.73/1.13  Preprocessing        : 0.27
% 1.73/1.13  Parsing              : 0.15
% 1.73/1.13  CNF conversion       : 0.02
% 1.73/1.13  Main loop            : 0.11
% 1.73/1.13  Inferencing          : 0.05
% 1.73/1.13  Reduction            : 0.03
% 1.73/1.13  Demodulation         : 0.02
% 1.73/1.13  BG Simplification    : 0.01
% 1.73/1.13  Subsumption          : 0.01
% 1.73/1.13  Abstraction          : 0.00
% 1.73/1.13  MUC search           : 0.00
% 1.73/1.13  Cooper               : 0.00
% 1.73/1.13  Total                : 0.40
% 1.73/1.13  Index Insertion      : 0.00
% 1.73/1.13  Index Deletion       : 0.00
% 1.73/1.13  Index Matching       : 0.00
% 1.73/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
