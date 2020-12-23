%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:56 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   42 (  54 expanded)
%              Number of leaves         :   22 (  29 expanded)
%              Depth                    :    5
%              Number of atoms          :   56 (  80 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => ( r1_tarski(k1_relat_1(D),B)
         => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_42,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_44,axiom,(
    ! [A,B] : r1_tarski(k2_relat_1(k2_zfmisc_1(A,B)),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(B))
         => v5_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(c_20,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_23,plain,(
    ! [C_21,A_22,B_23] :
      ( v1_relat_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_27,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_23])).

tff(c_8,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10,plain,(
    ! [A_9,B_10] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_9,B_10)),B_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_28,plain,(
    ! [B_24,A_25] :
      ( v5_relat_1(B_24,A_25)
      | ~ r1_tarski(k2_relat_1(B_24),A_25)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_31,plain,(
    ! [A_9,B_10] :
      ( v5_relat_1(k2_zfmisc_1(A_9,B_10),B_10)
      | ~ v1_relat_1(k2_zfmisc_1(A_9,B_10)) ) ),
    inference(resolution,[status(thm)],[c_10,c_28])).

tff(c_34,plain,(
    ! [A_9,B_10] : v5_relat_1(k2_zfmisc_1(A_9,B_10),B_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_31])).

tff(c_41,plain,(
    ! [C_30,A_31,B_32] :
      ( v5_relat_1(C_30,A_31)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(B_32))
      | ~ v5_relat_1(B_32,A_31)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_43,plain,(
    ! [A_31] :
      ( v5_relat_1('#skF_4',A_31)
      | ~ v5_relat_1(k2_zfmisc_1('#skF_1','#skF_3'),A_31)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_20,c_41])).

tff(c_47,plain,(
    ! [A_33] :
      ( v5_relat_1('#skF_4',A_33)
      | ~ v5_relat_1(k2_zfmisc_1('#skF_1','#skF_3'),A_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_43])).

tff(c_52,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_47])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( r1_tarski(k2_relat_1(B_6),A_5)
      | ~ v5_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_18,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_53,plain,(
    ! [C_34,A_35,B_36] :
      ( m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36)))
      | ~ r1_tarski(k2_relat_1(C_34),B_36)
      | ~ r1_tarski(k1_relat_1(C_34),A_35)
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_61,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_53,c_16])).

tff(c_68,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_18,c_61])).

tff(c_71,plain,
    ( ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_68])).

tff(c_75,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_52,c_71])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:03:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.12  
% 1.65/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.12  %$ v5_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.65/1.12  
% 1.65/1.12  %Foreground sorts:
% 1.65/1.12  
% 1.65/1.12  
% 1.65/1.12  %Background operators:
% 1.65/1.12  
% 1.65/1.12  
% 1.65/1.12  %Foreground operators:
% 1.65/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.65/1.12  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.65/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.65/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.12  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.65/1.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.65/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.65/1.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.65/1.12  tff('#skF_4', type, '#skF_4': $i).
% 1.65/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.12  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.65/1.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.65/1.12  
% 1.77/1.13  tff(f_63, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 1.77/1.13  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.77/1.13  tff(f_42, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.77/1.13  tff(f_44, axiom, (![A, B]: r1_tarski(k2_relat_1(k2_zfmisc_1(A, B)), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t194_relat_1)).
% 1.77/1.13  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 1.77/1.13  tff(f_34, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(B)) => v5_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_relat_1)).
% 1.77/1.13  tff(f_56, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 1.77/1.13  tff(c_20, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.77/1.13  tff(c_23, plain, (![C_21, A_22, B_23]: (v1_relat_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.77/1.13  tff(c_27, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_23])).
% 1.77/1.13  tff(c_8, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.77/1.13  tff(c_10, plain, (![A_9, B_10]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_9, B_10)), B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.77/1.13  tff(c_28, plain, (![B_24, A_25]: (v5_relat_1(B_24, A_25) | ~r1_tarski(k2_relat_1(B_24), A_25) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.77/1.13  tff(c_31, plain, (![A_9, B_10]: (v5_relat_1(k2_zfmisc_1(A_9, B_10), B_10) | ~v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(resolution, [status(thm)], [c_10, c_28])).
% 1.77/1.13  tff(c_34, plain, (![A_9, B_10]: (v5_relat_1(k2_zfmisc_1(A_9, B_10), B_10))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_31])).
% 1.77/1.13  tff(c_41, plain, (![C_30, A_31, B_32]: (v5_relat_1(C_30, A_31) | ~m1_subset_1(C_30, k1_zfmisc_1(B_32)) | ~v5_relat_1(B_32, A_31) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.77/1.13  tff(c_43, plain, (![A_31]: (v5_relat_1('#skF_4', A_31) | ~v5_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'), A_31) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_20, c_41])).
% 1.77/1.13  tff(c_47, plain, (![A_33]: (v5_relat_1('#skF_4', A_33) | ~v5_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'), A_33))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_43])).
% 1.77/1.13  tff(c_52, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_47])).
% 1.77/1.13  tff(c_6, plain, (![B_6, A_5]: (r1_tarski(k2_relat_1(B_6), A_5) | ~v5_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.77/1.13  tff(c_18, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.77/1.13  tff(c_53, plain, (![C_34, A_35, B_36]: (m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))) | ~r1_tarski(k2_relat_1(C_34), B_36) | ~r1_tarski(k1_relat_1(C_34), A_35) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.77/1.13  tff(c_16, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.77/1.13  tff(c_61, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_53, c_16])).
% 1.77/1.13  tff(c_68, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_27, c_18, c_61])).
% 1.77/1.13  tff(c_71, plain, (~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6, c_68])).
% 1.77/1.13  tff(c_75, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27, c_52, c_71])).
% 1.77/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.13  
% 1.77/1.13  Inference rules
% 1.77/1.13  ----------------------
% 1.77/1.13  #Ref     : 0
% 1.77/1.13  #Sup     : 9
% 1.77/1.13  #Fact    : 0
% 1.77/1.13  #Define  : 0
% 1.77/1.13  #Split   : 0
% 1.77/1.13  #Chain   : 0
% 1.77/1.13  #Close   : 0
% 1.77/1.13  
% 1.77/1.13  Ordering : KBO
% 1.77/1.13  
% 1.77/1.13  Simplification rules
% 1.77/1.13  ----------------------
% 1.77/1.13  #Subsume      : 0
% 1.77/1.13  #Demod        : 7
% 1.77/1.13  #Tautology    : 2
% 1.77/1.13  #SimpNegUnit  : 0
% 1.77/1.13  #BackRed      : 0
% 1.77/1.13  
% 1.77/1.13  #Partial instantiations: 0
% 1.77/1.13  #Strategies tried      : 1
% 1.77/1.13  
% 1.77/1.13  Timing (in seconds)
% 1.77/1.13  ----------------------
% 1.77/1.13  Preprocessing        : 0.27
% 1.77/1.13  Parsing              : 0.16
% 1.77/1.13  CNF conversion       : 0.02
% 1.77/1.13  Main loop            : 0.11
% 1.77/1.13  Inferencing          : 0.05
% 1.77/1.13  Reduction            : 0.03
% 1.77/1.13  Demodulation         : 0.02
% 1.77/1.13  BG Simplification    : 0.01
% 1.77/1.13  Subsumption          : 0.02
% 1.77/1.14  Abstraction          : 0.00
% 1.77/1.14  MUC search           : 0.00
% 1.77/1.14  Cooper               : 0.00
% 1.77/1.14  Total                : 0.40
% 1.77/1.14  Index Insertion      : 0.00
% 1.77/1.14  Index Deletion       : 0.00
% 1.77/1.14  Index Matching       : 0.00
% 1.77/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
