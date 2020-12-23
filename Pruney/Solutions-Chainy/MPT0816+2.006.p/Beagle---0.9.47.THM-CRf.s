%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:55 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   36 (  42 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :   49 (  70 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
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
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ( r1_tarski(A,D)
       => m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_relset_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(c_18,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(k2_zfmisc_1(A_1,C_3),k2_zfmisc_1(B_2,C_3))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [C_3,A_1,B_2] :
      ( r1_tarski(k2_zfmisc_1(C_3,A_1),k2_zfmisc_1(C_3,B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    ! [A_22,B_23,C_24,D_25] :
      ( m1_subset_1(A_22,k1_zfmisc_1(k2_zfmisc_1(B_23,C_24)))
      | ~ r1_tarski(A_22,D_25)
      | ~ m1_subset_1(D_25,k1_zfmisc_1(k2_zfmisc_1(B_23,C_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_142,plain,(
    ! [B_56,B_53,C_52,A_55,C_54] :
      ( m1_subset_1(k2_zfmisc_1(C_54,A_55),k1_zfmisc_1(k2_zfmisc_1(B_56,C_52)))
      | ~ m1_subset_1(k2_zfmisc_1(C_54,B_53),k1_zfmisc_1(k2_zfmisc_1(B_56,C_52)))
      | ~ r1_tarski(A_55,B_53) ) ),
    inference(resolution,[status(thm)],[c_2,c_34])).

tff(c_155,plain,(
    ! [A_59,B_57,C_61,B_58,C_60] :
      ( m1_subset_1(k2_zfmisc_1(C_61,A_59),k1_zfmisc_1(k2_zfmisc_1(B_57,C_60)))
      | ~ r1_tarski(A_59,B_58)
      | ~ r1_tarski(k2_zfmisc_1(C_61,B_58),k2_zfmisc_1(B_57,C_60)) ) ),
    inference(resolution,[status(thm)],[c_8,c_142])).

tff(c_183,plain,(
    ! [C_62,B_63,C_64] :
      ( m1_subset_1(k2_zfmisc_1(C_62,k2_relat_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(B_63,C_64)))
      | ~ r1_tarski(k2_zfmisc_1(C_62,'#skF_2'),k2_zfmisc_1(B_63,C_64)) ) ),
    inference(resolution,[status(thm)],[c_16,c_155])).

tff(c_10,plain,(
    ! [A_6] :
      ( r1_tarski(A_6,k2_zfmisc_1(k1_relat_1(A_6),k2_relat_1(A_6)))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_47,plain,(
    ! [A_6,B_23,C_24] :
      ( m1_subset_1(A_6,k1_zfmisc_1(k2_zfmisc_1(B_23,C_24)))
      | ~ m1_subset_1(k2_zfmisc_1(k1_relat_1(A_6),k2_relat_1(A_6)),k1_zfmisc_1(k2_zfmisc_1(B_23,C_24)))
      | ~ v1_relat_1(A_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_34])).

tff(c_192,plain,(
    ! [B_63,C_64] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(B_63,C_64)))
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),k2_zfmisc_1(B_63,C_64)) ) ),
    inference(resolution,[status(thm)],[c_183,c_47])).

tff(c_218,plain,(
    ! [B_70,C_71] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(B_70,C_71)))
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),k2_zfmisc_1(B_70,C_71)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_192])).

tff(c_244,plain,(
    ! [B_72] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(B_72,'#skF_2')))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_72) ) ),
    inference(resolution,[status(thm)],[c_4,c_218])).

tff(c_14,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_250,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_244,c_14])).

tff(c_255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_250])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:30:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.36  
% 2.00/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.37  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.00/1.37  
% 2.00/1.37  %Foreground sorts:
% 2.00/1.37  
% 2.00/1.37  
% 2.00/1.37  %Background operators:
% 2.00/1.37  
% 2.00/1.37  
% 2.00/1.37  %Foreground operators:
% 2.00/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.00/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.00/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.00/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.00/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.00/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.00/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.00/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.00/1.37  
% 2.28/1.38  tff(f_54, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 2.28/1.38  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 2.28/1.38  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.28/1.38  tff(f_45, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => (r1_tarski(A, D) => m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_relset_1)).
% 2.28/1.38  tff(f_39, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 2.28/1.38  tff(c_18, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.28/1.38  tff(c_4, plain, (![A_1, C_3, B_2]: (r1_tarski(k2_zfmisc_1(A_1, C_3), k2_zfmisc_1(B_2, C_3)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.28/1.38  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.28/1.38  tff(c_16, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.28/1.38  tff(c_8, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.28/1.38  tff(c_2, plain, (![C_3, A_1, B_2]: (r1_tarski(k2_zfmisc_1(C_3, A_1), k2_zfmisc_1(C_3, B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.28/1.38  tff(c_34, plain, (![A_22, B_23, C_24, D_25]: (m1_subset_1(A_22, k1_zfmisc_1(k2_zfmisc_1(B_23, C_24))) | ~r1_tarski(A_22, D_25) | ~m1_subset_1(D_25, k1_zfmisc_1(k2_zfmisc_1(B_23, C_24))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.28/1.38  tff(c_142, plain, (![B_56, B_53, C_52, A_55, C_54]: (m1_subset_1(k2_zfmisc_1(C_54, A_55), k1_zfmisc_1(k2_zfmisc_1(B_56, C_52))) | ~m1_subset_1(k2_zfmisc_1(C_54, B_53), k1_zfmisc_1(k2_zfmisc_1(B_56, C_52))) | ~r1_tarski(A_55, B_53))), inference(resolution, [status(thm)], [c_2, c_34])).
% 2.28/1.38  tff(c_155, plain, (![A_59, B_57, C_61, B_58, C_60]: (m1_subset_1(k2_zfmisc_1(C_61, A_59), k1_zfmisc_1(k2_zfmisc_1(B_57, C_60))) | ~r1_tarski(A_59, B_58) | ~r1_tarski(k2_zfmisc_1(C_61, B_58), k2_zfmisc_1(B_57, C_60)))), inference(resolution, [status(thm)], [c_8, c_142])).
% 2.28/1.38  tff(c_183, plain, (![C_62, B_63, C_64]: (m1_subset_1(k2_zfmisc_1(C_62, k2_relat_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(B_63, C_64))) | ~r1_tarski(k2_zfmisc_1(C_62, '#skF_2'), k2_zfmisc_1(B_63, C_64)))), inference(resolution, [status(thm)], [c_16, c_155])).
% 2.28/1.38  tff(c_10, plain, (![A_6]: (r1_tarski(A_6, k2_zfmisc_1(k1_relat_1(A_6), k2_relat_1(A_6))) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.28/1.38  tff(c_47, plain, (![A_6, B_23, C_24]: (m1_subset_1(A_6, k1_zfmisc_1(k2_zfmisc_1(B_23, C_24))) | ~m1_subset_1(k2_zfmisc_1(k1_relat_1(A_6), k2_relat_1(A_6)), k1_zfmisc_1(k2_zfmisc_1(B_23, C_24))) | ~v1_relat_1(A_6))), inference(resolution, [status(thm)], [c_10, c_34])).
% 2.28/1.38  tff(c_192, plain, (![B_63, C_64]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(B_63, C_64))) | ~v1_relat_1('#skF_3') | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), k2_zfmisc_1(B_63, C_64)))), inference(resolution, [status(thm)], [c_183, c_47])).
% 2.28/1.38  tff(c_218, plain, (![B_70, C_71]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(B_70, C_71))) | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), k2_zfmisc_1(B_70, C_71)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_192])).
% 2.28/1.38  tff(c_244, plain, (![B_72]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(B_72, '#skF_2'))) | ~r1_tarski(k1_relat_1('#skF_3'), B_72))), inference(resolution, [status(thm)], [c_4, c_218])).
% 2.28/1.38  tff(c_14, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.28/1.38  tff(c_250, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_244, c_14])).
% 2.28/1.38  tff(c_255, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_250])).
% 2.28/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.38  
% 2.28/1.38  Inference rules
% 2.28/1.38  ----------------------
% 2.28/1.38  #Ref     : 0
% 2.28/1.38  #Sup     : 53
% 2.28/1.38  #Fact    : 0
% 2.28/1.38  #Define  : 0
% 2.28/1.38  #Split   : 0
% 2.28/1.38  #Chain   : 0
% 2.28/1.38  #Close   : 0
% 2.28/1.38  
% 2.28/1.38  Ordering : KBO
% 2.28/1.38  
% 2.28/1.38  Simplification rules
% 2.28/1.38  ----------------------
% 2.28/1.38  #Subsume      : 0
% 2.28/1.38  #Demod        : 2
% 2.28/1.38  #Tautology    : 1
% 2.28/1.38  #SimpNegUnit  : 0
% 2.28/1.38  #BackRed      : 0
% 2.28/1.38  
% 2.28/1.38  #Partial instantiations: 0
% 2.28/1.38  #Strategies tried      : 1
% 2.28/1.38  
% 2.28/1.38  Timing (in seconds)
% 2.28/1.38  ----------------------
% 2.28/1.38  Preprocessing        : 0.34
% 2.28/1.38  Parsing              : 0.19
% 2.28/1.38  CNF conversion       : 0.02
% 2.28/1.38  Main loop            : 0.22
% 2.28/1.38  Inferencing          : 0.09
% 2.28/1.38  Reduction            : 0.05
% 2.28/1.38  Demodulation         : 0.04
% 2.28/1.38  BG Simplification    : 0.01
% 2.28/1.38  Subsumption          : 0.05
% 2.28/1.38  Abstraction          : 0.01
% 2.28/1.38  MUC search           : 0.00
% 2.28/1.38  Cooper               : 0.00
% 2.28/1.38  Total                : 0.59
% 2.28/1.38  Index Insertion      : 0.00
% 2.28/1.38  Index Deletion       : 0.00
% 2.28/1.38  Index Matching       : 0.00
% 2.28/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
