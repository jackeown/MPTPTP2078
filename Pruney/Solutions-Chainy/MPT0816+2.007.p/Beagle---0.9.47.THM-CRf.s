%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:55 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   37 (  40 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   47 (  59 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( ( r1_tarski(k1_relat_1(C),A)
            & r1_tarski(k2_relat_1(C),B) )
         => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_39,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_39,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_47,plain,(
    ~ r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_39,c_14])).

tff(c_18,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [A_6,C_8,B_7,D_9] :
      ( r1_tarski(k2_zfmisc_1(A_6,C_8),k2_zfmisc_1(B_7,D_9))
      | ~ r1_tarski(C_8,D_9)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_105,plain,(
    ! [A_26] :
      ( r1_tarski(A_26,k2_zfmisc_1(k1_relat_1(A_26),k2_relat_1(A_26)))
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_162,plain,(
    ! [A_35] :
      ( k2_xboole_0(A_35,k2_zfmisc_1(k1_relat_1(A_35),k2_relat_1(A_35))) = k2_zfmisc_1(k1_relat_1(A_35),k2_relat_1(A_35))
      | ~ v1_relat_1(A_35) ) ),
    inference(resolution,[status(thm)],[c_105,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_194,plain,(
    ! [A_36,C_37] :
      ( r1_tarski(A_36,C_37)
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(A_36),k2_relat_1(A_36)),C_37)
      | ~ v1_relat_1(A_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_2])).

tff(c_321,plain,(
    ! [A_50,B_51,D_52] :
      ( r1_tarski(A_50,k2_zfmisc_1(B_51,D_52))
      | ~ v1_relat_1(A_50)
      | ~ r1_tarski(k2_relat_1(A_50),D_52)
      | ~ r1_tarski(k1_relat_1(A_50),B_51) ) ),
    inference(resolution,[status(thm)],[c_6,c_194])).

tff(c_333,plain,(
    ! [B_51] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(B_51,'#skF_2'))
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_51) ) ),
    inference(resolution,[status(thm)],[c_16,c_321])).

tff(c_345,plain,(
    ! [B_53] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(B_53,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_333])).

tff(c_362,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_18,c_345])).

tff(c_370,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_362])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:20:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.32  
% 2.11/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.32  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.11/1.32  
% 2.11/1.32  %Foreground sorts:
% 2.11/1.32  
% 2.11/1.32  
% 2.11/1.32  %Background operators:
% 2.11/1.32  
% 2.11/1.32  
% 2.11/1.32  %Foreground operators:
% 2.11/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.11/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.11/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.11/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.11/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.11/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.11/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.11/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.11/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.11/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.11/1.32  
% 2.11/1.33  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.11/1.33  tff(f_56, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 2.11/1.33  tff(f_39, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_zfmisc_1)).
% 2.11/1.33  tff(f_47, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 2.11/1.33  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.11/1.33  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.11/1.33  tff(c_39, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.11/1.33  tff(c_14, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.11/1.33  tff(c_47, plain, (~r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_39, c_14])).
% 2.11/1.33  tff(c_18, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.11/1.33  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.11/1.33  tff(c_16, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.11/1.33  tff(c_6, plain, (![A_6, C_8, B_7, D_9]: (r1_tarski(k2_zfmisc_1(A_6, C_8), k2_zfmisc_1(B_7, D_9)) | ~r1_tarski(C_8, D_9) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.11/1.33  tff(c_105, plain, (![A_26]: (r1_tarski(A_26, k2_zfmisc_1(k1_relat_1(A_26), k2_relat_1(A_26))) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.11/1.33  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.11/1.33  tff(c_162, plain, (![A_35]: (k2_xboole_0(A_35, k2_zfmisc_1(k1_relat_1(A_35), k2_relat_1(A_35)))=k2_zfmisc_1(k1_relat_1(A_35), k2_relat_1(A_35)) | ~v1_relat_1(A_35))), inference(resolution, [status(thm)], [c_105, c_4])).
% 2.11/1.33  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.11/1.33  tff(c_194, plain, (![A_36, C_37]: (r1_tarski(A_36, C_37) | ~r1_tarski(k2_zfmisc_1(k1_relat_1(A_36), k2_relat_1(A_36)), C_37) | ~v1_relat_1(A_36))), inference(superposition, [status(thm), theory('equality')], [c_162, c_2])).
% 2.11/1.33  tff(c_321, plain, (![A_50, B_51, D_52]: (r1_tarski(A_50, k2_zfmisc_1(B_51, D_52)) | ~v1_relat_1(A_50) | ~r1_tarski(k2_relat_1(A_50), D_52) | ~r1_tarski(k1_relat_1(A_50), B_51))), inference(resolution, [status(thm)], [c_6, c_194])).
% 2.11/1.33  tff(c_333, plain, (![B_51]: (r1_tarski('#skF_3', k2_zfmisc_1(B_51, '#skF_2')) | ~v1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), B_51))), inference(resolution, [status(thm)], [c_16, c_321])).
% 2.11/1.33  tff(c_345, plain, (![B_53]: (r1_tarski('#skF_3', k2_zfmisc_1(B_53, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), B_53))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_333])).
% 2.11/1.33  tff(c_362, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_345])).
% 2.11/1.33  tff(c_370, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_362])).
% 2.11/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.33  
% 2.11/1.33  Inference rules
% 2.11/1.33  ----------------------
% 2.11/1.33  #Ref     : 0
% 2.11/1.33  #Sup     : 86
% 2.11/1.33  #Fact    : 0
% 2.35/1.33  #Define  : 0
% 2.35/1.33  #Split   : 4
% 2.35/1.33  #Chain   : 0
% 2.35/1.33  #Close   : 0
% 2.35/1.33  
% 2.35/1.33  Ordering : KBO
% 2.35/1.33  
% 2.35/1.33  Simplification rules
% 2.35/1.33  ----------------------
% 2.35/1.33  #Subsume      : 10
% 2.35/1.33  #Demod        : 13
% 2.35/1.33  #Tautology    : 25
% 2.35/1.33  #SimpNegUnit  : 1
% 2.35/1.33  #BackRed      : 0
% 2.35/1.33  
% 2.35/1.33  #Partial instantiations: 0
% 2.35/1.33  #Strategies tried      : 1
% 2.35/1.33  
% 2.35/1.33  Timing (in seconds)
% 2.35/1.33  ----------------------
% 2.35/1.33  Preprocessing        : 0.24
% 2.35/1.33  Parsing              : 0.14
% 2.35/1.33  CNF conversion       : 0.02
% 2.35/1.33  Main loop            : 0.26
% 2.35/1.33  Inferencing          : 0.10
% 2.35/1.33  Reduction            : 0.07
% 2.35/1.33  Demodulation         : 0.05
% 2.35/1.33  BG Simplification    : 0.01
% 2.35/1.33  Subsumption          : 0.06
% 2.35/1.33  Abstraction          : 0.01
% 2.35/1.33  MUC search           : 0.00
% 2.35/1.33  Cooper               : 0.00
% 2.35/1.33  Total                : 0.52
% 2.35/1.33  Index Insertion      : 0.00
% 2.35/1.33  Index Deletion       : 0.00
% 2.35/1.33  Index Matching       : 0.00
% 2.35/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
