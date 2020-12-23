%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:55 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :   36 (  42 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 (  71 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( ( r1_tarski(k1_relat_1(C),A)
            & r1_tarski(k2_relat_1(C),B) )
         => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_22,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_30,plain,(
    ~ r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_14])).

tff(c_18,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    ! [A_9] :
      ( r1_tarski(A_9,k2_zfmisc_1(k1_relat_1(A_9),k2_relat_1(A_9)))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_44,plain,(
    ! [A_20,C_21,B_22] :
      ( r1_tarski(k2_zfmisc_1(A_20,C_21),k2_zfmisc_1(B_22,C_21))
      | ~ r1_tarski(A_20,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_69,plain,(
    ! [A_32,B_33,C_34,A_35] :
      ( r1_tarski(A_32,k2_zfmisc_1(B_33,C_34))
      | ~ r1_tarski(A_32,k2_zfmisc_1(A_35,C_34))
      | ~ r1_tarski(A_35,B_33) ) ),
    inference(resolution,[status(thm)],[c_44,c_2])).

tff(c_92,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,k2_zfmisc_1(B_39,k2_relat_1(A_38)))
      | ~ r1_tarski(k1_relat_1(A_38),B_39)
      | ~ v1_relat_1(A_38) ) ),
    inference(resolution,[status(thm)],[c_12,c_69])).

tff(c_48,plain,(
    ! [C_23,A_24,B_25] :
      ( r1_tarski(k2_zfmisc_1(C_23,A_24),k2_zfmisc_1(C_23,B_25))
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_51,plain,(
    ! [A_1,C_23,B_25,A_24] :
      ( r1_tarski(A_1,k2_zfmisc_1(C_23,B_25))
      | ~ r1_tarski(A_1,k2_zfmisc_1(C_23,A_24))
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(resolution,[status(thm)],[c_48,c_2])).

tff(c_865,plain,(
    ! [A_126,B_127,B_128] :
      ( r1_tarski(A_126,k2_zfmisc_1(B_127,B_128))
      | ~ r1_tarski(k2_relat_1(A_126),B_128)
      | ~ r1_tarski(k1_relat_1(A_126),B_127)
      | ~ v1_relat_1(A_126) ) ),
    inference(resolution,[status(thm)],[c_92,c_51])).

tff(c_887,plain,(
    ! [B_127] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(B_127,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_127)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_16,c_865])).

tff(c_900,plain,(
    ! [B_129] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(B_129,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_887])).

tff(c_930,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_18,c_900])).

tff(c_941,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_930])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:21:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.31/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.51  
% 3.31/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.52  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.31/1.52  
% 3.31/1.52  %Foreground sorts:
% 3.31/1.52  
% 3.31/1.52  
% 3.31/1.52  %Background operators:
% 3.31/1.52  
% 3.31/1.52  
% 3.31/1.52  %Foreground operators:
% 3.31/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.31/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.31/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.31/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.31/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.31/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.31/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.31/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.31/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.31/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.31/1.52  
% 3.31/1.53  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.31/1.53  tff(f_54, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 3.31/1.53  tff(f_45, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 3.31/1.53  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 3.31/1.53  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.31/1.53  tff(c_22, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.31/1.53  tff(c_14, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.31/1.53  tff(c_30, plain, (~r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_14])).
% 3.31/1.53  tff(c_18, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.31/1.53  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.31/1.53  tff(c_16, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.31/1.53  tff(c_12, plain, (![A_9]: (r1_tarski(A_9, k2_zfmisc_1(k1_relat_1(A_9), k2_relat_1(A_9))) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.31/1.53  tff(c_44, plain, (![A_20, C_21, B_22]: (r1_tarski(k2_zfmisc_1(A_20, C_21), k2_zfmisc_1(B_22, C_21)) | ~r1_tarski(A_20, B_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.31/1.53  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.31/1.53  tff(c_69, plain, (![A_32, B_33, C_34, A_35]: (r1_tarski(A_32, k2_zfmisc_1(B_33, C_34)) | ~r1_tarski(A_32, k2_zfmisc_1(A_35, C_34)) | ~r1_tarski(A_35, B_33))), inference(resolution, [status(thm)], [c_44, c_2])).
% 3.31/1.53  tff(c_92, plain, (![A_38, B_39]: (r1_tarski(A_38, k2_zfmisc_1(B_39, k2_relat_1(A_38))) | ~r1_tarski(k1_relat_1(A_38), B_39) | ~v1_relat_1(A_38))), inference(resolution, [status(thm)], [c_12, c_69])).
% 3.31/1.53  tff(c_48, plain, (![C_23, A_24, B_25]: (r1_tarski(k2_zfmisc_1(C_23, A_24), k2_zfmisc_1(C_23, B_25)) | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.31/1.53  tff(c_51, plain, (![A_1, C_23, B_25, A_24]: (r1_tarski(A_1, k2_zfmisc_1(C_23, B_25)) | ~r1_tarski(A_1, k2_zfmisc_1(C_23, A_24)) | ~r1_tarski(A_24, B_25))), inference(resolution, [status(thm)], [c_48, c_2])).
% 3.31/1.53  tff(c_865, plain, (![A_126, B_127, B_128]: (r1_tarski(A_126, k2_zfmisc_1(B_127, B_128)) | ~r1_tarski(k2_relat_1(A_126), B_128) | ~r1_tarski(k1_relat_1(A_126), B_127) | ~v1_relat_1(A_126))), inference(resolution, [status(thm)], [c_92, c_51])).
% 3.31/1.53  tff(c_887, plain, (![B_127]: (r1_tarski('#skF_3', k2_zfmisc_1(B_127, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), B_127) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_16, c_865])).
% 3.31/1.53  tff(c_900, plain, (![B_129]: (r1_tarski('#skF_3', k2_zfmisc_1(B_129, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), B_129))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_887])).
% 3.31/1.53  tff(c_930, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_900])).
% 3.31/1.53  tff(c_941, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_930])).
% 3.31/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.53  
% 3.31/1.53  Inference rules
% 3.31/1.53  ----------------------
% 3.31/1.53  #Ref     : 0
% 3.31/1.53  #Sup     : 281
% 3.31/1.53  #Fact    : 0
% 3.31/1.53  #Define  : 0
% 3.31/1.53  #Split   : 1
% 3.31/1.53  #Chain   : 0
% 3.31/1.53  #Close   : 0
% 3.31/1.53  
% 3.31/1.53  Ordering : KBO
% 3.31/1.53  
% 3.31/1.53  Simplification rules
% 3.31/1.53  ----------------------
% 3.31/1.53  #Subsume      : 19
% 3.31/1.53  #Demod        : 2
% 3.31/1.53  #Tautology    : 1
% 3.31/1.53  #SimpNegUnit  : 1
% 3.31/1.53  #BackRed      : 0
% 3.31/1.53  
% 3.31/1.53  #Partial instantiations: 0
% 3.31/1.53  #Strategies tried      : 1
% 3.31/1.53  
% 3.31/1.53  Timing (in seconds)
% 3.31/1.53  ----------------------
% 3.31/1.53  Preprocessing        : 0.27
% 3.31/1.53  Parsing              : 0.15
% 3.31/1.53  CNF conversion       : 0.02
% 3.31/1.53  Main loop            : 0.50
% 3.31/1.53  Inferencing          : 0.16
% 3.31/1.53  Reduction            : 0.11
% 3.31/1.53  Demodulation         : 0.07
% 3.31/1.53  BG Simplification    : 0.02
% 3.31/1.53  Subsumption          : 0.17
% 3.31/1.53  Abstraction          : 0.02
% 3.56/1.53  MUC search           : 0.00
% 3.56/1.53  Cooper               : 0.00
% 3.56/1.53  Total                : 0.79
% 3.56/1.53  Index Insertion      : 0.00
% 3.56/1.53  Index Deletion       : 0.00
% 3.56/1.54  Index Matching       : 0.00
% 3.56/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
