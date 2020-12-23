%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:56 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   33 (  36 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   44 (  56 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
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
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_28,plain,(
    ~ r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_20,c_12])).

tff(c_16,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_14,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10,plain,(
    ! [A_10] :
      ( r1_tarski(A_10,k2_zfmisc_1(k1_relat_1(A_10),k2_relat_1(A_10)))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_46,plain,(
    ! [A_23,C_24,B_25,D_26] :
      ( r1_tarski(k2_zfmisc_1(A_23,C_24),k2_zfmisc_1(B_25,D_26))
      | ~ r1_tarski(C_24,D_26)
      | ~ r1_tarski(A_23,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_73,plain,(
    ! [A_35,D_33,A_34,C_32,B_31] :
      ( r1_tarski(A_34,k2_zfmisc_1(B_31,D_33))
      | ~ r1_tarski(A_34,k2_zfmisc_1(A_35,C_32))
      | ~ r1_tarski(C_32,D_33)
      | ~ r1_tarski(A_35,B_31) ) ),
    inference(resolution,[status(thm)],[c_46,c_2])).

tff(c_96,plain,(
    ! [A_37,B_38,D_39] :
      ( r1_tarski(A_37,k2_zfmisc_1(B_38,D_39))
      | ~ r1_tarski(k2_relat_1(A_37),D_39)
      | ~ r1_tarski(k1_relat_1(A_37),B_38)
      | ~ v1_relat_1(A_37) ) ),
    inference(resolution,[status(thm)],[c_10,c_73])).

tff(c_106,plain,(
    ! [B_38] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(B_38,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_38)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_14,c_96])).

tff(c_115,plain,(
    ! [B_40] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(B_40,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_106])).

tff(c_129,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_16,c_115])).

tff(c_136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_129])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:22:32 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.23  
% 1.99/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.24  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.99/1.24  
% 1.99/1.24  %Foreground sorts:
% 1.99/1.24  
% 1.99/1.24  
% 1.99/1.24  %Background operators:
% 1.99/1.24  
% 1.99/1.24  
% 1.99/1.24  %Foreground operators:
% 1.99/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.99/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.99/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.24  tff('#skF_3', type, '#skF_3': $i).
% 1.99/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.99/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.99/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.99/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.99/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.99/1.24  
% 1.99/1.25  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.99/1.25  tff(f_54, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 1.99/1.25  tff(f_45, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 1.99/1.25  tff(f_37, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_zfmisc_1)).
% 1.99/1.25  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.99/1.25  tff(c_20, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.99/1.25  tff(c_12, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.99/1.25  tff(c_28, plain, (~r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_12])).
% 1.99/1.25  tff(c_16, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.99/1.25  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.99/1.25  tff(c_14, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.99/1.25  tff(c_10, plain, (![A_10]: (r1_tarski(A_10, k2_zfmisc_1(k1_relat_1(A_10), k2_relat_1(A_10))) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.99/1.25  tff(c_46, plain, (![A_23, C_24, B_25, D_26]: (r1_tarski(k2_zfmisc_1(A_23, C_24), k2_zfmisc_1(B_25, D_26)) | ~r1_tarski(C_24, D_26) | ~r1_tarski(A_23, B_25))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.99/1.25  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.99/1.25  tff(c_73, plain, (![A_35, D_33, A_34, C_32, B_31]: (r1_tarski(A_34, k2_zfmisc_1(B_31, D_33)) | ~r1_tarski(A_34, k2_zfmisc_1(A_35, C_32)) | ~r1_tarski(C_32, D_33) | ~r1_tarski(A_35, B_31))), inference(resolution, [status(thm)], [c_46, c_2])).
% 1.99/1.25  tff(c_96, plain, (![A_37, B_38, D_39]: (r1_tarski(A_37, k2_zfmisc_1(B_38, D_39)) | ~r1_tarski(k2_relat_1(A_37), D_39) | ~r1_tarski(k1_relat_1(A_37), B_38) | ~v1_relat_1(A_37))), inference(resolution, [status(thm)], [c_10, c_73])).
% 1.99/1.25  tff(c_106, plain, (![B_38]: (r1_tarski('#skF_3', k2_zfmisc_1(B_38, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), B_38) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_14, c_96])).
% 1.99/1.25  tff(c_115, plain, (![B_40]: (r1_tarski('#skF_3', k2_zfmisc_1(B_40, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), B_40))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_106])).
% 1.99/1.25  tff(c_129, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_16, c_115])).
% 1.99/1.25  tff(c_136, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_129])).
% 1.99/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.25  
% 1.99/1.25  Inference rules
% 1.99/1.25  ----------------------
% 1.99/1.25  #Ref     : 0
% 1.99/1.25  #Sup     : 29
% 1.99/1.25  #Fact    : 0
% 1.99/1.25  #Define  : 0
% 1.99/1.25  #Split   : 0
% 1.99/1.25  #Chain   : 0
% 1.99/1.25  #Close   : 0
% 1.99/1.25  
% 1.99/1.25  Ordering : KBO
% 1.99/1.25  
% 1.99/1.25  Simplification rules
% 1.99/1.25  ----------------------
% 1.99/1.25  #Subsume      : 0
% 1.99/1.25  #Demod        : 2
% 1.99/1.25  #Tautology    : 1
% 1.99/1.25  #SimpNegUnit  : 1
% 1.99/1.25  #BackRed      : 0
% 1.99/1.25  
% 1.99/1.25  #Partial instantiations: 0
% 1.99/1.25  #Strategies tried      : 1
% 1.99/1.25  
% 1.99/1.25  Timing (in seconds)
% 1.99/1.25  ----------------------
% 1.99/1.25  Preprocessing        : 0.29
% 1.99/1.25  Parsing              : 0.17
% 1.99/1.25  CNF conversion       : 0.02
% 1.99/1.25  Main loop            : 0.17
% 1.99/1.25  Inferencing          : 0.06
% 1.99/1.25  Reduction            : 0.04
% 1.99/1.25  Demodulation         : 0.03
% 1.99/1.25  BG Simplification    : 0.01
% 1.99/1.25  Subsumption          : 0.04
% 1.99/1.25  Abstraction          : 0.01
% 1.99/1.25  MUC search           : 0.00
% 1.99/1.25  Cooper               : 0.00
% 1.99/1.25  Total                : 0.49
% 1.99/1.25  Index Insertion      : 0.00
% 1.99/1.25  Index Deletion       : 0.00
% 1.99/1.25  Index Matching       : 0.00
% 1.99/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
