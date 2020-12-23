%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:39 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   39 (  44 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :   57 (  73 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_67,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_xboole_0(k1_relat_1(A),k1_relat_1(B))
             => r1_xboole_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t214_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,k4_xboole_0(B,C))
     => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(A,C)
        & r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_xboole_1)).

tff(c_16,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_14,plain,(
    ! [A_17] :
      ( r1_tarski(A_17,k2_zfmisc_1(k1_relat_1(A_17),k2_relat_1(A_17)))
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    r1_xboole_0(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_36,plain,(
    ! [A_27,B_28,C_29,D_30] :
      ( ~ r1_xboole_0(A_27,B_28)
      | r1_xboole_0(k2_zfmisc_1(A_27,C_29),k2_zfmisc_1(B_28,D_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_xboole_0(A_1,C_3)
      | ~ r1_xboole_0(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_135,plain,(
    ! [B_78,A_77,C_75,A_79,D_76] :
      ( r1_xboole_0(A_77,k2_zfmisc_1(B_78,D_76))
      | ~ r1_tarski(A_77,k2_zfmisc_1(A_79,C_75))
      | ~ r1_xboole_0(A_79,B_78) ) ),
    inference(resolution,[status(thm)],[c_36,c_2])).

tff(c_139,plain,(
    ! [A_80,B_81,D_82] :
      ( r1_xboole_0(A_80,k2_zfmisc_1(B_81,D_82))
      | ~ r1_xboole_0(k1_relat_1(A_80),B_81)
      | ~ v1_relat_1(A_80) ) ),
    inference(resolution,[status(thm)],[c_14,c_135])).

tff(c_152,plain,(
    ! [D_82] :
      ( r1_xboole_0('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_2'),D_82))
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_18,c_139])).

tff(c_162,plain,(
    ! [D_83] : r1_xboole_0('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_2'),D_83)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_152])).

tff(c_8,plain,(
    ! [A_10,C_12,B_11] :
      ( r1_xboole_0(A_10,k4_xboole_0(C_12,B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_48,plain,(
    ! [B_37,A_38,C_39] :
      ( r1_xboole_0(B_37,k4_xboole_0(A_38,C_39))
      | ~ r1_xboole_0(A_38,k4_xboole_0(B_37,C_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_51,plain,(
    ! [C_12,A_10,B_11] :
      ( r1_xboole_0(C_12,k4_xboole_0(A_10,B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(resolution,[status(thm)],[c_8,c_48])).

tff(c_59,plain,(
    ! [A_43,B_44,C_45] :
      ( ~ r1_xboole_0(A_43,k4_xboole_0(B_44,C_45))
      | ~ r1_xboole_0(A_43,C_45)
      | r1_xboole_0(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_66,plain,(
    ! [C_12,B_11,A_10] :
      ( ~ r1_xboole_0(C_12,B_11)
      | r1_xboole_0(C_12,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(resolution,[status(thm)],[c_51,c_59])).

tff(c_183,plain,(
    ! [A_88,D_89] :
      ( r1_xboole_0('#skF_1',A_88)
      | ~ r1_tarski(A_88,k2_zfmisc_1(k1_relat_1('#skF_2'),D_89)) ) ),
    inference(resolution,[status(thm)],[c_162,c_66])).

tff(c_187,plain,
    ( r1_xboole_0('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_183])).

tff(c_190,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_187])).

tff(c_192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_190])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:00:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.23  
% 2.08/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.23  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.08/1.23  
% 2.08/1.23  %Foreground sorts:
% 2.08/1.23  
% 2.08/1.23  
% 2.08/1.23  %Background operators:
% 2.08/1.23  
% 2.08/1.23  
% 2.08/1.23  %Foreground operators:
% 2.08/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.08/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.08/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.08/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.08/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.08/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.08/1.23  
% 2.12/1.24  tff(f_67, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k1_relat_1(A), k1_relat_1(B)) => r1_xboole_0(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t214_relat_1)).
% 2.12/1.24  tff(f_57, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 2.12/1.24  tff(f_53, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 2.12/1.24  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.12/1.24  tff(f_47, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 2.12/1.24  tff(f_35, axiom, (![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_xboole_1)).
% 2.12/1.24  tff(f_43, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_xboole_1)).
% 2.12/1.24  tff(c_16, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.12/1.24  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.12/1.24  tff(c_14, plain, (![A_17]: (r1_tarski(A_17, k2_zfmisc_1(k1_relat_1(A_17), k2_relat_1(A_17))) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.12/1.24  tff(c_22, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.12/1.24  tff(c_18, plain, (r1_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.12/1.24  tff(c_36, plain, (![A_27, B_28, C_29, D_30]: (~r1_xboole_0(A_27, B_28) | r1_xboole_0(k2_zfmisc_1(A_27, C_29), k2_zfmisc_1(B_28, D_30)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.12/1.24  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_xboole_0(A_1, C_3) | ~r1_xboole_0(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.12/1.24  tff(c_135, plain, (![B_78, A_77, C_75, A_79, D_76]: (r1_xboole_0(A_77, k2_zfmisc_1(B_78, D_76)) | ~r1_tarski(A_77, k2_zfmisc_1(A_79, C_75)) | ~r1_xboole_0(A_79, B_78))), inference(resolution, [status(thm)], [c_36, c_2])).
% 2.12/1.24  tff(c_139, plain, (![A_80, B_81, D_82]: (r1_xboole_0(A_80, k2_zfmisc_1(B_81, D_82)) | ~r1_xboole_0(k1_relat_1(A_80), B_81) | ~v1_relat_1(A_80))), inference(resolution, [status(thm)], [c_14, c_135])).
% 2.12/1.24  tff(c_152, plain, (![D_82]: (r1_xboole_0('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_2'), D_82)) | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_139])).
% 2.12/1.24  tff(c_162, plain, (![D_83]: (r1_xboole_0('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_2'), D_83)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_152])).
% 2.12/1.24  tff(c_8, plain, (![A_10, C_12, B_11]: (r1_xboole_0(A_10, k4_xboole_0(C_12, B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.12/1.24  tff(c_48, plain, (![B_37, A_38, C_39]: (r1_xboole_0(B_37, k4_xboole_0(A_38, C_39)) | ~r1_xboole_0(A_38, k4_xboole_0(B_37, C_39)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.12/1.24  tff(c_51, plain, (![C_12, A_10, B_11]: (r1_xboole_0(C_12, k4_xboole_0(A_10, B_11)) | ~r1_tarski(A_10, B_11))), inference(resolution, [status(thm)], [c_8, c_48])).
% 2.12/1.24  tff(c_59, plain, (![A_43, B_44, C_45]: (~r1_xboole_0(A_43, k4_xboole_0(B_44, C_45)) | ~r1_xboole_0(A_43, C_45) | r1_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.12/1.24  tff(c_66, plain, (![C_12, B_11, A_10]: (~r1_xboole_0(C_12, B_11) | r1_xboole_0(C_12, A_10) | ~r1_tarski(A_10, B_11))), inference(resolution, [status(thm)], [c_51, c_59])).
% 2.12/1.24  tff(c_183, plain, (![A_88, D_89]: (r1_xboole_0('#skF_1', A_88) | ~r1_tarski(A_88, k2_zfmisc_1(k1_relat_1('#skF_2'), D_89)))), inference(resolution, [status(thm)], [c_162, c_66])).
% 2.12/1.24  tff(c_187, plain, (r1_xboole_0('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_14, c_183])).
% 2.12/1.24  tff(c_190, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_187])).
% 2.12/1.24  tff(c_192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_190])).
% 2.12/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.24  
% 2.12/1.24  Inference rules
% 2.12/1.24  ----------------------
% 2.12/1.24  #Ref     : 0
% 2.12/1.24  #Sup     : 42
% 2.12/1.24  #Fact    : 0
% 2.12/1.24  #Define  : 0
% 2.12/1.24  #Split   : 1
% 2.12/1.24  #Chain   : 0
% 2.12/1.24  #Close   : 0
% 2.12/1.24  
% 2.12/1.24  Ordering : KBO
% 2.12/1.24  
% 2.12/1.24  Simplification rules
% 2.12/1.24  ----------------------
% 2.12/1.24  #Subsume      : 2
% 2.12/1.24  #Demod        : 3
% 2.12/1.24  #Tautology    : 0
% 2.12/1.24  #SimpNegUnit  : 1
% 2.12/1.24  #BackRed      : 0
% 2.12/1.24  
% 2.12/1.24  #Partial instantiations: 0
% 2.12/1.24  #Strategies tried      : 1
% 2.12/1.24  
% 2.12/1.24  Timing (in seconds)
% 2.12/1.24  ----------------------
% 2.12/1.24  Preprocessing        : 0.26
% 2.12/1.24  Parsing              : 0.15
% 2.12/1.24  CNF conversion       : 0.02
% 2.12/1.24  Main loop            : 0.22
% 2.12/1.24  Inferencing          : 0.08
% 2.12/1.24  Reduction            : 0.05
% 2.12/1.24  Demodulation         : 0.03
% 2.12/1.24  BG Simplification    : 0.01
% 2.12/1.24  Subsumption          : 0.06
% 2.12/1.24  Abstraction          : 0.01
% 2.12/1.24  MUC search           : 0.00
% 2.12/1.24  Cooper               : 0.00
% 2.12/1.24  Total                : 0.51
% 2.12/1.24  Index Insertion      : 0.00
% 2.12/1.24  Index Deletion       : 0.00
% 2.12/1.24  Index Matching       : 0.00
% 2.12/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
