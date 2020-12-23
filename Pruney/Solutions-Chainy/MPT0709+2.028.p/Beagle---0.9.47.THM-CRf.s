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
% DateTime   : Thu Dec  3 10:05:28 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   35 (  39 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   68 (  88 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( r1_tarski(A,k1_relat_1(B))
            & v2_funct_1(B) )
         => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
          & r1_tarski(A,k1_relat_1(C))
          & v2_funct_1(C) )
       => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_16,plain,(
    k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_22,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_18,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_20,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k10_relat_1(B_4,A_3),k1_relat_1(B_4))
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [B_6,A_5] :
      ( r1_tarski(k9_relat_1(B_6,k10_relat_1(B_6,A_5)),A_5)
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_91,plain,(
    ! [A_26,B_27,C_28] :
      ( r1_tarski(A_26,B_27)
      | ~ v2_funct_1(C_28)
      | ~ r1_tarski(A_26,k1_relat_1(C_28))
      | ~ r1_tarski(k9_relat_1(C_28,A_26),k9_relat_1(C_28,B_27))
      | ~ v1_funct_1(C_28)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_153,plain,(
    ! [B_32,B_33] :
      ( r1_tarski(k10_relat_1(B_32,k9_relat_1(B_32,B_33)),B_33)
      | ~ v2_funct_1(B_32)
      | ~ r1_tarski(k10_relat_1(B_32,k9_relat_1(B_32,B_33)),k1_relat_1(B_32))
      | ~ v1_funct_1(B_32)
      | ~ v1_relat_1(B_32) ) ),
    inference(resolution,[status(thm)],[c_10,c_91])).

tff(c_164,plain,(
    ! [B_34,B_35] :
      ( r1_tarski(k10_relat_1(B_34,k9_relat_1(B_34,B_35)),B_35)
      | ~ v2_funct_1(B_34)
      | ~ v1_funct_1(B_34)
      | ~ v1_relat_1(B_34) ) ),
    inference(resolution,[status(thm)],[c_8,c_153])).

tff(c_46,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,k10_relat_1(B_20,k9_relat_1(B_20,A_19)))
      | ~ r1_tarski(A_19,k1_relat_1(B_20))
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_49,plain,(
    ! [B_20,A_19] :
      ( k10_relat_1(B_20,k9_relat_1(B_20,A_19)) = A_19
      | ~ r1_tarski(k10_relat_1(B_20,k9_relat_1(B_20,A_19)),A_19)
      | ~ r1_tarski(A_19,k1_relat_1(B_20))
      | ~ v1_relat_1(B_20) ) ),
    inference(resolution,[status(thm)],[c_46,c_2])).

tff(c_180,plain,(
    ! [B_36,B_37] :
      ( k10_relat_1(B_36,k9_relat_1(B_36,B_37)) = B_37
      | ~ r1_tarski(B_37,k1_relat_1(B_36))
      | ~ v2_funct_1(B_36)
      | ~ v1_funct_1(B_36)
      | ~ v1_relat_1(B_36) ) ),
    inference(resolution,[status(thm)],[c_164,c_49])).

tff(c_190,plain,
    ( k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_180])).

tff(c_199,plain,(
    k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_18,c_190])).

tff(c_201,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_199])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:33:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.25  
% 2.04/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.25  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_1
% 2.04/1.25  
% 2.04/1.25  %Foreground sorts:
% 2.04/1.25  
% 2.04/1.25  
% 2.04/1.25  %Background operators:
% 2.04/1.25  
% 2.04/1.25  
% 2.04/1.25  %Foreground operators:
% 2.04/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.04/1.25  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.04/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.04/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.25  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.04/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.04/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.25  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.04/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.04/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.04/1.25  
% 2.04/1.26  tff(f_70, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 2.04/1.26  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 2.04/1.26  tff(f_41, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 2.04/1.26  tff(f_59, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_funct_1)).
% 2.04/1.26  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 2.04/1.26  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.04/1.26  tff(c_16, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.04/1.26  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.04/1.26  tff(c_22, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.04/1.26  tff(c_18, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.04/1.26  tff(c_20, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.04/1.26  tff(c_8, plain, (![B_4, A_3]: (r1_tarski(k10_relat_1(B_4, A_3), k1_relat_1(B_4)) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.04/1.26  tff(c_10, plain, (![B_6, A_5]: (r1_tarski(k9_relat_1(B_6, k10_relat_1(B_6, A_5)), A_5) | ~v1_funct_1(B_6) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.04/1.26  tff(c_91, plain, (![A_26, B_27, C_28]: (r1_tarski(A_26, B_27) | ~v2_funct_1(C_28) | ~r1_tarski(A_26, k1_relat_1(C_28)) | ~r1_tarski(k9_relat_1(C_28, A_26), k9_relat_1(C_28, B_27)) | ~v1_funct_1(C_28) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.04/1.26  tff(c_153, plain, (![B_32, B_33]: (r1_tarski(k10_relat_1(B_32, k9_relat_1(B_32, B_33)), B_33) | ~v2_funct_1(B_32) | ~r1_tarski(k10_relat_1(B_32, k9_relat_1(B_32, B_33)), k1_relat_1(B_32)) | ~v1_funct_1(B_32) | ~v1_relat_1(B_32))), inference(resolution, [status(thm)], [c_10, c_91])).
% 2.04/1.26  tff(c_164, plain, (![B_34, B_35]: (r1_tarski(k10_relat_1(B_34, k9_relat_1(B_34, B_35)), B_35) | ~v2_funct_1(B_34) | ~v1_funct_1(B_34) | ~v1_relat_1(B_34))), inference(resolution, [status(thm)], [c_8, c_153])).
% 2.04/1.26  tff(c_46, plain, (![A_19, B_20]: (r1_tarski(A_19, k10_relat_1(B_20, k9_relat_1(B_20, A_19))) | ~r1_tarski(A_19, k1_relat_1(B_20)) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.04/1.26  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.04/1.26  tff(c_49, plain, (![B_20, A_19]: (k10_relat_1(B_20, k9_relat_1(B_20, A_19))=A_19 | ~r1_tarski(k10_relat_1(B_20, k9_relat_1(B_20, A_19)), A_19) | ~r1_tarski(A_19, k1_relat_1(B_20)) | ~v1_relat_1(B_20))), inference(resolution, [status(thm)], [c_46, c_2])).
% 2.04/1.26  tff(c_180, plain, (![B_36, B_37]: (k10_relat_1(B_36, k9_relat_1(B_36, B_37))=B_37 | ~r1_tarski(B_37, k1_relat_1(B_36)) | ~v2_funct_1(B_36) | ~v1_funct_1(B_36) | ~v1_relat_1(B_36))), inference(resolution, [status(thm)], [c_164, c_49])).
% 2.04/1.26  tff(c_190, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_20, c_180])).
% 2.04/1.26  tff(c_199, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_18, c_190])).
% 2.04/1.26  tff(c_201, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_199])).
% 2.04/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.26  
% 2.04/1.26  Inference rules
% 2.04/1.26  ----------------------
% 2.04/1.26  #Ref     : 0
% 2.04/1.26  #Sup     : 38
% 2.04/1.26  #Fact    : 0
% 2.04/1.26  #Define  : 0
% 2.04/1.26  #Split   : 1
% 2.04/1.26  #Chain   : 0
% 2.04/1.26  #Close   : 0
% 2.04/1.26  
% 2.04/1.26  Ordering : KBO
% 2.04/1.26  
% 2.04/1.26  Simplification rules
% 2.04/1.26  ----------------------
% 2.04/1.26  #Subsume      : 6
% 2.04/1.26  #Demod        : 23
% 2.04/1.26  #Tautology    : 15
% 2.04/1.26  #SimpNegUnit  : 1
% 2.04/1.26  #BackRed      : 0
% 2.04/1.26  
% 2.04/1.26  #Partial instantiations: 0
% 2.04/1.26  #Strategies tried      : 1
% 2.04/1.26  
% 2.04/1.26  Timing (in seconds)
% 2.04/1.26  ----------------------
% 2.04/1.26  Preprocessing        : 0.29
% 2.04/1.26  Parsing              : 0.17
% 2.04/1.26  CNF conversion       : 0.02
% 2.04/1.26  Main loop            : 0.19
% 2.04/1.26  Inferencing          : 0.08
% 2.04/1.26  Reduction            : 0.05
% 2.04/1.26  Demodulation         : 0.04
% 2.04/1.26  BG Simplification    : 0.01
% 2.04/1.26  Subsumption          : 0.04
% 2.04/1.26  Abstraction          : 0.01
% 2.04/1.26  MUC search           : 0.00
% 2.04/1.26  Cooper               : 0.00
% 2.04/1.26  Total                : 0.51
% 2.04/1.26  Index Insertion      : 0.00
% 2.04/1.26  Index Deletion       : 0.00
% 2.04/1.26  Index Matching       : 0.00
% 2.04/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
