%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:47 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   41 (  52 expanded)
%              Number of leaves         :   23 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  75 expanded)
%              Number of equality atoms :   14 (  25 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_24,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_18,plain,(
    k10_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_69,plain,(
    ! [B_30,A_31] :
      ( r1_xboole_0(k2_relat_1(B_30),A_31)
      | k10_relat_1(B_30,A_31) != k1_xboole_0
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_82,plain,(
    ! [A_34,B_35] :
      ( r1_xboole_0(A_34,k2_relat_1(B_35))
      | k10_relat_1(B_35,A_34) != k1_xboole_0
      | ~ v1_relat_1(B_35) ) ),
    inference(resolution,[status(thm)],[c_69,c_2])).

tff(c_20,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_40,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = A_21
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_44,plain,(
    k3_xboole_0('#skF_3',k2_relat_1('#skF_4')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_20,c_40])).

tff(c_49,plain,(
    ! [A_23,B_24,C_25] :
      ( ~ r1_xboole_0(A_23,B_24)
      | ~ r2_hidden(C_25,k3_xboole_0(A_23,B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_52,plain,(
    ! [C_25] :
      ( ~ r1_xboole_0('#skF_3',k2_relat_1('#skF_4'))
      | ~ r2_hidden(C_25,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_49])).

tff(c_59,plain,(
    ~ r1_xboole_0('#skF_3',k2_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_89,plain,
    ( k10_relat_1('#skF_4','#skF_3') != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_59])).

tff(c_99,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_18,c_89])).

tff(c_102,plain,(
    ! [C_36] : ~ r2_hidden(C_36,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_106,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_8,c_102])).

tff(c_110,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_106])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:31:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.30  
% 1.90/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.31  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.07/1.31  
% 2.07/1.31  %Foreground sorts:
% 2.07/1.31  
% 2.07/1.31  
% 2.07/1.31  %Background operators:
% 2.07/1.31  
% 2.07/1.31  
% 2.07/1.31  %Foreground operators:
% 2.07/1.31  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.07/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.07/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.07/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.07/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.07/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.07/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.07/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.31  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.07/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.07/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.07/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.07/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.07/1.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.07/1.31  
% 2.07/1.32  tff(f_74, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_relat_1)).
% 2.07/1.32  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.07/1.32  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 2.07/1.32  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.07/1.32  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.07/1.32  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.07/1.32  tff(c_22, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.07/1.32  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.07/1.32  tff(c_24, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.07/1.32  tff(c_18, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.07/1.32  tff(c_69, plain, (![B_30, A_31]: (r1_xboole_0(k2_relat_1(B_30), A_31) | k10_relat_1(B_30, A_31)!=k1_xboole_0 | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.07/1.32  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.07/1.32  tff(c_82, plain, (![A_34, B_35]: (r1_xboole_0(A_34, k2_relat_1(B_35)) | k10_relat_1(B_35, A_34)!=k1_xboole_0 | ~v1_relat_1(B_35))), inference(resolution, [status(thm)], [c_69, c_2])).
% 2.07/1.32  tff(c_20, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.07/1.32  tff(c_40, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=A_21 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.07/1.32  tff(c_44, plain, (k3_xboole_0('#skF_3', k2_relat_1('#skF_4'))='#skF_3'), inference(resolution, [status(thm)], [c_20, c_40])).
% 2.07/1.32  tff(c_49, plain, (![A_23, B_24, C_25]: (~r1_xboole_0(A_23, B_24) | ~r2_hidden(C_25, k3_xboole_0(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.07/1.32  tff(c_52, plain, (![C_25]: (~r1_xboole_0('#skF_3', k2_relat_1('#skF_4')) | ~r2_hidden(C_25, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_49])).
% 2.07/1.32  tff(c_59, plain, (~r1_xboole_0('#skF_3', k2_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_52])).
% 2.07/1.32  tff(c_89, plain, (k10_relat_1('#skF_4', '#skF_3')!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_82, c_59])).
% 2.07/1.32  tff(c_99, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_18, c_89])).
% 2.07/1.32  tff(c_102, plain, (![C_36]: (~r2_hidden(C_36, '#skF_3'))), inference(splitRight, [status(thm)], [c_52])).
% 2.07/1.32  tff(c_106, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_8, c_102])).
% 2.07/1.32  tff(c_110, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_106])).
% 2.07/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.32  
% 2.07/1.32  Inference rules
% 2.07/1.32  ----------------------
% 2.07/1.32  #Ref     : 0
% 2.07/1.32  #Sup     : 19
% 2.07/1.32  #Fact    : 0
% 2.07/1.32  #Define  : 0
% 2.07/1.32  #Split   : 1
% 2.07/1.32  #Chain   : 0
% 2.07/1.32  #Close   : 0
% 2.07/1.32  
% 2.07/1.32  Ordering : KBO
% 2.07/1.32  
% 2.07/1.32  Simplification rules
% 2.07/1.32  ----------------------
% 2.07/1.32  #Subsume      : 0
% 2.07/1.32  #Demod        : 2
% 2.07/1.32  #Tautology    : 8
% 2.07/1.32  #SimpNegUnit  : 2
% 2.07/1.32  #BackRed      : 0
% 2.07/1.32  
% 2.07/1.32  #Partial instantiations: 0
% 2.07/1.32  #Strategies tried      : 1
% 2.07/1.32  
% 2.07/1.32  Timing (in seconds)
% 2.07/1.32  ----------------------
% 2.07/1.32  Preprocessing        : 0.36
% 2.07/1.32  Parsing              : 0.19
% 2.07/1.32  CNF conversion       : 0.02
% 2.07/1.32  Main loop            : 0.14
% 2.07/1.32  Inferencing          : 0.06
% 2.07/1.32  Reduction            : 0.04
% 2.07/1.32  Demodulation         : 0.02
% 2.07/1.32  BG Simplification    : 0.01
% 2.07/1.32  Subsumption          : 0.02
% 2.07/1.32  Abstraction          : 0.01
% 2.07/1.32  MUC search           : 0.00
% 2.07/1.32  Cooper               : 0.00
% 2.07/1.32  Total                : 0.52
% 2.07/1.32  Index Insertion      : 0.00
% 2.07/1.32  Index Deletion       : 0.00
% 2.07/1.32  Index Matching       : 0.00
% 2.07/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
