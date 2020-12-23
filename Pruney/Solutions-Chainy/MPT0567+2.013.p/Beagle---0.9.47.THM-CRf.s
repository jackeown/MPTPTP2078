%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:16 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   37 (  43 expanded)
%              Number of leaves         :   22 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   38 (  50 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

tff(f_49,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_28,plain,(
    k10_relat_1('#skF_7',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_30,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_80,plain,(
    ! [A_69,B_70,D_71] :
      ( r2_hidden('#skF_6'(A_69,B_70,k10_relat_1(A_69,B_70),D_71),B_70)
      | ~ r2_hidden(D_71,k10_relat_1(A_69,B_70))
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_33,plain,(
    ! [A_53,B_54,C_55] :
      ( ~ r1_xboole_0(A_53,B_54)
      | ~ r2_hidden(C_55,k3_xboole_0(A_53,B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_44,plain,(
    ! [A_58,B_59] :
      ( ~ r1_xboole_0(A_58,B_59)
      | k3_xboole_0(A_58,B_59) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_33])).

tff(c_49,plain,(
    ! [A_60] : k3_xboole_0(A_60,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_44])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_57,plain,(
    ! [A_60,C_5] :
      ( ~ r1_xboole_0(A_60,k1_xboole_0)
      | ~ r2_hidden(C_5,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_4])).

tff(c_63,plain,(
    ! [C_5] : ~ r2_hidden(C_5,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_57])).

tff(c_94,plain,(
    ! [D_72,A_73] :
      ( ~ r2_hidden(D_72,k10_relat_1(A_73,k1_xboole_0))
      | ~ v1_relat_1(A_73) ) ),
    inference(resolution,[status(thm)],[c_80,c_63])).

tff(c_105,plain,(
    ! [A_74] :
      ( ~ v1_relat_1(A_74)
      | k10_relat_1(A_74,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_94])).

tff(c_108,plain,(
    k10_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_105])).

tff(c_112,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:31:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.27  
% 1.85/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.27  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_1
% 1.85/1.27  
% 1.85/1.27  %Foreground sorts:
% 1.85/1.27  
% 1.85/1.27  
% 1.85/1.27  %Background operators:
% 1.85/1.27  
% 1.85/1.27  
% 1.85/1.27  %Foreground operators:
% 1.85/1.27  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.85/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.85/1.27  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.85/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.85/1.27  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.85/1.27  tff('#skF_7', type, '#skF_7': $i).
% 1.85/1.27  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 1.85/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.85/1.27  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 1.85/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.27  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.85/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.85/1.27  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.85/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.85/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.85/1.27  
% 1.85/1.28  tff(f_67, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_relat_1)).
% 1.85/1.28  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.85/1.28  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 1.85/1.28  tff(f_49, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.85/1.28  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.85/1.28  tff(c_28, plain, (k10_relat_1('#skF_7', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.85/1.28  tff(c_30, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.85/1.28  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.85/1.28  tff(c_80, plain, (![A_69, B_70, D_71]: (r2_hidden('#skF_6'(A_69, B_70, k10_relat_1(A_69, B_70), D_71), B_70) | ~r2_hidden(D_71, k10_relat_1(A_69, B_70)) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.85/1.28  tff(c_8, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.85/1.28  tff(c_33, plain, (![A_53, B_54, C_55]: (~r1_xboole_0(A_53, B_54) | ~r2_hidden(C_55, k3_xboole_0(A_53, B_54)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.85/1.28  tff(c_44, plain, (![A_58, B_59]: (~r1_xboole_0(A_58, B_59) | k3_xboole_0(A_58, B_59)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_33])).
% 1.85/1.28  tff(c_49, plain, (![A_60]: (k3_xboole_0(A_60, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_44])).
% 1.85/1.28  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.85/1.28  tff(c_57, plain, (![A_60, C_5]: (~r1_xboole_0(A_60, k1_xboole_0) | ~r2_hidden(C_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_49, c_4])).
% 1.85/1.28  tff(c_63, plain, (![C_5]: (~r2_hidden(C_5, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_57])).
% 1.85/1.28  tff(c_94, plain, (![D_72, A_73]: (~r2_hidden(D_72, k10_relat_1(A_73, k1_xboole_0)) | ~v1_relat_1(A_73))), inference(resolution, [status(thm)], [c_80, c_63])).
% 1.85/1.28  tff(c_105, plain, (![A_74]: (~v1_relat_1(A_74) | k10_relat_1(A_74, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_94])).
% 1.85/1.28  tff(c_108, plain, (k10_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_105])).
% 1.85/1.28  tff(c_112, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_108])).
% 1.85/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.28  
% 1.85/1.28  Inference rules
% 1.85/1.28  ----------------------
% 1.85/1.28  #Ref     : 0
% 1.85/1.28  #Sup     : 16
% 1.85/1.28  #Fact    : 0
% 1.85/1.28  #Define  : 0
% 1.85/1.28  #Split   : 0
% 1.85/1.28  #Chain   : 0
% 1.85/1.28  #Close   : 0
% 1.85/1.28  
% 1.85/1.28  Ordering : KBO
% 1.85/1.28  
% 1.85/1.28  Simplification rules
% 1.85/1.28  ----------------------
% 1.85/1.28  #Subsume      : 0
% 1.85/1.28  #Demod        : 2
% 1.85/1.28  #Tautology    : 5
% 1.85/1.28  #SimpNegUnit  : 1
% 1.85/1.28  #BackRed      : 0
% 1.85/1.28  
% 1.85/1.28  #Partial instantiations: 0
% 1.85/1.28  #Strategies tried      : 1
% 1.85/1.28  
% 1.85/1.28  Timing (in seconds)
% 1.85/1.28  ----------------------
% 1.85/1.29  Preprocessing        : 0.37
% 1.85/1.29  Parsing              : 0.22
% 1.85/1.29  CNF conversion       : 0.03
% 1.85/1.29  Main loop            : 0.14
% 1.85/1.29  Inferencing          : 0.06
% 1.85/1.29  Reduction            : 0.03
% 1.85/1.29  Demodulation         : 0.03
% 1.85/1.29  BG Simplification    : 0.01
% 1.85/1.29  Subsumption          : 0.02
% 1.85/1.29  Abstraction          : 0.01
% 1.85/1.29  MUC search           : 0.00
% 1.85/1.29  Cooper               : 0.00
% 1.85/1.29  Total                : 0.54
% 1.85/1.29  Index Insertion      : 0.00
% 1.85/1.29  Index Deletion       : 0.00
% 1.85/1.29  Index Matching       : 0.00
% 1.85/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
