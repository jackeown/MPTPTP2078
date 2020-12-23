%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:27 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   48 (  61 expanded)
%              Number of leaves         :   28 (  33 expanded)
%              Depth                    :    6
%              Number of atoms          :   51 (  76 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > v5_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v5_ordinal1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_ordinal1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v4_relat_1(k1_xboole_0,A)
      & v5_relat_1(k1_xboole_0,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l222_relat_1)).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(k1_xboole_0)
        & v5_relat_1(k1_xboole_0,A)
        & v1_funct_1(k1_xboole_0)
        & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_44,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_42,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_24,plain,(
    ! [A_29] :
      ( v5_ordinal1(A_29)
      | ~ v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_32,plain,(
    ! [A_33] :
      ( v1_funct_1(A_33)
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_36,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_32])).

tff(c_20,plain,(
    ! [B_27] : v5_relat_1(k1_xboole_0,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_26,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,'#skF_5')
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_28,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_26])).

tff(c_47,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_28])).

tff(c_48,plain,(
    ~ v5_ordinal1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_47])).

tff(c_51,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_48])).

tff(c_55,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_51])).

tff(c_56,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_47])).

tff(c_16,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_59,plain,(
    ! [A_40,B_41,C_42] :
      ( ~ r1_xboole_0(A_40,B_41)
      | ~ r2_hidden(C_42,k3_xboole_0(A_40,B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_66,plain,(
    ! [A_6,C_42] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_42,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_59])).

tff(c_79,plain,(
    ! [C_45] : ~ r2_hidden(C_45,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_66])).

tff(c_83,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_79])).

tff(c_87,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_83])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:39:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.18  
% 1.79/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.18  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > v5_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4
% 1.79/1.18  
% 1.79/1.18  %Foreground sorts:
% 1.79/1.18  
% 1.79/1.18  
% 1.79/1.18  %Background operators:
% 1.79/1.18  
% 1.79/1.18  
% 1.79/1.18  %Foreground operators:
% 1.79/1.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.79/1.18  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.79/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.79/1.18  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.79/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.79/1.18  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.79/1.18  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 1.79/1.18  tff('#skF_5', type, '#skF_5': $i).
% 1.79/1.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.79/1.18  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.79/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.79/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.18  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.79/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.79/1.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.79/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.79/1.19  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.79/1.19  
% 1.79/1.19  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.79/1.19  tff(f_66, axiom, (![A]: (v1_xboole_0(A) => v5_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_ordinal1)).
% 1.79/1.19  tff(f_62, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 1.79/1.19  tff(f_58, axiom, (![A, B]: (v4_relat_1(k1_xboole_0, A) & v5_relat_1(k1_xboole_0, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l222_relat_1)).
% 1.79/1.19  tff(f_75, negated_conjecture, ~(![A]: (((v1_relat_1(k1_xboole_0) & v5_relat_1(k1_xboole_0, A)) & v1_funct_1(k1_xboole_0)) & v5_ordinal1(k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_ordinal1)).
% 1.79/1.19  tff(f_54, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 1.79/1.19  tff(f_44, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.79/1.19  tff(f_42, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.79/1.19  tff(f_40, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.79/1.19  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.79/1.19  tff(c_24, plain, (![A_29]: (v5_ordinal1(A_29) | ~v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.79/1.19  tff(c_32, plain, (![A_33]: (v1_funct_1(A_33) | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.79/1.19  tff(c_36, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_32])).
% 1.79/1.19  tff(c_20, plain, (![B_27]: (v5_relat_1(k1_xboole_0, B_27))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.79/1.19  tff(c_26, plain, (~v1_relat_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0, '#skF_5') | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.79/1.19  tff(c_28, plain, (~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_26])).
% 1.79/1.19  tff(c_47, plain, (~v1_relat_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_28])).
% 1.79/1.19  tff(c_48, plain, (~v5_ordinal1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_47])).
% 1.79/1.19  tff(c_51, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_48])).
% 1.79/1.19  tff(c_55, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_51])).
% 1.79/1.19  tff(c_56, plain, (~v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_47])).
% 1.79/1.19  tff(c_16, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.79/1.19  tff(c_10, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.79/1.19  tff(c_8, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.79/1.19  tff(c_59, plain, (![A_40, B_41, C_42]: (~r1_xboole_0(A_40, B_41) | ~r2_hidden(C_42, k3_xboole_0(A_40, B_41)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.79/1.19  tff(c_66, plain, (![A_6, C_42]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_42, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_59])).
% 1.79/1.19  tff(c_79, plain, (![C_45]: (~r2_hidden(C_45, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_66])).
% 1.79/1.19  tff(c_83, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_79])).
% 1.79/1.19  tff(c_87, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_83])).
% 1.79/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.19  
% 1.79/1.19  Inference rules
% 1.79/1.19  ----------------------
% 1.79/1.19  #Ref     : 0
% 1.79/1.19  #Sup     : 9
% 1.79/1.19  #Fact    : 0
% 1.79/1.19  #Define  : 0
% 1.79/1.19  #Split   : 1
% 1.79/1.19  #Chain   : 0
% 1.79/1.19  #Close   : 0
% 1.79/1.19  
% 1.79/1.19  Ordering : KBO
% 1.79/1.19  
% 1.79/1.19  Simplification rules
% 1.79/1.19  ----------------------
% 1.79/1.19  #Subsume      : 0
% 1.79/1.19  #Demod        : 5
% 1.79/1.19  #Tautology    : 4
% 1.79/1.19  #SimpNegUnit  : 1
% 1.79/1.19  #BackRed      : 0
% 1.79/1.19  
% 1.79/1.19  #Partial instantiations: 0
% 1.79/1.19  #Strategies tried      : 1
% 1.79/1.19  
% 1.79/1.20  Timing (in seconds)
% 1.79/1.20  ----------------------
% 1.87/1.20  Preprocessing        : 0.28
% 1.87/1.20  Parsing              : 0.16
% 1.87/1.20  CNF conversion       : 0.02
% 1.87/1.20  Main loop            : 0.11
% 1.87/1.20  Inferencing          : 0.05
% 1.87/1.20  Reduction            : 0.03
% 1.87/1.20  Demodulation         : 0.02
% 1.87/1.20  BG Simplification    : 0.01
% 1.87/1.20  Subsumption          : 0.01
% 1.87/1.20  Abstraction          : 0.00
% 1.87/1.20  MUC search           : 0.00
% 1.87/1.20  Cooper               : 0.00
% 1.87/1.20  Total                : 0.42
% 1.87/1.20  Index Insertion      : 0.00
% 1.87/1.20  Index Deletion       : 0.00
% 1.87/1.20  Index Matching       : 0.00
% 1.87/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
