%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:27 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   46 (  59 expanded)
%              Number of leaves         :   28 (  33 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  70 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > v5_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v5_ordinal1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_ordinal1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v4_relat_1(k1_xboole_0,A)
      & v5_relat_1(k1_xboole_0,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l222_relat_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(k1_xboole_0)
        & v5_relat_1(k1_xboole_0,A)
        & v1_funct_1(k1_xboole_0)
        & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_28,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_26,plain,(
    ! [A_28] :
      ( v5_ordinal1(A_28)
      | ~ v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_33,plain,(
    ! [A_31] :
      ( v1_funct_1(A_31)
      | ~ v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_37,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_33])).

tff(c_22,plain,(
    ! [B_26] : v5_relat_1(k1_xboole_0,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,'#skF_4')
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_30,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_28])).

tff(c_57,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_30])).

tff(c_58,plain,(
    ~ v5_ordinal1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_57])).

tff(c_61,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26,c_58])).

tff(c_65,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_61])).

tff(c_66,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_57])).

tff(c_18,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_1'(A_7),A_7)
      | v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_1] : k4_xboole_0(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_97,plain,(
    ! [B_43,A_44] :
      ( ~ r2_hidden(B_43,A_44)
      | k4_xboole_0(A_44,k1_tarski(B_43)) != A_44 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_107,plain,(
    ! [B_45] : ~ r2_hidden(B_45,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_97])).

tff(c_111,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_107])).

tff(c_115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_111])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:34:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.16  
% 1.68/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.17  %$ v5_relat_1 > v4_relat_1 > r2_hidden > v5_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.68/1.17  
% 1.68/1.17  %Foreground sorts:
% 1.68/1.17  
% 1.68/1.17  
% 1.68/1.17  %Background operators:
% 1.68/1.17  
% 1.68/1.17  
% 1.68/1.17  %Foreground operators:
% 1.68/1.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.68/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.68/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.68/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.68/1.17  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.68/1.17  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.68/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.68/1.17  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.68/1.17  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 1.68/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.68/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.68/1.17  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.68/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.68/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.68/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.68/1.17  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.68/1.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.68/1.17  
% 1.88/1.18  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.88/1.18  tff(f_59, axiom, (![A]: (v1_xboole_0(A) => v5_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_ordinal1)).
% 1.88/1.18  tff(f_55, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 1.88/1.18  tff(f_51, axiom, (![A, B]: (v4_relat_1(k1_xboole_0, A) & v5_relat_1(k1_xboole_0, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l222_relat_1)).
% 1.88/1.18  tff(f_68, negated_conjecture, ~(![A]: (((v1_relat_1(k1_xboole_0) & v5_relat_1(k1_xboole_0, A)) & v1_funct_1(k1_xboole_0)) & v5_ordinal1(k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_ordinal1)).
% 1.88/1.18  tff(f_47, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 1.88/1.18  tff(f_28, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 1.88/1.18  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.88/1.18  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.88/1.18  tff(c_26, plain, (![A_28]: (v5_ordinal1(A_28) | ~v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.88/1.18  tff(c_33, plain, (![A_31]: (v1_funct_1(A_31) | ~v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.88/1.18  tff(c_37, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_33])).
% 1.88/1.18  tff(c_22, plain, (![B_26]: (v5_relat_1(k1_xboole_0, B_26))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.88/1.18  tff(c_28, plain, (~v1_relat_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0, '#skF_4') | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.88/1.18  tff(c_30, plain, (~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_28])).
% 1.88/1.18  tff(c_57, plain, (~v1_relat_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_37, c_30])).
% 1.88/1.18  tff(c_58, plain, (~v5_ordinal1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_57])).
% 1.88/1.18  tff(c_61, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_58])).
% 1.88/1.18  tff(c_65, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_61])).
% 1.88/1.18  tff(c_66, plain, (~v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_57])).
% 1.88/1.18  tff(c_18, plain, (![A_7]: (r2_hidden('#skF_1'(A_7), A_7) | v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.88/1.18  tff(c_4, plain, (![A_1]: (k4_xboole_0(k1_xboole_0, A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.88/1.18  tff(c_97, plain, (![B_43, A_44]: (~r2_hidden(B_43, A_44) | k4_xboole_0(A_44, k1_tarski(B_43))!=A_44)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.88/1.18  tff(c_107, plain, (![B_45]: (~r2_hidden(B_45, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_97])).
% 1.88/1.18  tff(c_111, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_107])).
% 1.88/1.18  tff(c_115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_111])).
% 1.88/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.18  
% 1.88/1.18  Inference rules
% 1.88/1.18  ----------------------
% 1.88/1.18  #Ref     : 0
% 1.88/1.18  #Sup     : 15
% 1.88/1.18  #Fact    : 0
% 1.88/1.18  #Define  : 0
% 1.88/1.18  #Split   : 1
% 1.88/1.18  #Chain   : 0
% 1.88/1.18  #Close   : 0
% 1.88/1.18  
% 1.88/1.18  Ordering : KBO
% 1.88/1.18  
% 1.88/1.18  Simplification rules
% 1.88/1.18  ----------------------
% 1.88/1.18  #Subsume      : 0
% 1.88/1.18  #Demod        : 3
% 1.88/1.18  #Tautology    : 11
% 1.88/1.18  #SimpNegUnit  : 1
% 1.88/1.18  #BackRed      : 0
% 1.88/1.18  
% 1.88/1.18  #Partial instantiations: 0
% 1.88/1.18  #Strategies tried      : 1
% 1.88/1.18  
% 1.88/1.18  Timing (in seconds)
% 1.88/1.18  ----------------------
% 1.88/1.18  Preprocessing        : 0.28
% 1.88/1.18  Parsing              : 0.15
% 1.88/1.18  CNF conversion       : 0.02
% 1.88/1.18  Main loop            : 0.10
% 1.88/1.18  Inferencing          : 0.04
% 1.88/1.18  Reduction            : 0.03
% 1.88/1.18  Demodulation         : 0.02
% 1.88/1.18  BG Simplification    : 0.01
% 1.88/1.18  Subsumption          : 0.01
% 1.88/1.18  Abstraction          : 0.01
% 1.88/1.18  MUC search           : 0.00
% 1.88/1.18  Cooper               : 0.00
% 1.88/1.18  Total                : 0.41
% 1.88/1.18  Index Insertion      : 0.00
% 1.88/1.18  Index Deletion       : 0.00
% 1.88/1.18  Index Matching       : 0.00
% 1.88/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
