%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:56 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   68 (  88 expanded)
%              Number of leaves         :   39 (  49 expanded)
%              Depth                    :    9
%              Number of atoms          :   64 ( 100 expanded)
%              Number of equality atoms :   15 (  29 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_10 > #skF_8 > #skF_9 > #skF_3 > #skF_2 > #skF_7 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_98,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_85,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_53,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k2_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relat_1)).

tff(c_50,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_66,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_234,plain,(
    ! [C_133,A_134] :
      ( r2_hidden(k4_tarski(C_133,'#skF_9'(A_134,k1_relat_1(A_134),C_133)),A_134)
      | ~ r2_hidden(C_133,k1_relat_1(A_134)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_14,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_92,plain,(
    ! [A_97,B_98,C_99] :
      ( ~ r1_xboole_0(A_97,B_98)
      | ~ r2_hidden(C_99,k3_xboole_0(A_97,B_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_103,plain,(
    ! [A_11,C_99] :
      ( ~ r1_xboole_0(A_11,k1_xboole_0)
      | ~ r2_hidden(C_99,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_92])).

tff(c_107,plain,(
    ! [C_99] : ~ r2_hidden(C_99,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_103])).

tff(c_258,plain,(
    ! [C_135] : ~ r2_hidden(C_135,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_234,c_107])).

tff(c_279,plain,(
    v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_4,c_258])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_293,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_279,c_6])).

tff(c_304,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_293])).

tff(c_305,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_336,plain,(
    ! [A_147,B_148,C_149] :
      ( ~ r1_xboole_0(A_147,B_148)
      | ~ r2_hidden(C_149,k3_xboole_0(A_147,B_148)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_347,plain,(
    ! [A_11,C_149] :
      ( ~ r1_xboole_0(A_11,k1_xboole_0)
      | ~ r2_hidden(C_149,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_336])).

tff(c_351,plain,(
    ! [C_149] : ~ r2_hidden(C_149,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_347])).

tff(c_34,plain,(
    ! [A_42] :
      ( r2_hidden('#skF_3'(A_42),A_42)
      | v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_361,plain,(
    ! [C_153] : ~ r2_hidden(C_153,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_347])).

tff(c_371,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_34,c_361])).

tff(c_306,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_442,plain,(
    ! [A_171,B_172] :
      ( r2_hidden('#skF_10'(A_171,B_172),k1_relat_1(B_172))
      | ~ r2_hidden(A_171,k2_relat_1(B_172))
      | ~ v1_relat_1(B_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_448,plain,(
    ! [A_171] :
      ( r2_hidden('#skF_10'(A_171,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_171,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_442])).

tff(c_451,plain,(
    ! [A_171] :
      ( r2_hidden('#skF_10'(A_171,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_171,k2_relat_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_448])).

tff(c_453,plain,(
    ! [A_173] : ~ r2_hidden(A_173,k2_relat_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_351,c_451])).

tff(c_462,plain,(
    v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_4,c_453])).

tff(c_469,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_462,c_6])).

tff(c_474,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_305,c_469])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:54:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.34  
% 2.31/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.34  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_10 > #skF_8 > #skF_9 > #skF_3 > #skF_2 > #skF_7 > #skF_5 > #skF_4
% 2.31/1.34  
% 2.31/1.34  %Foreground sorts:
% 2.31/1.34  
% 2.31/1.34  
% 2.31/1.34  %Background operators:
% 2.31/1.34  
% 2.31/1.34  
% 2.31/1.34  %Foreground operators:
% 2.31/1.34  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.31/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.31/1.34  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.31/1.34  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.31/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.31/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.31/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.31/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.31/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.31/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.31/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.31/1.34  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 2.31/1.34  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 2.31/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.31/1.34  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 2.31/1.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.31/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.31/1.34  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.31/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.31/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.31/1.34  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.31/1.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.31/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.31/1.34  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.31/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.31/1.34  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.31/1.34  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.31/1.34  
% 2.31/1.35  tff(f_98, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.31/1.35  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.31/1.35  tff(f_85, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 2.31/1.35  tff(f_53, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.31/1.35  tff(f_51, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.31/1.35  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.31/1.35  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.31/1.35  tff(f_77, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.31/1.35  tff(f_94, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k2_relat_1(B)) & (![C]: ~r2_hidden(C, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relat_1)).
% 2.31/1.35  tff(c_50, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.31/1.35  tff(c_66, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_50])).
% 2.31/1.35  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.31/1.35  tff(c_234, plain, (![C_133, A_134]: (r2_hidden(k4_tarski(C_133, '#skF_9'(A_134, k1_relat_1(A_134), C_133)), A_134) | ~r2_hidden(C_133, k1_relat_1(A_134)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.31/1.35  tff(c_14, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.31/1.35  tff(c_12, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.31/1.35  tff(c_92, plain, (![A_97, B_98, C_99]: (~r1_xboole_0(A_97, B_98) | ~r2_hidden(C_99, k3_xboole_0(A_97, B_98)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.31/1.35  tff(c_103, plain, (![A_11, C_99]: (~r1_xboole_0(A_11, k1_xboole_0) | ~r2_hidden(C_99, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_92])).
% 2.31/1.35  tff(c_107, plain, (![C_99]: (~r2_hidden(C_99, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_103])).
% 2.31/1.35  tff(c_258, plain, (![C_135]: (~r2_hidden(C_135, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_234, c_107])).
% 2.31/1.35  tff(c_279, plain, (v1_xboole_0(k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_258])).
% 2.31/1.35  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.31/1.35  tff(c_293, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_279, c_6])).
% 2.31/1.35  tff(c_304, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_293])).
% 2.31/1.35  tff(c_305, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 2.31/1.35  tff(c_336, plain, (![A_147, B_148, C_149]: (~r1_xboole_0(A_147, B_148) | ~r2_hidden(C_149, k3_xboole_0(A_147, B_148)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.31/1.35  tff(c_347, plain, (![A_11, C_149]: (~r1_xboole_0(A_11, k1_xboole_0) | ~r2_hidden(C_149, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_336])).
% 2.31/1.35  tff(c_351, plain, (![C_149]: (~r2_hidden(C_149, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_347])).
% 2.31/1.35  tff(c_34, plain, (![A_42]: (r2_hidden('#skF_3'(A_42), A_42) | v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.31/1.35  tff(c_361, plain, (![C_153]: (~r2_hidden(C_153, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_347])).
% 2.31/1.35  tff(c_371, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_361])).
% 2.31/1.35  tff(c_306, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 2.31/1.35  tff(c_442, plain, (![A_171, B_172]: (r2_hidden('#skF_10'(A_171, B_172), k1_relat_1(B_172)) | ~r2_hidden(A_171, k2_relat_1(B_172)) | ~v1_relat_1(B_172))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.31/1.35  tff(c_448, plain, (![A_171]: (r2_hidden('#skF_10'(A_171, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_171, k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_306, c_442])).
% 2.31/1.35  tff(c_451, plain, (![A_171]: (r2_hidden('#skF_10'(A_171, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_171, k2_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_371, c_448])).
% 2.31/1.35  tff(c_453, plain, (![A_173]: (~r2_hidden(A_173, k2_relat_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_351, c_451])).
% 2.31/1.35  tff(c_462, plain, (v1_xboole_0(k2_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_453])).
% 2.31/1.35  tff(c_469, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_462, c_6])).
% 2.31/1.35  tff(c_474, plain, $false, inference(negUnitSimplification, [status(thm)], [c_305, c_469])).
% 2.31/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.35  
% 2.31/1.35  Inference rules
% 2.31/1.35  ----------------------
% 2.31/1.35  #Ref     : 0
% 2.31/1.35  #Sup     : 83
% 2.31/1.35  #Fact    : 0
% 2.31/1.35  #Define  : 0
% 2.31/1.35  #Split   : 1
% 2.31/1.35  #Chain   : 0
% 2.31/1.35  #Close   : 0
% 2.31/1.35  
% 2.31/1.35  Ordering : KBO
% 2.31/1.35  
% 2.31/1.35  Simplification rules
% 2.31/1.35  ----------------------
% 2.31/1.35  #Subsume      : 3
% 2.31/1.35  #Demod        : 24
% 2.31/1.35  #Tautology    : 43
% 2.31/1.35  #SimpNegUnit  : 5
% 2.31/1.35  #BackRed      : 0
% 2.31/1.35  
% 2.31/1.35  #Partial instantiations: 0
% 2.31/1.35  #Strategies tried      : 1
% 2.31/1.35  
% 2.31/1.35  Timing (in seconds)
% 2.31/1.35  ----------------------
% 2.31/1.35  Preprocessing        : 0.33
% 2.31/1.35  Parsing              : 0.17
% 2.31/1.35  CNF conversion       : 0.03
% 2.31/1.35  Main loop            : 0.21
% 2.31/1.36  Inferencing          : 0.09
% 2.31/1.36  Reduction            : 0.06
% 2.31/1.36  Demodulation         : 0.04
% 2.31/1.36  BG Simplification    : 0.02
% 2.31/1.36  Subsumption          : 0.03
% 2.31/1.36  Abstraction          : 0.01
% 2.31/1.36  MUC search           : 0.00
% 2.31/1.36  Cooper               : 0.00
% 2.31/1.36  Total                : 0.57
% 2.31/1.36  Index Insertion      : 0.00
% 2.31/1.36  Index Deletion       : 0.00
% 2.31/1.36  Index Matching       : 0.00
% 2.31/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
