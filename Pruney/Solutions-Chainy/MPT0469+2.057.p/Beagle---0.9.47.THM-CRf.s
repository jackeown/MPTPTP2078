%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:59 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :   68 (  89 expanded)
%              Number of leaves         :   39 (  51 expanded)
%              Depth                    :    7
%              Number of atoms          :   62 ( 109 expanded)
%              Number of equality atoms :   16 (  40 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_10 > #skF_2 > #skF_8 > #skF_11 > #skF_7 > #skF_3 > #skF_9 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_90,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_78,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_48,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_74,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_123,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_22,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_566,plain,(
    ! [C_150,A_151] :
      ( r2_hidden(k4_tarski(C_150,'#skF_7'(A_151,k1_relat_1(A_151),C_150)),A_151)
      | ~ r2_hidden(C_150,k1_relat_1(A_151)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_64,plain,(
    ! [C_74,A_59,D_77] :
      ( r2_hidden(C_74,k2_relat_1(A_59))
      | ~ r2_hidden(k4_tarski(D_77,C_74),A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_598,plain,(
    ! [A_151,C_150] :
      ( r2_hidden('#skF_7'(A_151,k1_relat_1(A_151),C_150),k2_relat_1(A_151))
      | ~ r2_hidden(C_150,k1_relat_1(A_151)) ) ),
    inference(resolution,[status(thm)],[c_566,c_64])).

tff(c_62,plain,(
    ! [A_59,C_74] :
      ( r2_hidden(k4_tarski('#skF_11'(A_59,k2_relat_1(A_59),C_74),C_74),A_59)
      | ~ r2_hidden(C_74,k2_relat_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_452,plain,(
    ! [A_135,C_136] :
      ( r2_hidden(k4_tarski('#skF_11'(A_135,k2_relat_1(A_135),C_136),C_136),A_135)
      | ~ r2_hidden(C_136,k2_relat_1(A_135)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_26,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_186,plain,(
    ! [D_95,B_96,A_97] :
      ( ~ r2_hidden(D_95,B_96)
      | ~ r2_hidden(D_95,k4_xboole_0(A_97,B_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_193,plain,(
    ! [D_95,A_11] :
      ( ~ r2_hidden(D_95,k1_xboole_0)
      | ~ r2_hidden(D_95,A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_186])).

tff(c_620,plain,(
    ! [C_159,A_160] :
      ( ~ r2_hidden(k4_tarski('#skF_11'(k1_xboole_0,k2_relat_1(k1_xboole_0),C_159),C_159),A_160)
      | ~ r2_hidden(C_159,k2_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_452,c_193])).

tff(c_631,plain,(
    ! [C_161] : ~ r2_hidden(C_161,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_62,c_620])).

tff(c_726,plain,(
    ! [C_169] : ~ r2_hidden(C_169,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_598,c_631])).

tff(c_754,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_726])).

tff(c_765,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_754])).

tff(c_766,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_767,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_1284,plain,(
    ! [A_239,C_240] :
      ( r2_hidden(k4_tarski('#skF_11'(A_239,k2_relat_1(A_239),C_240),C_240),A_239)
      | ~ r2_hidden(C_240,k2_relat_1(A_239)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_52,plain,(
    ! [C_55,A_40,D_58] :
      ( r2_hidden(C_55,k1_relat_1(A_40))
      | ~ r2_hidden(k4_tarski(C_55,D_58),A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1321,plain,(
    ! [A_241,C_242] :
      ( r2_hidden('#skF_11'(A_241,k2_relat_1(A_241),C_242),k1_relat_1(A_241))
      | ~ r2_hidden(C_242,k2_relat_1(A_241)) ) ),
    inference(resolution,[status(thm)],[c_1284,c_52])).

tff(c_1324,plain,(
    ! [C_242] :
      ( r2_hidden('#skF_11'(k1_xboole_0,k2_relat_1(k1_xboole_0),C_242),k1_xboole_0)
      | ~ r2_hidden(C_242,k2_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_767,c_1321])).

tff(c_1325,plain,(
    ! [C_243] :
      ( r2_hidden('#skF_11'(k1_xboole_0,k2_relat_1(k1_xboole_0),C_243),k1_xboole_0)
      | ~ r2_hidden(C_243,k2_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_767,c_1321])).

tff(c_834,plain,(
    ! [D_181,B_182,A_183] :
      ( ~ r2_hidden(D_181,B_182)
      | ~ r2_hidden(D_181,k4_xboole_0(A_183,B_182)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_841,plain,(
    ! [D_181,A_11] :
      ( ~ r2_hidden(D_181,k1_xboole_0)
      | ~ r2_hidden(D_181,A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_834])).

tff(c_1332,plain,(
    ! [C_244,A_245] :
      ( ~ r2_hidden('#skF_11'(k1_xboole_0,k2_relat_1(k1_xboole_0),C_244),A_245)
      | ~ r2_hidden(C_244,k2_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_1325,c_841])).

tff(c_1347,plain,(
    ! [C_246] : ~ r2_hidden(C_246,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_1324,c_1332])).

tff(c_1381,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_1347])).

tff(c_1394,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_766,c_1381])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:30:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.33/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.57  
% 3.33/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.58  %$ r2_hidden > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_10 > #skF_2 > #skF_8 > #skF_11 > #skF_7 > #skF_3 > #skF_9 > #skF_5 > #skF_4
% 3.33/1.58  
% 3.33/1.58  %Foreground sorts:
% 3.33/1.58  
% 3.33/1.58  
% 3.33/1.58  %Background operators:
% 3.33/1.58  
% 3.33/1.58  
% 3.33/1.58  %Foreground operators:
% 3.33/1.58  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.33/1.58  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.33/1.58  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 3.33/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.33/1.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.33/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.33/1.58  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.33/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.33/1.58  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.33/1.58  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.33/1.58  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.33/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.33/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.33/1.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.33/1.58  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 3.33/1.58  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.33/1.58  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 3.33/1.58  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.33/1.58  tff('#skF_11', type, '#skF_11': ($i * $i * $i) > $i).
% 3.33/1.58  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 3.33/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.58  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.33/1.58  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.33/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.33/1.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.33/1.58  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.33/1.58  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 3.33/1.58  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.33/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.33/1.58  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.33/1.58  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.33/1.58  
% 3.33/1.59  tff(f_90, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.33/1.59  tff(f_44, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.33/1.59  tff(f_78, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 3.33/1.59  tff(f_86, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 3.33/1.59  tff(f_48, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.33/1.59  tff(f_36, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.33/1.59  tff(c_74, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.33/1.59  tff(c_123, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_74])).
% 3.33/1.59  tff(c_22, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.33/1.59  tff(c_566, plain, (![C_150, A_151]: (r2_hidden(k4_tarski(C_150, '#skF_7'(A_151, k1_relat_1(A_151), C_150)), A_151) | ~r2_hidden(C_150, k1_relat_1(A_151)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.33/1.59  tff(c_64, plain, (![C_74, A_59, D_77]: (r2_hidden(C_74, k2_relat_1(A_59)) | ~r2_hidden(k4_tarski(D_77, C_74), A_59))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.33/1.59  tff(c_598, plain, (![A_151, C_150]: (r2_hidden('#skF_7'(A_151, k1_relat_1(A_151), C_150), k2_relat_1(A_151)) | ~r2_hidden(C_150, k1_relat_1(A_151)))), inference(resolution, [status(thm)], [c_566, c_64])).
% 3.33/1.59  tff(c_62, plain, (![A_59, C_74]: (r2_hidden(k4_tarski('#skF_11'(A_59, k2_relat_1(A_59), C_74), C_74), A_59) | ~r2_hidden(C_74, k2_relat_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.33/1.59  tff(c_452, plain, (![A_135, C_136]: (r2_hidden(k4_tarski('#skF_11'(A_135, k2_relat_1(A_135), C_136), C_136), A_135) | ~r2_hidden(C_136, k2_relat_1(A_135)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.33/1.59  tff(c_26, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.33/1.59  tff(c_186, plain, (![D_95, B_96, A_97]: (~r2_hidden(D_95, B_96) | ~r2_hidden(D_95, k4_xboole_0(A_97, B_96)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.33/1.59  tff(c_193, plain, (![D_95, A_11]: (~r2_hidden(D_95, k1_xboole_0) | ~r2_hidden(D_95, A_11))), inference(superposition, [status(thm), theory('equality')], [c_26, c_186])).
% 3.33/1.59  tff(c_620, plain, (![C_159, A_160]: (~r2_hidden(k4_tarski('#skF_11'(k1_xboole_0, k2_relat_1(k1_xboole_0), C_159), C_159), A_160) | ~r2_hidden(C_159, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_452, c_193])).
% 3.33/1.59  tff(c_631, plain, (![C_161]: (~r2_hidden(C_161, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_62, c_620])).
% 3.33/1.59  tff(c_726, plain, (![C_169]: (~r2_hidden(C_169, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_598, c_631])).
% 3.33/1.59  tff(c_754, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_726])).
% 3.33/1.59  tff(c_765, plain, $false, inference(negUnitSimplification, [status(thm)], [c_123, c_754])).
% 3.33/1.59  tff(c_766, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_74])).
% 3.33/1.59  tff(c_767, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_74])).
% 3.33/1.59  tff(c_1284, plain, (![A_239, C_240]: (r2_hidden(k4_tarski('#skF_11'(A_239, k2_relat_1(A_239), C_240), C_240), A_239) | ~r2_hidden(C_240, k2_relat_1(A_239)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.33/1.59  tff(c_52, plain, (![C_55, A_40, D_58]: (r2_hidden(C_55, k1_relat_1(A_40)) | ~r2_hidden(k4_tarski(C_55, D_58), A_40))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.33/1.59  tff(c_1321, plain, (![A_241, C_242]: (r2_hidden('#skF_11'(A_241, k2_relat_1(A_241), C_242), k1_relat_1(A_241)) | ~r2_hidden(C_242, k2_relat_1(A_241)))), inference(resolution, [status(thm)], [c_1284, c_52])).
% 3.33/1.59  tff(c_1324, plain, (![C_242]: (r2_hidden('#skF_11'(k1_xboole_0, k2_relat_1(k1_xboole_0), C_242), k1_xboole_0) | ~r2_hidden(C_242, k2_relat_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_767, c_1321])).
% 3.33/1.59  tff(c_1325, plain, (![C_243]: (r2_hidden('#skF_11'(k1_xboole_0, k2_relat_1(k1_xboole_0), C_243), k1_xboole_0) | ~r2_hidden(C_243, k2_relat_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_767, c_1321])).
% 3.33/1.59  tff(c_834, plain, (![D_181, B_182, A_183]: (~r2_hidden(D_181, B_182) | ~r2_hidden(D_181, k4_xboole_0(A_183, B_182)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.33/1.59  tff(c_841, plain, (![D_181, A_11]: (~r2_hidden(D_181, k1_xboole_0) | ~r2_hidden(D_181, A_11))), inference(superposition, [status(thm), theory('equality')], [c_26, c_834])).
% 3.33/1.59  tff(c_1332, plain, (![C_244, A_245]: (~r2_hidden('#skF_11'(k1_xboole_0, k2_relat_1(k1_xboole_0), C_244), A_245) | ~r2_hidden(C_244, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_1325, c_841])).
% 3.33/1.59  tff(c_1347, plain, (![C_246]: (~r2_hidden(C_246, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_1324, c_1332])).
% 3.33/1.59  tff(c_1381, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_1347])).
% 3.33/1.59  tff(c_1394, plain, $false, inference(negUnitSimplification, [status(thm)], [c_766, c_1381])).
% 3.33/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.59  
% 3.33/1.59  Inference rules
% 3.33/1.59  ----------------------
% 3.33/1.59  #Ref     : 0
% 3.33/1.59  #Sup     : 288
% 3.33/1.59  #Fact    : 0
% 3.33/1.59  #Define  : 0
% 3.33/1.59  #Split   : 1
% 3.33/1.59  #Chain   : 0
% 3.33/1.59  #Close   : 0
% 3.33/1.59  
% 3.33/1.59  Ordering : KBO
% 3.33/1.59  
% 3.33/1.59  Simplification rules
% 3.33/1.59  ----------------------
% 3.33/1.59  #Subsume      : 55
% 3.33/1.59  #Demod        : 74
% 3.33/1.59  #Tautology    : 118
% 3.33/1.59  #SimpNegUnit  : 2
% 3.33/1.59  #BackRed      : 1
% 3.33/1.59  
% 3.33/1.59  #Partial instantiations: 0
% 3.33/1.59  #Strategies tried      : 1
% 3.33/1.59  
% 3.33/1.59  Timing (in seconds)
% 3.33/1.59  ----------------------
% 3.33/1.59  Preprocessing        : 0.36
% 3.33/1.59  Parsing              : 0.18
% 3.33/1.59  CNF conversion       : 0.03
% 3.33/1.59  Main loop            : 0.44
% 3.33/1.59  Inferencing          : 0.17
% 3.33/1.59  Reduction            : 0.12
% 3.33/1.59  Demodulation         : 0.09
% 3.33/1.59  BG Simplification    : 0.03
% 3.33/1.59  Subsumption          : 0.08
% 3.33/1.59  Abstraction          : 0.03
% 3.33/1.59  MUC search           : 0.00
% 3.33/1.59  Cooper               : 0.00
% 3.33/1.59  Total                : 0.83
% 3.33/1.59  Index Insertion      : 0.00
% 3.33/1.59  Index Deletion       : 0.00
% 3.33/1.59  Index Matching       : 0.00
% 3.33/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
