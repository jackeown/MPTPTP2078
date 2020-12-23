%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:56 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 259 expanded)
%              Number of leaves         :   29 (  95 expanded)
%              Depth                    :   13
%              Number of atoms          :  110 ( 535 expanded)
%              Number of equality atoms :   23 ( 102 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_12 > #skF_10 > #skF_8 > #skF_11 > #skF_2 > #skF_7 > #skF_1 > #skF_9 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_96,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_52,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_83,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k2_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

tff(c_42,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_45,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r2_hidden('#skF_2'(A_1,B_2),A_1)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_136,plain,(
    ! [A_91,B_92] :
      ( r2_hidden('#skF_1'(A_91,B_92),B_92)
      | r2_hidden('#skF_2'(A_91,B_92),A_91)
      | B_92 = A_91 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_51,plain,(
    ! [A_71,B_72,C_73] :
      ( ~ r1_xboole_0(A_71,B_72)
      | ~ r2_hidden(C_73,B_72)
      | ~ r2_hidden(C_73,A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_54,plain,(
    ! [C_73,A_9] :
      ( ~ r2_hidden(C_73,k1_xboole_0)
      | ~ r2_hidden(C_73,A_9) ) ),
    inference(resolution,[status(thm)],[c_16,c_51])).

tff(c_187,plain,(
    ! [B_99,A_100] :
      ( ~ r2_hidden('#skF_2'(k1_xboole_0,B_99),A_100)
      | r2_hidden('#skF_1'(k1_xboole_0,B_99),B_99)
      | k1_xboole_0 = B_99 ) ),
    inference(resolution,[status(thm)],[c_136,c_54])).

tff(c_194,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_2),B_2)
      | k1_xboole_0 = B_2 ) ),
    inference(resolution,[status(thm)],[c_8,c_187])).

tff(c_28,plain,(
    ! [C_50,A_35] :
      ( r2_hidden(k4_tarski(C_50,'#skF_11'(A_35,k1_relat_1(A_35),C_50)),A_35)
      | ~ r2_hidden(C_50,k1_relat_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_212,plain,(
    ! [C_102,A_103] :
      ( r2_hidden(k4_tarski(C_102,'#skF_11'(A_103,k1_relat_1(A_103),C_102)),A_103)
      | ~ r2_hidden(C_102,k1_relat_1(A_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_251,plain,(
    ! [C_116,A_117] :
      ( ~ r2_hidden(k4_tarski(C_116,'#skF_11'(k1_xboole_0,k1_relat_1(k1_xboole_0),C_116)),A_117)
      | ~ r2_hidden(C_116,k1_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_212,c_54])).

tff(c_257,plain,(
    ! [C_118] : ~ r2_hidden(C_118,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_28,c_251])).

tff(c_265,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_194,c_257])).

tff(c_306,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_265])).

tff(c_307,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_26,plain,(
    ! [A_17] :
      ( r2_hidden('#skF_5'(A_17),A_17)
      | v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_318,plain,(
    ! [A_131,B_132,C_133] :
      ( ~ r1_xboole_0(A_131,B_132)
      | ~ r2_hidden(C_133,B_132)
      | ~ r2_hidden(C_133,A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_322,plain,(
    ! [C_134,A_135] :
      ( ~ r2_hidden(C_134,k1_xboole_0)
      | ~ r2_hidden(C_134,A_135) ) ),
    inference(resolution,[status(thm)],[c_16,c_318])).

tff(c_339,plain,(
    ! [A_135] :
      ( ~ r2_hidden('#skF_5'(k1_xboole_0),A_135)
      | v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_322])).

tff(c_341,plain,(
    ! [A_136] : ~ r2_hidden('#skF_5'(k1_xboole_0),A_136) ),
    inference(splitLeft,[status(thm)],[c_339])).

tff(c_346,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26,c_341])).

tff(c_308,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_414,plain,(
    ! [A_149,B_150] :
      ( r2_hidden('#skF_12'(A_149,B_150),k1_relat_1(B_150))
      | ~ r2_hidden(A_149,k2_relat_1(B_150))
      | ~ v1_relat_1(B_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_417,plain,(
    ! [A_149] :
      ( r2_hidden('#skF_12'(A_149,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_149,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_414])).

tff(c_419,plain,(
    ! [A_149] :
      ( r2_hidden('#skF_12'(A_149,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_149,k2_relat_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_417])).

tff(c_420,plain,(
    ! [A_151] :
      ( r2_hidden('#skF_12'(A_151,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_151,k2_relat_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_417])).

tff(c_321,plain,(
    ! [C_133,A_9] :
      ( ~ r2_hidden(C_133,k1_xboole_0)
      | ~ r2_hidden(C_133,A_9) ) ),
    inference(resolution,[status(thm)],[c_16,c_318])).

tff(c_424,plain,(
    ! [A_152,A_153] :
      ( ~ r2_hidden('#skF_12'(A_152,k1_xboole_0),A_153)
      | ~ r2_hidden(A_152,k2_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_420,c_321])).

tff(c_436,plain,(
    ! [A_154] : ~ r2_hidden(A_154,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_419,c_424])).

tff(c_461,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_2'(A_1,k2_relat_1(k1_xboole_0)),A_1)
      | k2_relat_1(k1_xboole_0) = A_1 ) ),
    inference(resolution,[status(thm)],[c_8,c_436])).

tff(c_496,plain,(
    ! [A_159] :
      ( r2_hidden('#skF_2'(A_159,k2_relat_1(k1_xboole_0)),A_159)
      | k2_relat_1(k1_xboole_0) = A_159 ) ),
    inference(resolution,[status(thm)],[c_8,c_436])).

tff(c_511,plain,(
    ! [A_9] :
      ( ~ r2_hidden('#skF_2'(k1_xboole_0,k2_relat_1(k1_xboole_0)),A_9)
      | k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_496,c_321])).

tff(c_522,plain,(
    ! [A_160] : ~ r2_hidden('#skF_2'(k1_xboole_0,k2_relat_1(k1_xboole_0)),A_160) ),
    inference(negUnitSimplification,[status(thm)],[c_307,c_511])).

tff(c_526,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_461,c_522])).

tff(c_536,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_307,c_526])).

tff(c_537,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_339])).

tff(c_621,plain,(
    ! [A_175,B_176] :
      ( r2_hidden('#skF_12'(A_175,B_176),k1_relat_1(B_176))
      | ~ r2_hidden(A_175,k2_relat_1(B_176))
      | ~ v1_relat_1(B_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_624,plain,(
    ! [A_175] :
      ( r2_hidden('#skF_12'(A_175,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_175,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_621])).

tff(c_626,plain,(
    ! [A_175] :
      ( r2_hidden('#skF_12'(A_175,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_175,k2_relat_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_537,c_624])).

tff(c_627,plain,(
    ! [A_177] :
      ( r2_hidden('#skF_12'(A_177,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_177,k2_relat_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_537,c_624])).

tff(c_631,plain,(
    ! [A_178,A_179] :
      ( ~ r2_hidden('#skF_12'(A_178,k1_xboole_0),A_179)
      | ~ r2_hidden(A_178,k2_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_627,c_321])).

tff(c_643,plain,(
    ! [A_180] : ~ r2_hidden(A_180,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_626,c_631])).

tff(c_673,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_1'(k2_relat_1(k1_xboole_0),B_2),B_2)
      | k2_relat_1(k1_xboole_0) = B_2 ) ),
    inference(resolution,[status(thm)],[c_8,c_643])).

tff(c_689,plain,(
    ! [B_185] :
      ( r2_hidden('#skF_1'(k2_relat_1(k1_xboole_0),B_185),B_185)
      | k2_relat_1(k1_xboole_0) = B_185 ) ),
    inference(resolution,[status(thm)],[c_8,c_643])).

tff(c_703,plain,(
    ! [A_9] :
      ( ~ r2_hidden('#skF_1'(k2_relat_1(k1_xboole_0),k1_xboole_0),A_9)
      | k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_689,c_321])).

tff(c_711,plain,(
    ! [A_186] : ~ r2_hidden('#skF_1'(k2_relat_1(k1_xboole_0),k1_xboole_0),A_186) ),
    inference(negUnitSimplification,[status(thm)],[c_307,c_703])).

tff(c_715,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_673,c_711])).

tff(c_721,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_307,c_715])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:54:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.38  
% 2.54/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.38  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_12 > #skF_10 > #skF_8 > #skF_11 > #skF_2 > #skF_7 > #skF_1 > #skF_9 > #skF_4
% 2.54/1.38  
% 2.54/1.38  %Foreground sorts:
% 2.54/1.38  
% 2.54/1.38  
% 2.54/1.38  %Background operators:
% 2.54/1.38  
% 2.54/1.38  
% 2.54/1.38  %Foreground operators:
% 2.54/1.38  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.54/1.38  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.54/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.54/1.38  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.54/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.54/1.38  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.54/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.54/1.38  tff('#skF_12', type, '#skF_12': ($i * $i) > $i).
% 2.54/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.54/1.38  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 2.54/1.38  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 2.54/1.38  tff('#skF_11', type, '#skF_11': ($i * $i * $i) > $i).
% 2.54/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.54/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.54/1.38  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.54/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.54/1.38  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 2.54/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.54/1.38  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.54/1.38  
% 2.54/1.40  tff(f_96, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.54/1.40  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 2.54/1.40  tff(f_52, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.54/1.40  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.54/1.40  tff(f_83, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 2.54/1.40  tff(f_75, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.54/1.40  tff(f_92, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k2_relat_1(B)) & (![C]: ~r2_hidden(C, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relat_1)).
% 2.54/1.40  tff(c_42, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.54/1.40  tff(c_45, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_42])).
% 2.54/1.40  tff(c_8, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r2_hidden('#skF_2'(A_1, B_2), A_1) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.54/1.40  tff(c_136, plain, (![A_91, B_92]: (r2_hidden('#skF_1'(A_91, B_92), B_92) | r2_hidden('#skF_2'(A_91, B_92), A_91) | B_92=A_91)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.54/1.40  tff(c_16, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.54/1.40  tff(c_51, plain, (![A_71, B_72, C_73]: (~r1_xboole_0(A_71, B_72) | ~r2_hidden(C_73, B_72) | ~r2_hidden(C_73, A_71))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.54/1.40  tff(c_54, plain, (![C_73, A_9]: (~r2_hidden(C_73, k1_xboole_0) | ~r2_hidden(C_73, A_9))), inference(resolution, [status(thm)], [c_16, c_51])).
% 2.54/1.40  tff(c_187, plain, (![B_99, A_100]: (~r2_hidden('#skF_2'(k1_xboole_0, B_99), A_100) | r2_hidden('#skF_1'(k1_xboole_0, B_99), B_99) | k1_xboole_0=B_99)), inference(resolution, [status(thm)], [c_136, c_54])).
% 2.54/1.40  tff(c_194, plain, (![B_2]: (r2_hidden('#skF_1'(k1_xboole_0, B_2), B_2) | k1_xboole_0=B_2)), inference(resolution, [status(thm)], [c_8, c_187])).
% 2.54/1.40  tff(c_28, plain, (![C_50, A_35]: (r2_hidden(k4_tarski(C_50, '#skF_11'(A_35, k1_relat_1(A_35), C_50)), A_35) | ~r2_hidden(C_50, k1_relat_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.54/1.40  tff(c_212, plain, (![C_102, A_103]: (r2_hidden(k4_tarski(C_102, '#skF_11'(A_103, k1_relat_1(A_103), C_102)), A_103) | ~r2_hidden(C_102, k1_relat_1(A_103)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.54/1.40  tff(c_251, plain, (![C_116, A_117]: (~r2_hidden(k4_tarski(C_116, '#skF_11'(k1_xboole_0, k1_relat_1(k1_xboole_0), C_116)), A_117) | ~r2_hidden(C_116, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_212, c_54])).
% 2.54/1.40  tff(c_257, plain, (![C_118]: (~r2_hidden(C_118, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_28, c_251])).
% 2.54/1.40  tff(c_265, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_194, c_257])).
% 2.54/1.40  tff(c_306, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_265])).
% 2.54/1.40  tff(c_307, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 2.54/1.40  tff(c_26, plain, (![A_17]: (r2_hidden('#skF_5'(A_17), A_17) | v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.54/1.40  tff(c_318, plain, (![A_131, B_132, C_133]: (~r1_xboole_0(A_131, B_132) | ~r2_hidden(C_133, B_132) | ~r2_hidden(C_133, A_131))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.54/1.40  tff(c_322, plain, (![C_134, A_135]: (~r2_hidden(C_134, k1_xboole_0) | ~r2_hidden(C_134, A_135))), inference(resolution, [status(thm)], [c_16, c_318])).
% 2.54/1.40  tff(c_339, plain, (![A_135]: (~r2_hidden('#skF_5'(k1_xboole_0), A_135) | v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_322])).
% 2.54/1.40  tff(c_341, plain, (![A_136]: (~r2_hidden('#skF_5'(k1_xboole_0), A_136))), inference(splitLeft, [status(thm)], [c_339])).
% 2.54/1.40  tff(c_346, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_341])).
% 2.54/1.40  tff(c_308, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 2.54/1.40  tff(c_414, plain, (![A_149, B_150]: (r2_hidden('#skF_12'(A_149, B_150), k1_relat_1(B_150)) | ~r2_hidden(A_149, k2_relat_1(B_150)) | ~v1_relat_1(B_150))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.54/1.40  tff(c_417, plain, (![A_149]: (r2_hidden('#skF_12'(A_149, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_149, k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_308, c_414])).
% 2.54/1.40  tff(c_419, plain, (![A_149]: (r2_hidden('#skF_12'(A_149, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_149, k2_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_346, c_417])).
% 2.54/1.40  tff(c_420, plain, (![A_151]: (r2_hidden('#skF_12'(A_151, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_151, k2_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_346, c_417])).
% 2.54/1.40  tff(c_321, plain, (![C_133, A_9]: (~r2_hidden(C_133, k1_xboole_0) | ~r2_hidden(C_133, A_9))), inference(resolution, [status(thm)], [c_16, c_318])).
% 2.54/1.40  tff(c_424, plain, (![A_152, A_153]: (~r2_hidden('#skF_12'(A_152, k1_xboole_0), A_153) | ~r2_hidden(A_152, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_420, c_321])).
% 2.54/1.40  tff(c_436, plain, (![A_154]: (~r2_hidden(A_154, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_419, c_424])).
% 2.54/1.40  tff(c_461, plain, (![A_1]: (r2_hidden('#skF_2'(A_1, k2_relat_1(k1_xboole_0)), A_1) | k2_relat_1(k1_xboole_0)=A_1)), inference(resolution, [status(thm)], [c_8, c_436])).
% 2.54/1.40  tff(c_496, plain, (![A_159]: (r2_hidden('#skF_2'(A_159, k2_relat_1(k1_xboole_0)), A_159) | k2_relat_1(k1_xboole_0)=A_159)), inference(resolution, [status(thm)], [c_8, c_436])).
% 2.54/1.40  tff(c_511, plain, (![A_9]: (~r2_hidden('#skF_2'(k1_xboole_0, k2_relat_1(k1_xboole_0)), A_9) | k2_relat_1(k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_496, c_321])).
% 2.54/1.40  tff(c_522, plain, (![A_160]: (~r2_hidden('#skF_2'(k1_xboole_0, k2_relat_1(k1_xboole_0)), A_160))), inference(negUnitSimplification, [status(thm)], [c_307, c_511])).
% 2.54/1.40  tff(c_526, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_461, c_522])).
% 2.54/1.40  tff(c_536, plain, $false, inference(negUnitSimplification, [status(thm)], [c_307, c_526])).
% 2.54/1.40  tff(c_537, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_339])).
% 2.54/1.40  tff(c_621, plain, (![A_175, B_176]: (r2_hidden('#skF_12'(A_175, B_176), k1_relat_1(B_176)) | ~r2_hidden(A_175, k2_relat_1(B_176)) | ~v1_relat_1(B_176))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.54/1.40  tff(c_624, plain, (![A_175]: (r2_hidden('#skF_12'(A_175, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_175, k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_308, c_621])).
% 2.54/1.40  tff(c_626, plain, (![A_175]: (r2_hidden('#skF_12'(A_175, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_175, k2_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_537, c_624])).
% 2.54/1.40  tff(c_627, plain, (![A_177]: (r2_hidden('#skF_12'(A_177, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_177, k2_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_537, c_624])).
% 2.54/1.40  tff(c_631, plain, (![A_178, A_179]: (~r2_hidden('#skF_12'(A_178, k1_xboole_0), A_179) | ~r2_hidden(A_178, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_627, c_321])).
% 2.54/1.40  tff(c_643, plain, (![A_180]: (~r2_hidden(A_180, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_626, c_631])).
% 2.54/1.40  tff(c_673, plain, (![B_2]: (r2_hidden('#skF_1'(k2_relat_1(k1_xboole_0), B_2), B_2) | k2_relat_1(k1_xboole_0)=B_2)), inference(resolution, [status(thm)], [c_8, c_643])).
% 2.54/1.40  tff(c_689, plain, (![B_185]: (r2_hidden('#skF_1'(k2_relat_1(k1_xboole_0), B_185), B_185) | k2_relat_1(k1_xboole_0)=B_185)), inference(resolution, [status(thm)], [c_8, c_643])).
% 2.54/1.40  tff(c_703, plain, (![A_9]: (~r2_hidden('#skF_1'(k2_relat_1(k1_xboole_0), k1_xboole_0), A_9) | k2_relat_1(k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_689, c_321])).
% 2.54/1.40  tff(c_711, plain, (![A_186]: (~r2_hidden('#skF_1'(k2_relat_1(k1_xboole_0), k1_xboole_0), A_186))), inference(negUnitSimplification, [status(thm)], [c_307, c_703])).
% 2.54/1.40  tff(c_715, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_673, c_711])).
% 2.54/1.40  tff(c_721, plain, $false, inference(negUnitSimplification, [status(thm)], [c_307, c_715])).
% 2.54/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.40  
% 2.54/1.40  Inference rules
% 2.54/1.40  ----------------------
% 2.54/1.40  #Ref     : 1
% 2.54/1.40  #Sup     : 125
% 2.54/1.40  #Fact    : 0
% 2.54/1.40  #Define  : 0
% 2.54/1.40  #Split   : 3
% 2.54/1.40  #Chain   : 0
% 2.54/1.40  #Close   : 0
% 2.54/1.40  
% 2.54/1.40  Ordering : KBO
% 2.54/1.40  
% 2.54/1.40  Simplification rules
% 2.54/1.40  ----------------------
% 2.54/1.40  #Subsume      : 26
% 2.54/1.40  #Demod        : 12
% 2.54/1.40  #Tautology    : 25
% 2.54/1.40  #SimpNegUnit  : 6
% 2.54/1.40  #BackRed      : 0
% 2.54/1.40  
% 2.54/1.40  #Partial instantiations: 0
% 2.54/1.40  #Strategies tried      : 1
% 2.54/1.40  
% 2.54/1.40  Timing (in seconds)
% 2.54/1.40  ----------------------
% 2.54/1.40  Preprocessing        : 0.30
% 2.54/1.40  Parsing              : 0.16
% 2.54/1.40  CNF conversion       : 0.03
% 2.54/1.40  Main loop            : 0.33
% 2.54/1.40  Inferencing          : 0.15
% 2.54/1.40  Reduction            : 0.07
% 2.54/1.40  Demodulation         : 0.05
% 2.54/1.40  BG Simplification    : 0.02
% 2.54/1.40  Subsumption          : 0.06
% 2.54/1.40  Abstraction          : 0.01
% 2.54/1.40  MUC search           : 0.00
% 2.54/1.40  Cooper               : 0.00
% 2.54/1.40  Total                : 0.67
% 2.54/1.40  Index Insertion      : 0.00
% 2.54/1.40  Index Deletion       : 0.00
% 2.54/1.40  Index Matching       : 0.00
% 2.54/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
