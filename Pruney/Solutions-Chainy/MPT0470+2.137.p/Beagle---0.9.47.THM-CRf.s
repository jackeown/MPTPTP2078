%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:20 EST 2020

% Result     : Theorem 5.21s
% Output     : CNFRefutation 5.56s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 161 expanded)
%              Number of leaves         :   32 (  67 expanded)
%              Depth                    :   11
%              Number of atoms          :  117 ( 258 expanded)
%              Number of equality atoms :   27 (  90 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k5_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_6 > #skF_4 > #skF_3 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_9 > #skF_11 > #skF_8 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_11',type,(
    '#skF_11': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( C = k5_relat_1(A,B)
              <=> ! [D,E] :
                    ( r2_hidden(k4_tarski(D,E),C)
                  <=> ? [F] :
                        ( r2_hidden(k4_tarski(D,F),A)
                        & r2_hidden(k4_tarski(F,E),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_54,plain,
    ( k5_relat_1('#skF_12',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_12') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_169,plain,(
    k5_relat_1(k1_xboole_0,'#skF_12') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_56,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_20,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_77,plain,(
    ! [A_128,B_129] : k4_xboole_0(A_128,k4_xboole_0(A_128,B_129)) = k3_xboole_0(A_128,B_129) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_95,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_77])).

tff(c_100,plain,(
    ! [A_132] : k4_xboole_0(A_132,A_132) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_95])).

tff(c_50,plain,(
    ! [A_119,B_120] :
      ( v1_relat_1(k4_xboole_0(A_119,B_120))
      | ~ v1_relat_1(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_108,plain,(
    ! [A_132] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_132) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_50])).

tff(c_143,plain,(
    ! [A_132] : ~ v1_relat_1(A_132) ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_148,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_56])).

tff(c_149,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_48,plain,(
    ! [A_117,B_118] :
      ( v1_relat_1(k5_relat_1(A_117,B_118))
      | ~ v1_relat_1(B_118)
      | ~ v1_relat_1(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_52,plain,(
    ! [A_121] :
      ( k1_xboole_0 = A_121
      | r2_hidden(k4_tarski('#skF_10'(A_121),'#skF_11'(A_121)),A_121)
      | ~ v1_relat_1(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1395,plain,(
    ! [D_231,B_232,A_233,E_234] :
      ( r2_hidden(k4_tarski(D_231,'#skF_4'(B_232,A_233,k5_relat_1(A_233,B_232),D_231,E_234)),A_233)
      | ~ r2_hidden(k4_tarski(D_231,E_234),k5_relat_1(A_233,B_232))
      | ~ v1_relat_1(k5_relat_1(A_233,B_232))
      | ~ v1_relat_1(B_232)
      | ~ v1_relat_1(A_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_98,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_95])).

tff(c_181,plain,(
    ! [A_146,B_147] :
      ( r2_hidden('#skF_3'(A_146,B_147),B_147)
      | ~ r2_hidden(A_146,B_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_199,plain,(
    ! [A_146,A_1,B_2] :
      ( r2_hidden('#skF_3'(A_146,k4_xboole_0(A_1,B_2)),A_1)
      | ~ r2_hidden(A_146,k4_xboole_0(A_1,B_2)) ) ),
    inference(resolution,[status(thm)],[c_181,c_6])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_459,plain,(
    ! [A_173,A_174,B_175] :
      ( ~ r2_hidden('#skF_3'(A_173,k4_xboole_0(A_174,B_175)),B_175)
      | ~ r2_hidden(A_173,k4_xboole_0(A_174,B_175)) ) ),
    inference(resolution,[status(thm)],[c_181,c_4])).

tff(c_463,plain,(
    ! [A_146,A_1] : ~ r2_hidden(A_146,k4_xboole_0(A_1,A_1)) ),
    inference(resolution,[status(thm)],[c_199,c_459])).

tff(c_481,plain,(
    ! [A_146] : ~ r2_hidden(A_146,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_463])).

tff(c_1405,plain,(
    ! [D_231,E_234,B_232] :
      ( ~ r2_hidden(k4_tarski(D_231,E_234),k5_relat_1(k1_xboole_0,B_232))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_232))
      | ~ v1_relat_1(B_232)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1395,c_481])).

tff(c_2613,plain,(
    ! [D_299,E_300,B_301] :
      ( ~ r2_hidden(k4_tarski(D_299,E_300),k5_relat_1(k1_xboole_0,B_301))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_301))
      | ~ v1_relat_1(B_301) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_1405])).

tff(c_2654,plain,(
    ! [B_302] :
      ( ~ v1_relat_1(B_302)
      | k5_relat_1(k1_xboole_0,B_302) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_302)) ) ),
    inference(resolution,[status(thm)],[c_52,c_2613])).

tff(c_2661,plain,(
    ! [B_118] :
      ( k5_relat_1(k1_xboole_0,B_118) = k1_xboole_0
      | ~ v1_relat_1(B_118)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_48,c_2654])).

tff(c_2667,plain,(
    ! [B_303] :
      ( k5_relat_1(k1_xboole_0,B_303) = k1_xboole_0
      | ~ v1_relat_1(B_303) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_2661])).

tff(c_2682,plain,(
    k5_relat_1(k1_xboole_0,'#skF_12') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_2667])).

tff(c_2691,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_2682])).

tff(c_2692,plain,(
    k5_relat_1('#skF_12',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_3744,plain,(
    ! [B_385,A_386,D_387,E_388] :
      ( r2_hidden(k4_tarski('#skF_4'(B_385,A_386,k5_relat_1(A_386,B_385),D_387,E_388),E_388),B_385)
      | ~ r2_hidden(k4_tarski(D_387,E_388),k5_relat_1(A_386,B_385))
      | ~ v1_relat_1(k5_relat_1(A_386,B_385))
      | ~ v1_relat_1(B_385)
      | ~ v1_relat_1(A_386) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2714,plain,(
    ! [A_309,B_310] :
      ( r2_hidden('#skF_3'(A_309,B_310),B_310)
      | ~ r2_hidden(A_309,B_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2976,plain,(
    ! [A_341,A_342,B_343] :
      ( r2_hidden('#skF_3'(A_341,k4_xboole_0(A_342,B_343)),A_342)
      | ~ r2_hidden(A_341,k4_xboole_0(A_342,B_343)) ) ),
    inference(resolution,[status(thm)],[c_2714,c_6])).

tff(c_2730,plain,(
    ! [A_309,A_1,B_2] :
      ( ~ r2_hidden('#skF_3'(A_309,k4_xboole_0(A_1,B_2)),B_2)
      | ~ r2_hidden(A_309,k4_xboole_0(A_1,B_2)) ) ),
    inference(resolution,[status(thm)],[c_2714,c_4])).

tff(c_2984,plain,(
    ! [A_341,A_342] : ~ r2_hidden(A_341,k4_xboole_0(A_342,A_342)) ),
    inference(resolution,[status(thm)],[c_2976,c_2730])).

tff(c_3029,plain,(
    ! [A_341] : ~ r2_hidden(A_341,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_2984])).

tff(c_3750,plain,(
    ! [D_387,E_388,A_386] :
      ( ~ r2_hidden(k4_tarski(D_387,E_388),k5_relat_1(A_386,k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_386,k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_386) ) ),
    inference(resolution,[status(thm)],[c_3744,c_3029])).

tff(c_5133,plain,(
    ! [D_464,E_465,A_466] :
      ( ~ r2_hidden(k4_tarski(D_464,E_465),k5_relat_1(A_466,k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_466,k1_xboole_0))
      | ~ v1_relat_1(A_466) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_3750])).

tff(c_5174,plain,(
    ! [A_467] :
      ( ~ v1_relat_1(A_467)
      | k5_relat_1(A_467,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_467,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_52,c_5133])).

tff(c_5181,plain,(
    ! [A_117] :
      ( k5_relat_1(A_117,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_117) ) ),
    inference(resolution,[status(thm)],[c_48,c_5174])).

tff(c_5187,plain,(
    ! [A_468] :
      ( k5_relat_1(A_468,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_468) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_5181])).

tff(c_5202,plain,(
    k5_relat_1('#skF_12',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_5187])).

tff(c_5211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2692,c_5202])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:44:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.21/2.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.49/2.05  
% 5.49/2.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.49/2.05  %$ r2_hidden > v1_relat_1 > k5_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_6 > #skF_4 > #skF_3 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_9 > #skF_11 > #skF_8 > #skF_12
% 5.49/2.05  
% 5.49/2.05  %Foreground sorts:
% 5.49/2.05  
% 5.49/2.05  
% 5.49/2.05  %Background operators:
% 5.49/2.05  
% 5.49/2.05  
% 5.49/2.05  %Foreground operators:
% 5.49/2.05  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.49/2.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.49/2.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.49/2.05  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 5.49/2.05  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.49/2.05  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.49/2.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.49/2.05  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 5.49/2.05  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.49/2.05  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.49/2.05  tff('#skF_10', type, '#skF_10': $i > $i).
% 5.49/2.05  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.49/2.05  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.49/2.05  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 5.49/2.05  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 5.49/2.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.49/2.05  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.49/2.05  tff('#skF_11', type, '#skF_11': $i > $i).
% 5.49/2.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.49/2.05  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.49/2.05  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 5.49/2.05  tff('#skF_12', type, '#skF_12': $i).
% 5.49/2.05  
% 5.56/2.07  tff(f_97, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 5.56/2.07  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 5.56/2.07  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 5.56/2.07  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.56/2.07  tff(f_82, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_relat_1)).
% 5.56/2.07  tff(f_78, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 5.56/2.07  tff(f_90, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 5.56/2.07  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_1)).
% 5.56/2.07  tff(f_54, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 5.56/2.07  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.56/2.07  tff(c_54, plain, (k5_relat_1('#skF_12', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_12')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.56/2.07  tff(c_169, plain, (k5_relat_1(k1_xboole_0, '#skF_12')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_54])).
% 5.56/2.07  tff(c_56, plain, (v1_relat_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.56/2.07  tff(c_20, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.56/2.07  tff(c_22, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.56/2.07  tff(c_77, plain, (![A_128, B_129]: (k4_xboole_0(A_128, k4_xboole_0(A_128, B_129))=k3_xboole_0(A_128, B_129))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.56/2.07  tff(c_95, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_77])).
% 5.56/2.07  tff(c_100, plain, (![A_132]: (k4_xboole_0(A_132, A_132)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_95])).
% 5.56/2.07  tff(c_50, plain, (![A_119, B_120]: (v1_relat_1(k4_xboole_0(A_119, B_120)) | ~v1_relat_1(A_119))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.56/2.07  tff(c_108, plain, (![A_132]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_132))), inference(superposition, [status(thm), theory('equality')], [c_100, c_50])).
% 5.56/2.07  tff(c_143, plain, (![A_132]: (~v1_relat_1(A_132))), inference(splitLeft, [status(thm)], [c_108])).
% 5.56/2.07  tff(c_148, plain, $false, inference(negUnitSimplification, [status(thm)], [c_143, c_56])).
% 5.56/2.07  tff(c_149, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_108])).
% 5.56/2.07  tff(c_48, plain, (![A_117, B_118]: (v1_relat_1(k5_relat_1(A_117, B_118)) | ~v1_relat_1(B_118) | ~v1_relat_1(A_117))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.56/2.07  tff(c_52, plain, (![A_121]: (k1_xboole_0=A_121 | r2_hidden(k4_tarski('#skF_10'(A_121), '#skF_11'(A_121)), A_121) | ~v1_relat_1(A_121))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.56/2.07  tff(c_1395, plain, (![D_231, B_232, A_233, E_234]: (r2_hidden(k4_tarski(D_231, '#skF_4'(B_232, A_233, k5_relat_1(A_233, B_232), D_231, E_234)), A_233) | ~r2_hidden(k4_tarski(D_231, E_234), k5_relat_1(A_233, B_232)) | ~v1_relat_1(k5_relat_1(A_233, B_232)) | ~v1_relat_1(B_232) | ~v1_relat_1(A_233))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.56/2.07  tff(c_98, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_95])).
% 5.56/2.07  tff(c_181, plain, (![A_146, B_147]: (r2_hidden('#skF_3'(A_146, B_147), B_147) | ~r2_hidden(A_146, B_147))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.56/2.07  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.56/2.07  tff(c_199, plain, (![A_146, A_1, B_2]: (r2_hidden('#skF_3'(A_146, k4_xboole_0(A_1, B_2)), A_1) | ~r2_hidden(A_146, k4_xboole_0(A_1, B_2)))), inference(resolution, [status(thm)], [c_181, c_6])).
% 5.56/2.07  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.56/2.07  tff(c_459, plain, (![A_173, A_174, B_175]: (~r2_hidden('#skF_3'(A_173, k4_xboole_0(A_174, B_175)), B_175) | ~r2_hidden(A_173, k4_xboole_0(A_174, B_175)))), inference(resolution, [status(thm)], [c_181, c_4])).
% 5.56/2.07  tff(c_463, plain, (![A_146, A_1]: (~r2_hidden(A_146, k4_xboole_0(A_1, A_1)))), inference(resolution, [status(thm)], [c_199, c_459])).
% 5.56/2.07  tff(c_481, plain, (![A_146]: (~r2_hidden(A_146, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_463])).
% 5.56/2.07  tff(c_1405, plain, (![D_231, E_234, B_232]: (~r2_hidden(k4_tarski(D_231, E_234), k5_relat_1(k1_xboole_0, B_232)) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_232)) | ~v1_relat_1(B_232) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_1395, c_481])).
% 5.56/2.07  tff(c_2613, plain, (![D_299, E_300, B_301]: (~r2_hidden(k4_tarski(D_299, E_300), k5_relat_1(k1_xboole_0, B_301)) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_301)) | ~v1_relat_1(B_301))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_1405])).
% 5.56/2.07  tff(c_2654, plain, (![B_302]: (~v1_relat_1(B_302) | k5_relat_1(k1_xboole_0, B_302)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_302)))), inference(resolution, [status(thm)], [c_52, c_2613])).
% 5.56/2.07  tff(c_2661, plain, (![B_118]: (k5_relat_1(k1_xboole_0, B_118)=k1_xboole_0 | ~v1_relat_1(B_118) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_48, c_2654])).
% 5.56/2.07  tff(c_2667, plain, (![B_303]: (k5_relat_1(k1_xboole_0, B_303)=k1_xboole_0 | ~v1_relat_1(B_303))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_2661])).
% 5.56/2.07  tff(c_2682, plain, (k5_relat_1(k1_xboole_0, '#skF_12')=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_2667])).
% 5.56/2.07  tff(c_2691, plain, $false, inference(negUnitSimplification, [status(thm)], [c_169, c_2682])).
% 5.56/2.07  tff(c_2692, plain, (k5_relat_1('#skF_12', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 5.56/2.07  tff(c_3744, plain, (![B_385, A_386, D_387, E_388]: (r2_hidden(k4_tarski('#skF_4'(B_385, A_386, k5_relat_1(A_386, B_385), D_387, E_388), E_388), B_385) | ~r2_hidden(k4_tarski(D_387, E_388), k5_relat_1(A_386, B_385)) | ~v1_relat_1(k5_relat_1(A_386, B_385)) | ~v1_relat_1(B_385) | ~v1_relat_1(A_386))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.56/2.07  tff(c_2714, plain, (![A_309, B_310]: (r2_hidden('#skF_3'(A_309, B_310), B_310) | ~r2_hidden(A_309, B_310))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.56/2.07  tff(c_2976, plain, (![A_341, A_342, B_343]: (r2_hidden('#skF_3'(A_341, k4_xboole_0(A_342, B_343)), A_342) | ~r2_hidden(A_341, k4_xboole_0(A_342, B_343)))), inference(resolution, [status(thm)], [c_2714, c_6])).
% 5.56/2.07  tff(c_2730, plain, (![A_309, A_1, B_2]: (~r2_hidden('#skF_3'(A_309, k4_xboole_0(A_1, B_2)), B_2) | ~r2_hidden(A_309, k4_xboole_0(A_1, B_2)))), inference(resolution, [status(thm)], [c_2714, c_4])).
% 5.56/2.07  tff(c_2984, plain, (![A_341, A_342]: (~r2_hidden(A_341, k4_xboole_0(A_342, A_342)))), inference(resolution, [status(thm)], [c_2976, c_2730])).
% 5.56/2.07  tff(c_3029, plain, (![A_341]: (~r2_hidden(A_341, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_2984])).
% 5.56/2.07  tff(c_3750, plain, (![D_387, E_388, A_386]: (~r2_hidden(k4_tarski(D_387, E_388), k5_relat_1(A_386, k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_386, k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_386))), inference(resolution, [status(thm)], [c_3744, c_3029])).
% 5.56/2.07  tff(c_5133, plain, (![D_464, E_465, A_466]: (~r2_hidden(k4_tarski(D_464, E_465), k5_relat_1(A_466, k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_466, k1_xboole_0)) | ~v1_relat_1(A_466))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_3750])).
% 5.56/2.07  tff(c_5174, plain, (![A_467]: (~v1_relat_1(A_467) | k5_relat_1(A_467, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_467, k1_xboole_0)))), inference(resolution, [status(thm)], [c_52, c_5133])).
% 5.56/2.07  tff(c_5181, plain, (![A_117]: (k5_relat_1(A_117, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_117))), inference(resolution, [status(thm)], [c_48, c_5174])).
% 5.56/2.07  tff(c_5187, plain, (![A_468]: (k5_relat_1(A_468, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_468))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_5181])).
% 5.56/2.07  tff(c_5202, plain, (k5_relat_1('#skF_12', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_5187])).
% 5.56/2.07  tff(c_5211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2692, c_5202])).
% 5.56/2.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.56/2.07  
% 5.56/2.07  Inference rules
% 5.56/2.07  ----------------------
% 5.56/2.07  #Ref     : 0
% 5.56/2.07  #Sup     : 1089
% 5.56/2.07  #Fact    : 0
% 5.56/2.07  #Define  : 0
% 5.56/2.07  #Split   : 3
% 5.56/2.07  #Chain   : 0
% 5.56/2.07  #Close   : 0
% 5.56/2.07  
% 5.56/2.07  Ordering : KBO
% 5.56/2.07  
% 5.56/2.07  Simplification rules
% 5.56/2.07  ----------------------
% 5.56/2.07  #Subsume      : 286
% 5.56/2.07  #Demod        : 577
% 5.56/2.07  #Tautology    : 248
% 5.56/2.07  #SimpNegUnit  : 47
% 5.56/2.07  #BackRed      : 13
% 5.56/2.07  
% 5.56/2.07  #Partial instantiations: 0
% 5.56/2.07  #Strategies tried      : 1
% 5.56/2.07  
% 5.56/2.07  Timing (in seconds)
% 5.56/2.07  ----------------------
% 5.56/2.07  Preprocessing        : 0.30
% 5.56/2.07  Parsing              : 0.15
% 5.56/2.07  CNF conversion       : 0.03
% 5.56/2.07  Main loop            : 0.95
% 5.56/2.07  Inferencing          : 0.35
% 5.56/2.07  Reduction            : 0.28
% 5.56/2.07  Demodulation         : 0.20
% 5.56/2.07  BG Simplification    : 0.04
% 5.56/2.07  Subsumption          : 0.20
% 5.56/2.07  Abstraction          : 0.06
% 5.56/2.07  MUC search           : 0.00
% 5.56/2.07  Cooper               : 0.00
% 5.56/2.07  Total                : 1.28
% 5.56/2.07  Index Insertion      : 0.00
% 5.56/2.07  Index Deletion       : 0.00
% 5.56/2.07  Index Matching       : 0.00
% 5.56/2.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
