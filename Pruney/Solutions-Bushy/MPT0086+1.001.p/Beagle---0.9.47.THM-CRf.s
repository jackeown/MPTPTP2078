%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0086+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:42 EST 2020

% Result     : Theorem 5.73s
% Output     : CNFRefutation 5.73s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 185 expanded)
%              Number of leaves         :   19 (  71 expanded)
%              Depth                    :   15
%              Number of atoms          :   98 ( 479 expanded)
%              Number of equality atoms :   39 ( 149 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_51,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_36,plain,(
    ! [A_7,B_8,C_9] :
      ( r2_hidden('#skF_3'(A_7,B_8,C_9),A_7)
      | r2_hidden('#skF_4'(A_7,B_8,C_9),C_9)
      | k4_xboole_0(A_7,B_8) = C_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_996,plain,(
    ! [A_112,B_113,C_114] :
      ( r2_hidden('#skF_3'(A_112,B_113,C_114),A_112)
      | r2_hidden('#skF_4'(A_112,B_113,C_114),B_113)
      | ~ r2_hidden('#skF_4'(A_112,B_113,C_114),A_112)
      | k4_xboole_0(A_112,B_113) = C_114 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1019,plain,(
    ! [C_9,B_8] :
      ( r2_hidden('#skF_4'(C_9,B_8,C_9),B_8)
      | r2_hidden('#skF_3'(C_9,B_8,C_9),C_9)
      | k4_xboole_0(C_9,B_8) = C_9 ) ),
    inference(resolution,[status(thm)],[c_36,c_996])).

tff(c_32,plain,(
    ! [A_7,B_8,C_9] :
      ( ~ r2_hidden('#skF_3'(A_7,B_8,C_9),C_9)
      | r2_hidden('#skF_4'(A_7,B_8,C_9),C_9)
      | k4_xboole_0(A_7,B_8) = C_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1143,plain,(
    ! [C_121,B_122] :
      ( r2_hidden('#skF_4'(C_121,B_122,C_121),B_122)
      | r2_hidden('#skF_3'(C_121,B_122,C_121),C_121)
      | k4_xboole_0(C_121,B_122) = C_121 ) ),
    inference(resolution,[status(thm)],[c_36,c_996])).

tff(c_26,plain,(
    ! [A_7,B_8,C_9] :
      ( ~ r2_hidden('#skF_3'(A_7,B_8,C_9),C_9)
      | r2_hidden('#skF_4'(A_7,B_8,C_9),B_8)
      | ~ r2_hidden('#skF_4'(A_7,B_8,C_9),A_7)
      | k4_xboole_0(A_7,B_8) = C_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1294,plain,(
    ! [C_128,B_129] :
      ( ~ r2_hidden('#skF_4'(C_128,B_129,C_128),C_128)
      | r2_hidden('#skF_4'(C_128,B_129,C_128),B_129)
      | k4_xboole_0(C_128,B_129) = C_128 ) ),
    inference(resolution,[status(thm)],[c_1143,c_26])).

tff(c_4003,plain,(
    ! [C_271,B_272] :
      ( r2_hidden('#skF_4'(C_271,B_272,C_271),B_272)
      | ~ r2_hidden('#skF_3'(C_271,B_272,C_271),C_271)
      | k4_xboole_0(C_271,B_272) = C_271 ) ),
    inference(resolution,[status(thm)],[c_32,c_1294])).

tff(c_4021,plain,(
    ! [C_273,B_274] :
      ( r2_hidden('#skF_4'(C_273,B_274,C_273),B_274)
      | k4_xboole_0(C_273,B_274) = C_273 ) ),
    inference(resolution,[status(thm)],[c_1019,c_4003])).

tff(c_22,plain,(
    ! [D_12,B_8,A_7] :
      ( ~ r2_hidden(D_12,B_8)
      | ~ r2_hidden(D_12,k4_xboole_0(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4356,plain,(
    ! [C_285,A_286,B_287] :
      ( ~ r2_hidden('#skF_4'(C_285,k4_xboole_0(A_286,B_287),C_285),B_287)
      | k4_xboole_0(C_285,k4_xboole_0(A_286,B_287)) = C_285 ) ),
    inference(resolution,[status(thm)],[c_4021,c_22])).

tff(c_4425,plain,(
    ! [C_9,A_286] :
      ( r2_hidden('#skF_3'(C_9,k4_xboole_0(A_286,C_9),C_9),C_9)
      | k4_xboole_0(C_9,k4_xboole_0(A_286,C_9)) = C_9 ) ),
    inference(resolution,[status(thm)],[c_36,c_4356])).

tff(c_5346,plain,(
    ! [C_305,A_306] :
      ( ~ r2_hidden('#skF_3'(C_305,k4_xboole_0(A_306,C_305),C_305),C_305)
      | k4_xboole_0(C_305,k4_xboole_0(A_306,C_305)) = C_305 ) ),
    inference(resolution,[status(thm)],[c_32,c_4356])).

tff(c_5479,plain,(
    ! [C_311,A_312] : k4_xboole_0(C_311,k4_xboole_0(A_312,C_311)) = C_311 ),
    inference(resolution,[status(thm)],[c_4425,c_5346])).

tff(c_595,plain,(
    ! [A_82,B_83,C_84] :
      ( r2_hidden('#skF_3'(A_82,B_83,C_84),A_82)
      | r2_hidden('#skF_4'(A_82,B_83,C_84),C_84)
      | k4_xboole_0(A_82,B_83) = C_84 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_44,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_73,plain,(
    ! [D_23,B_24,A_25] :
      ( ~ r2_hidden(D_23,B_24)
      | ~ r2_hidden(D_23,k4_xboole_0(A_25,B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_76,plain,(
    ! [D_23,A_16] :
      ( ~ r2_hidden(D_23,k1_xboole_0)
      | ~ r2_hidden(D_23,A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_73])).

tff(c_1321,plain,(
    ! [A_130,B_131,A_132] :
      ( ~ r2_hidden('#skF_4'(A_130,B_131,k1_xboole_0),A_132)
      | r2_hidden('#skF_3'(A_130,B_131,k1_xboole_0),A_130)
      | k4_xboole_0(A_130,B_131) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_595,c_76])).

tff(c_1391,plain,(
    ! [A_136,B_137] :
      ( r2_hidden('#skF_3'(A_136,B_137,k1_xboole_0),A_136)
      | k4_xboole_0(A_136,B_137) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_36,c_1321])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1480,plain,(
    ! [A_141,B_142,B_143] :
      ( r2_hidden('#skF_3'(k3_xboole_0(A_141,B_142),B_143,k1_xboole_0),B_142)
      | k4_xboole_0(k3_xboole_0(A_141,B_142),B_143) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1391,c_4])).

tff(c_34,plain,(
    ! [A_7,B_8,C_9] :
      ( ~ r2_hidden('#skF_3'(A_7,B_8,C_9),B_8)
      | r2_hidden('#skF_4'(A_7,B_8,C_9),C_9)
      | k4_xboole_0(A_7,B_8) = C_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1517,plain,(
    ! [A_141,B_142] :
      ( r2_hidden('#skF_4'(k3_xboole_0(A_141,B_142),B_142,k1_xboole_0),k1_xboole_0)
      | k4_xboole_0(k3_xboole_0(A_141,B_142),B_142) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1480,c_34])).

tff(c_1793,plain,(
    ! [A_161,B_162] :
      ( r2_hidden('#skF_4'(k3_xboole_0(A_161,B_162),B_162,k1_xboole_0),k1_xboole_0)
      | k4_xboole_0(k3_xboole_0(A_161,B_162),B_162) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1480,c_34])).

tff(c_2113,plain,(
    ! [A_178,B_179,A_180] :
      ( ~ r2_hidden('#skF_4'(k3_xboole_0(A_178,B_179),B_179,k1_xboole_0),A_180)
      | k4_xboole_0(k3_xboole_0(A_178,B_179),B_179) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1793,c_76])).

tff(c_2144,plain,(
    ! [A_141,B_142] : k4_xboole_0(k3_xboole_0(A_141,B_142),B_142) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1517,c_2113])).

tff(c_2255,plain,(
    ! [A_186,B_187,B_188,C_189] :
      ( r2_hidden('#skF_3'(k3_xboole_0(A_186,B_187),B_188,C_189),B_187)
      | r2_hidden('#skF_4'(k3_xboole_0(A_186,B_187),B_188,C_189),C_189)
      | k4_xboole_0(k3_xboole_0(A_186,B_187),B_188) = C_189 ) ),
    inference(resolution,[status(thm)],[c_595,c_4])).

tff(c_2261,plain,(
    ! [A_186,B_187,C_189] :
      ( r2_hidden('#skF_4'(k3_xboole_0(A_186,B_187),B_187,C_189),C_189)
      | k4_xboole_0(k3_xboole_0(A_186,B_187),B_187) = C_189 ) ),
    inference(resolution,[status(thm)],[c_2255,c_34])).

tff(c_2435,plain,(
    ! [A_192,B_193,C_194] :
      ( r2_hidden('#skF_4'(k3_xboole_0(A_192,B_193),B_193,C_194),C_194)
      | k1_xboole_0 = C_194 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2144,c_2261])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2484,plain,(
    ! [A_192,B_193,A_1,B_2] :
      ( r2_hidden('#skF_4'(k3_xboole_0(A_192,B_193),B_193,k3_xboole_0(A_1,B_2)),A_1)
      | k3_xboole_0(A_1,B_2) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2435,c_6])).

tff(c_4364,plain,(
    ! [A_1,A_286] :
      ( k4_xboole_0(k3_xboole_0(A_1,k4_xboole_0(A_286,A_1)),k4_xboole_0(A_286,A_1)) = k3_xboole_0(A_1,k4_xboole_0(A_286,A_1))
      | k3_xboole_0(A_1,k4_xboole_0(A_286,A_1)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2484,c_4356])).

tff(c_4413,plain,(
    ! [A_1,A_286] :
      ( k3_xboole_0(A_1,k4_xboole_0(A_286,A_1)) = k1_xboole_0
      | k3_xboole_0(A_1,k4_xboole_0(A_286,A_1)) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2144,c_4364])).

tff(c_4622,plain,(
    ! [A_1,A_286] : k3_xboole_0(A_1,k4_xboole_0(A_286,A_1)) = k1_xboole_0 ),
    inference(factorization,[status(thm),theory(equality)],[c_4413])).

tff(c_5491,plain,(
    ! [A_312,C_311] : k3_xboole_0(k4_xboole_0(A_312,C_311),C_311) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5479,c_4622])).

tff(c_63,plain,(
    ! [A_19,B_20] :
      ( r1_xboole_0(A_19,B_20)
      | k3_xboole_0(A_19,B_20) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_46,plain,(
    ~ r1_xboole_0(k4_xboole_0('#skF_5','#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_67,plain,(
    k3_xboole_0(k4_xboole_0('#skF_5','#skF_6'),'#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_63,c_46])).

tff(c_5623,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5491,c_67])).

%------------------------------------------------------------------------------
