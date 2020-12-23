%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:10 EST 2020

% Result     : Theorem 8.92s
% Output     : CNFRefutation 8.92s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 319 expanded)
%              Number of leaves         :   27 ( 119 expanded)
%              Depth                    :   19
%              Number of atoms          :  136 ( 600 expanded)
%              Number of equality atoms :   66 ( 281 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
        | k4_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_52,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_32,plain,(
    ! [C_19] : r2_hidden(C_19,k1_tarski(C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_24,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_81,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k2_xboole_0(A_30,B_31)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_88,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_81])).

tff(c_123,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k4_xboole_0(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_144,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k3_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_123])).

tff(c_149,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_144])).

tff(c_189,plain,(
    ! [A_43,B_44] : k5_xboole_0(A_43,k3_xboole_0(A_43,B_44)) = k4_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_204,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = k4_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_189])).

tff(c_209,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_204])).

tff(c_7743,plain,(
    ! [A_3923,B_3924,C_3925] :
      ( r2_hidden('#skF_1'(A_3923,B_3924,C_3925),A_3923)
      | r2_hidden('#skF_2'(A_3923,B_3924,C_3925),C_3925)
      | k4_xboole_0(A_3923,B_3924) = C_3925 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_7750,plain,(
    ! [A_3923,C_3925] :
      ( r2_hidden('#skF_2'(A_3923,A_3923,C_3925),C_3925)
      | k4_xboole_0(A_3923,A_3923) = C_3925 ) ),
    inference(resolution,[status(thm)],[c_7743,c_16])).

tff(c_7826,plain,(
    ! [A_3952,C_3953] :
      ( r2_hidden('#skF_2'(A_3952,A_3952,C_3953),C_3953)
      | k1_xboole_0 = C_3953 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_7750])).

tff(c_28,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_250,plain,(
    ! [D_50,A_51,B_52] :
      ( r2_hidden(D_50,A_51)
      | ~ r2_hidden(D_50,k4_xboole_0(A_51,B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_253,plain,(
    ! [D_50,A_13,B_14] :
      ( r2_hidden(D_50,A_13)
      | ~ r2_hidden(D_50,k3_xboole_0(A_13,B_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_250])).

tff(c_11644,plain,(
    ! [A_7869,A_7870,B_7871] :
      ( r2_hidden('#skF_2'(A_7869,A_7869,k3_xboole_0(A_7870,B_7871)),A_7870)
      | k3_xboole_0(A_7870,B_7871) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_7826,c_253])).

tff(c_30,plain,(
    ! [C_19,A_15] :
      ( C_19 = A_15
      | ~ r2_hidden(C_19,k1_tarski(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_13157,plain,(
    ! [A_8270,A_8271,B_8272] :
      ( '#skF_2'(A_8270,A_8270,k3_xboole_0(k1_tarski(A_8271),B_8272)) = A_8271
      | k3_xboole_0(k1_tarski(A_8271),B_8272) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_11644,c_30])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_11910,plain,(
    ! [A_7956,A_7957,B_7958] :
      ( ~ r2_hidden('#skF_2'(A_7956,A_7956,k4_xboole_0(A_7957,B_7958)),B_7958)
      | k4_xboole_0(A_7957,B_7958) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_7826,c_4])).

tff(c_11970,plain,(
    ! [A_7956,A_10] :
      ( ~ r2_hidden('#skF_2'(A_7956,A_7956,A_10),k1_xboole_0)
      | k4_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_11910])).

tff(c_11986,plain,(
    ! [A_7956,A_10] :
      ( ~ r2_hidden('#skF_2'(A_7956,A_7956,A_10),k1_xboole_0)
      | k1_xboole_0 = A_10 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_11970])).

tff(c_13167,plain,(
    ! [A_8271,B_8272] :
      ( ~ r2_hidden(A_8271,k1_xboole_0)
      | k3_xboole_0(k1_tarski(A_8271),B_8272) = k1_xboole_0
      | k3_xboole_0(k1_tarski(A_8271),B_8272) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13157,c_11986])).

tff(c_13448,plain,(
    ! [A_8327,B_8328] :
      ( ~ r2_hidden(A_8327,k1_xboole_0)
      | k3_xboole_0(k1_tarski(A_8327),B_8328) = k1_xboole_0 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_13167])).

tff(c_20,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_13481,plain,(
    ! [A_8327,B_8328] :
      ( k5_xboole_0(k1_tarski(A_8327),k1_xboole_0) = k4_xboole_0(k1_tarski(A_8327),B_8328)
      | ~ r2_hidden(A_8327,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13448,c_20])).

tff(c_13556,plain,(
    ! [A_8355,B_8356] :
      ( k4_xboole_0(k1_tarski(A_8355),B_8356) = k1_tarski(A_8355)
      | ~ r2_hidden(A_8355,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_13481])).

tff(c_14128,plain,(
    ! [D_8492,B_8493,A_8494] :
      ( ~ r2_hidden(D_8492,B_8493)
      | ~ r2_hidden(D_8492,k1_tarski(A_8494))
      | ~ r2_hidden(A_8494,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13556,c_4])).

tff(c_14201,plain,(
    ! [C_8521,A_8522] :
      ( ~ r2_hidden(C_8521,k1_tarski(A_8522))
      | ~ r2_hidden(A_8522,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_32,c_14128])).

tff(c_14289,plain,(
    ! [C_19] : ~ r2_hidden(C_19,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32,c_14201])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_7946,plain,(
    ! [A_4008,B_4009] :
      ( r2_hidden('#skF_2'(A_4008,B_4009,A_4008),A_4008)
      | k4_xboole_0(A_4008,B_4009) = A_4008 ) ),
    inference(resolution,[status(thm)],[c_7743,c_14])).

tff(c_26,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_259,plain,(
    ! [D_50,A_11] :
      ( r2_hidden(D_50,A_11)
      | ~ r2_hidden(D_50,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_250])).

tff(c_7985,plain,(
    ! [B_4009,A_11] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_4009,k1_xboole_0),A_11)
      | k4_xboole_0(k1_xboole_0,B_4009) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_7946,c_259])).

tff(c_210,plain,(
    ! [D_45,B_46,A_47] :
      ( ~ r2_hidden(D_45,B_46)
      | ~ r2_hidden(D_45,k4_xboole_0(A_47,B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_222,plain,(
    ! [D_45,A_10] :
      ( ~ r2_hidden(D_45,k1_xboole_0)
      | ~ r2_hidden(D_45,A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_210])).

tff(c_9588,plain,(
    ! [B_7063,A_7064] :
      ( ~ r2_hidden('#skF_2'(k1_xboole_0,B_7063,k1_xboole_0),A_7064)
      | k4_xboole_0(k1_xboole_0,B_7063) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_7946,c_222])).

tff(c_9636,plain,(
    ! [B_4009] : k4_xboole_0(k1_xboole_0,B_4009) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7985,c_9588])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14796,plain,(
    ! [A_8691,B_8692,A_8693,B_8694] :
      ( r2_hidden('#skF_2'(A_8691,B_8692,k4_xboole_0(A_8693,B_8694)),A_8693)
      | r2_hidden('#skF_1'(A_8691,B_8692,k4_xboole_0(A_8693,B_8694)),A_8691)
      | k4_xboole_0(A_8693,B_8694) = k4_xboole_0(A_8691,B_8692) ) ),
    inference(resolution,[status(thm)],[c_7743,c_6])).

tff(c_14900,plain,(
    ! [A_8691,B_8692,B_4009] :
      ( r2_hidden('#skF_2'(A_8691,B_8692,k4_xboole_0(k1_xboole_0,B_4009)),k1_xboole_0)
      | r2_hidden('#skF_1'(A_8691,B_8692,k1_xboole_0),A_8691)
      | k4_xboole_0(k1_xboole_0,B_4009) = k4_xboole_0(A_8691,B_8692) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9636,c_14796])).

tff(c_14970,plain,(
    ! [A_8691,B_8692] :
      ( r2_hidden('#skF_2'(A_8691,B_8692,k1_xboole_0),k1_xboole_0)
      | r2_hidden('#skF_1'(A_8691,B_8692,k1_xboole_0),A_8691)
      | k4_xboole_0(A_8691,B_8692) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9636,c_9636,c_14900])).

tff(c_14984,plain,(
    ! [A_8721,B_8722] :
      ( r2_hidden('#skF_1'(A_8721,B_8722,k1_xboole_0),A_8721)
      | k4_xboole_0(A_8721,B_8722) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_14289,c_14970])).

tff(c_15058,plain,(
    ! [A_8749,B_8750] :
      ( '#skF_1'(k1_tarski(A_8749),B_8750,k1_xboole_0) = A_8749
      | k4_xboole_0(k1_tarski(A_8749),B_8750) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14984,c_30])).

tff(c_15252,plain,(
    '#skF_1'(k1_tarski('#skF_6'),'#skF_7',k1_xboole_0) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_15058,c_52])).

tff(c_15275,plain,
    ( ~ r2_hidden('#skF_6','#skF_7')
    | r2_hidden('#skF_2'(k1_tarski('#skF_6'),'#skF_7',k1_xboole_0),k1_xboole_0)
    | k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_15252,c_16])).

tff(c_15322,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_14289,c_15275])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k4_xboole_0(A_1,B_2))
      | r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_11817,plain,(
    ! [A_7927,A_7928,B_7929] :
      ( r2_hidden('#skF_2'(A_7927,A_7927,k4_xboole_0(A_7928,B_7929)),A_7928)
      | k4_xboole_0(A_7928,B_7929) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_7826,c_6])).

tff(c_13024,plain,(
    ! [A_8241,A_8242,B_8243] :
      ( '#skF_2'(A_8241,A_8241,k4_xboole_0(k1_tarski(A_8242),B_8243)) = A_8242
      | k4_xboole_0(k1_tarski(A_8242),B_8243) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_11817,c_30])).

tff(c_7866,plain,(
    ! [A_3952,A_1,B_2] :
      ( ~ r2_hidden('#skF_2'(A_3952,A_3952,k4_xboole_0(A_1,B_2)),B_2)
      | k4_xboole_0(A_1,B_2) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_7826,c_4])).

tff(c_13037,plain,(
    ! [A_8242,B_8243] :
      ( ~ r2_hidden(A_8242,B_8243)
      | k4_xboole_0(k1_tarski(A_8242),B_8243) = k1_xboole_0
      | k4_xboole_0(k1_tarski(A_8242),B_8243) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13024,c_7866])).

tff(c_18646,plain,(
    ! [A_9598,B_9599] :
      ( ~ r2_hidden(A_9598,B_9599)
      | k4_xboole_0(k1_tarski(A_9598),B_9599) = k1_xboole_0 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_13037])).

tff(c_19296,plain,(
    ! [A_9710,B_9711] :
      ( k3_xboole_0(k1_tarski(A_9710),B_9711) = k1_xboole_0
      | ~ r2_hidden(A_9710,k4_xboole_0(k1_tarski(A_9710),B_9711)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18646,c_28])).

tff(c_19344,plain,(
    ! [D_6,B_2] :
      ( k3_xboole_0(k1_tarski(D_6),B_2) = k1_xboole_0
      | r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k1_tarski(D_6)) ) ),
    inference(resolution,[status(thm)],[c_2,c_19296])).

tff(c_19373,plain,(
    ! [D_9738,B_9739] :
      ( k3_xboole_0(k1_tarski(D_9738),B_9739) = k1_xboole_0
      | r2_hidden(D_9738,B_9739) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_19344])).

tff(c_19455,plain,(
    ! [D_9738,B_9739] :
      ( k5_xboole_0(k1_tarski(D_9738),k1_xboole_0) = k4_xboole_0(k1_tarski(D_9738),B_9739)
      | r2_hidden(D_9738,B_9739) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19373,c_20])).

tff(c_19575,plain,(
    ! [D_9766,B_9767] :
      ( k4_xboole_0(k1_tarski(D_9766),B_9767) = k1_tarski(D_9766)
      | r2_hidden(D_9766,B_9767) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_19455])).

tff(c_50,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') != k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_19708,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_19575,c_50])).

tff(c_19824,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15322,c_19708])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:06:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.92/2.98  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.92/2.99  
% 8.92/2.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.92/2.99  %$ r2_hidden > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4
% 8.92/2.99  
% 8.92/2.99  %Foreground sorts:
% 8.92/2.99  
% 8.92/2.99  
% 8.92/2.99  %Background operators:
% 8.92/2.99  
% 8.92/2.99  
% 8.92/2.99  %Foreground operators:
% 8.92/2.99  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.92/2.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.92/2.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.92/2.99  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.92/2.99  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.92/2.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.92/2.99  tff('#skF_7', type, '#skF_7': $i).
% 8.92/2.99  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.92/2.99  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.92/2.99  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.92/2.99  tff('#skF_6', type, '#skF_6': $i).
% 8.92/2.99  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.92/2.99  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.92/2.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.92/2.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.92/2.99  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.92/2.99  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.92/2.99  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 8.92/2.99  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.92/2.99  
% 8.92/3.01  tff(f_75, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) | (k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 8.92/3.01  tff(f_52, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 8.92/3.01  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 8.92/3.01  tff(f_39, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 8.92/3.01  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 8.92/3.01  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.92/3.01  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.92/3.01  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 8.92/3.01  tff(c_52, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.92/3.01  tff(c_32, plain, (![C_19]: (r2_hidden(C_19, k1_tarski(C_19)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.92/3.01  tff(c_24, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.92/3.01  tff(c_22, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.92/3.01  tff(c_81, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k2_xboole_0(A_30, B_31))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.92/3.01  tff(c_88, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_81])).
% 8.92/3.01  tff(c_123, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k4_xboole_0(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.92/3.01  tff(c_144, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k3_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_123])).
% 8.92/3.01  tff(c_149, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_88, c_144])).
% 8.92/3.01  tff(c_189, plain, (![A_43, B_44]: (k5_xboole_0(A_43, k3_xboole_0(A_43, B_44))=k4_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.92/3.01  tff(c_204, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=k4_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_149, c_189])).
% 8.92/3.01  tff(c_209, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_204])).
% 8.92/3.01  tff(c_7743, plain, (![A_3923, B_3924, C_3925]: (r2_hidden('#skF_1'(A_3923, B_3924, C_3925), A_3923) | r2_hidden('#skF_2'(A_3923, B_3924, C_3925), C_3925) | k4_xboole_0(A_3923, B_3924)=C_3925)), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.92/3.01  tff(c_16, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.92/3.01  tff(c_7750, plain, (![A_3923, C_3925]: (r2_hidden('#skF_2'(A_3923, A_3923, C_3925), C_3925) | k4_xboole_0(A_3923, A_3923)=C_3925)), inference(resolution, [status(thm)], [c_7743, c_16])).
% 8.92/3.01  tff(c_7826, plain, (![A_3952, C_3953]: (r2_hidden('#skF_2'(A_3952, A_3952, C_3953), C_3953) | k1_xboole_0=C_3953)), inference(demodulation, [status(thm), theory('equality')], [c_88, c_7750])).
% 8.92/3.01  tff(c_28, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.92/3.01  tff(c_250, plain, (![D_50, A_51, B_52]: (r2_hidden(D_50, A_51) | ~r2_hidden(D_50, k4_xboole_0(A_51, B_52)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.92/3.01  tff(c_253, plain, (![D_50, A_13, B_14]: (r2_hidden(D_50, A_13) | ~r2_hidden(D_50, k3_xboole_0(A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_250])).
% 8.92/3.01  tff(c_11644, plain, (![A_7869, A_7870, B_7871]: (r2_hidden('#skF_2'(A_7869, A_7869, k3_xboole_0(A_7870, B_7871)), A_7870) | k3_xboole_0(A_7870, B_7871)=k1_xboole_0)), inference(resolution, [status(thm)], [c_7826, c_253])).
% 8.92/3.01  tff(c_30, plain, (![C_19, A_15]: (C_19=A_15 | ~r2_hidden(C_19, k1_tarski(A_15)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.92/3.01  tff(c_13157, plain, (![A_8270, A_8271, B_8272]: ('#skF_2'(A_8270, A_8270, k3_xboole_0(k1_tarski(A_8271), B_8272))=A_8271 | k3_xboole_0(k1_tarski(A_8271), B_8272)=k1_xboole_0)), inference(resolution, [status(thm)], [c_11644, c_30])).
% 8.92/3.01  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.92/3.01  tff(c_11910, plain, (![A_7956, A_7957, B_7958]: (~r2_hidden('#skF_2'(A_7956, A_7956, k4_xboole_0(A_7957, B_7958)), B_7958) | k4_xboole_0(A_7957, B_7958)=k1_xboole_0)), inference(resolution, [status(thm)], [c_7826, c_4])).
% 8.92/3.01  tff(c_11970, plain, (![A_7956, A_10]: (~r2_hidden('#skF_2'(A_7956, A_7956, A_10), k1_xboole_0) | k4_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_11910])).
% 8.92/3.01  tff(c_11986, plain, (![A_7956, A_10]: (~r2_hidden('#skF_2'(A_7956, A_7956, A_10), k1_xboole_0) | k1_xboole_0=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_11970])).
% 8.92/3.01  tff(c_13167, plain, (![A_8271, B_8272]: (~r2_hidden(A_8271, k1_xboole_0) | k3_xboole_0(k1_tarski(A_8271), B_8272)=k1_xboole_0 | k3_xboole_0(k1_tarski(A_8271), B_8272)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_13157, c_11986])).
% 8.92/3.01  tff(c_13448, plain, (![A_8327, B_8328]: (~r2_hidden(A_8327, k1_xboole_0) | k3_xboole_0(k1_tarski(A_8327), B_8328)=k1_xboole_0)), inference(factorization, [status(thm), theory('equality')], [c_13167])).
% 8.92/3.01  tff(c_20, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.92/3.01  tff(c_13481, plain, (![A_8327, B_8328]: (k5_xboole_0(k1_tarski(A_8327), k1_xboole_0)=k4_xboole_0(k1_tarski(A_8327), B_8328) | ~r2_hidden(A_8327, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_13448, c_20])).
% 8.92/3.01  tff(c_13556, plain, (![A_8355, B_8356]: (k4_xboole_0(k1_tarski(A_8355), B_8356)=k1_tarski(A_8355) | ~r2_hidden(A_8355, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_209, c_13481])).
% 8.92/3.01  tff(c_14128, plain, (![D_8492, B_8493, A_8494]: (~r2_hidden(D_8492, B_8493) | ~r2_hidden(D_8492, k1_tarski(A_8494)) | ~r2_hidden(A_8494, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_13556, c_4])).
% 8.92/3.01  tff(c_14201, plain, (![C_8521, A_8522]: (~r2_hidden(C_8521, k1_tarski(A_8522)) | ~r2_hidden(A_8522, k1_xboole_0))), inference(resolution, [status(thm)], [c_32, c_14128])).
% 8.92/3.01  tff(c_14289, plain, (![C_19]: (~r2_hidden(C_19, k1_xboole_0))), inference(resolution, [status(thm)], [c_32, c_14201])).
% 8.92/3.01  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.92/3.01  tff(c_7946, plain, (![A_4008, B_4009]: (r2_hidden('#skF_2'(A_4008, B_4009, A_4008), A_4008) | k4_xboole_0(A_4008, B_4009)=A_4008)), inference(resolution, [status(thm)], [c_7743, c_14])).
% 8.92/3.01  tff(c_26, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k2_xboole_0(A_11, B_12))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.92/3.01  tff(c_259, plain, (![D_50, A_11]: (r2_hidden(D_50, A_11) | ~r2_hidden(D_50, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_250])).
% 8.92/3.01  tff(c_7985, plain, (![B_4009, A_11]: (r2_hidden('#skF_2'(k1_xboole_0, B_4009, k1_xboole_0), A_11) | k4_xboole_0(k1_xboole_0, B_4009)=k1_xboole_0)), inference(resolution, [status(thm)], [c_7946, c_259])).
% 8.92/3.01  tff(c_210, plain, (![D_45, B_46, A_47]: (~r2_hidden(D_45, B_46) | ~r2_hidden(D_45, k4_xboole_0(A_47, B_46)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.92/3.01  tff(c_222, plain, (![D_45, A_10]: (~r2_hidden(D_45, k1_xboole_0) | ~r2_hidden(D_45, A_10))), inference(superposition, [status(thm), theory('equality')], [c_24, c_210])).
% 8.92/3.01  tff(c_9588, plain, (![B_7063, A_7064]: (~r2_hidden('#skF_2'(k1_xboole_0, B_7063, k1_xboole_0), A_7064) | k4_xboole_0(k1_xboole_0, B_7063)=k1_xboole_0)), inference(resolution, [status(thm)], [c_7946, c_222])).
% 8.92/3.01  tff(c_9636, plain, (![B_4009]: (k4_xboole_0(k1_xboole_0, B_4009)=k1_xboole_0)), inference(resolution, [status(thm)], [c_7985, c_9588])).
% 8.92/3.01  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.92/3.01  tff(c_14796, plain, (![A_8691, B_8692, A_8693, B_8694]: (r2_hidden('#skF_2'(A_8691, B_8692, k4_xboole_0(A_8693, B_8694)), A_8693) | r2_hidden('#skF_1'(A_8691, B_8692, k4_xboole_0(A_8693, B_8694)), A_8691) | k4_xboole_0(A_8693, B_8694)=k4_xboole_0(A_8691, B_8692))), inference(resolution, [status(thm)], [c_7743, c_6])).
% 8.92/3.01  tff(c_14900, plain, (![A_8691, B_8692, B_4009]: (r2_hidden('#skF_2'(A_8691, B_8692, k4_xboole_0(k1_xboole_0, B_4009)), k1_xboole_0) | r2_hidden('#skF_1'(A_8691, B_8692, k1_xboole_0), A_8691) | k4_xboole_0(k1_xboole_0, B_4009)=k4_xboole_0(A_8691, B_8692))), inference(superposition, [status(thm), theory('equality')], [c_9636, c_14796])).
% 8.92/3.01  tff(c_14970, plain, (![A_8691, B_8692]: (r2_hidden('#skF_2'(A_8691, B_8692, k1_xboole_0), k1_xboole_0) | r2_hidden('#skF_1'(A_8691, B_8692, k1_xboole_0), A_8691) | k4_xboole_0(A_8691, B_8692)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_9636, c_9636, c_14900])).
% 8.92/3.01  tff(c_14984, plain, (![A_8721, B_8722]: (r2_hidden('#skF_1'(A_8721, B_8722, k1_xboole_0), A_8721) | k4_xboole_0(A_8721, B_8722)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_14289, c_14970])).
% 8.92/3.01  tff(c_15058, plain, (![A_8749, B_8750]: ('#skF_1'(k1_tarski(A_8749), B_8750, k1_xboole_0)=A_8749 | k4_xboole_0(k1_tarski(A_8749), B_8750)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14984, c_30])).
% 8.92/3.01  tff(c_15252, plain, ('#skF_1'(k1_tarski('#skF_6'), '#skF_7', k1_xboole_0)='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_15058, c_52])).
% 8.92/3.01  tff(c_15275, plain, (~r2_hidden('#skF_6', '#skF_7') | r2_hidden('#skF_2'(k1_tarski('#skF_6'), '#skF_7', k1_xboole_0), k1_xboole_0) | k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_15252, c_16])).
% 8.92/3.01  tff(c_15322, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_52, c_14289, c_15275])).
% 8.92/3.01  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k4_xboole_0(A_1, B_2)) | r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.92/3.01  tff(c_11817, plain, (![A_7927, A_7928, B_7929]: (r2_hidden('#skF_2'(A_7927, A_7927, k4_xboole_0(A_7928, B_7929)), A_7928) | k4_xboole_0(A_7928, B_7929)=k1_xboole_0)), inference(resolution, [status(thm)], [c_7826, c_6])).
% 8.92/3.01  tff(c_13024, plain, (![A_8241, A_8242, B_8243]: ('#skF_2'(A_8241, A_8241, k4_xboole_0(k1_tarski(A_8242), B_8243))=A_8242 | k4_xboole_0(k1_tarski(A_8242), B_8243)=k1_xboole_0)), inference(resolution, [status(thm)], [c_11817, c_30])).
% 8.92/3.01  tff(c_7866, plain, (![A_3952, A_1, B_2]: (~r2_hidden('#skF_2'(A_3952, A_3952, k4_xboole_0(A_1, B_2)), B_2) | k4_xboole_0(A_1, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_7826, c_4])).
% 8.92/3.01  tff(c_13037, plain, (![A_8242, B_8243]: (~r2_hidden(A_8242, B_8243) | k4_xboole_0(k1_tarski(A_8242), B_8243)=k1_xboole_0 | k4_xboole_0(k1_tarski(A_8242), B_8243)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_13024, c_7866])).
% 8.92/3.01  tff(c_18646, plain, (![A_9598, B_9599]: (~r2_hidden(A_9598, B_9599) | k4_xboole_0(k1_tarski(A_9598), B_9599)=k1_xboole_0)), inference(factorization, [status(thm), theory('equality')], [c_13037])).
% 8.92/3.01  tff(c_19296, plain, (![A_9710, B_9711]: (k3_xboole_0(k1_tarski(A_9710), B_9711)=k1_xboole_0 | ~r2_hidden(A_9710, k4_xboole_0(k1_tarski(A_9710), B_9711)))), inference(superposition, [status(thm), theory('equality')], [c_18646, c_28])).
% 8.92/3.01  tff(c_19344, plain, (![D_6, B_2]: (k3_xboole_0(k1_tarski(D_6), B_2)=k1_xboole_0 | r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k1_tarski(D_6)))), inference(resolution, [status(thm)], [c_2, c_19296])).
% 8.92/3.01  tff(c_19373, plain, (![D_9738, B_9739]: (k3_xboole_0(k1_tarski(D_9738), B_9739)=k1_xboole_0 | r2_hidden(D_9738, B_9739))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_19344])).
% 8.92/3.01  tff(c_19455, plain, (![D_9738, B_9739]: (k5_xboole_0(k1_tarski(D_9738), k1_xboole_0)=k4_xboole_0(k1_tarski(D_9738), B_9739) | r2_hidden(D_9738, B_9739))), inference(superposition, [status(thm), theory('equality')], [c_19373, c_20])).
% 8.92/3.01  tff(c_19575, plain, (![D_9766, B_9767]: (k4_xboole_0(k1_tarski(D_9766), B_9767)=k1_tarski(D_9766) | r2_hidden(D_9766, B_9767))), inference(demodulation, [status(thm), theory('equality')], [c_209, c_19455])).
% 8.92/3.01  tff(c_50, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')!=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.92/3.01  tff(c_19708, plain, (r2_hidden('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_19575, c_50])).
% 8.92/3.01  tff(c_19824, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15322, c_19708])).
% 8.92/3.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.92/3.01  
% 8.92/3.01  Inference rules
% 8.92/3.01  ----------------------
% 8.92/3.01  #Ref     : 0
% 8.92/3.01  #Sup     : 3410
% 8.92/3.01  #Fact    : 14
% 8.92/3.01  #Define  : 0
% 8.92/3.01  #Split   : 2
% 8.92/3.01  #Chain   : 0
% 8.92/3.01  #Close   : 0
% 8.92/3.01  
% 8.92/3.01  Ordering : KBO
% 8.92/3.01  
% 8.92/3.01  Simplification rules
% 8.92/3.01  ----------------------
% 8.92/3.01  #Subsume      : 1049
% 8.92/3.01  #Demod        : 1656
% 8.92/3.01  #Tautology    : 821
% 8.92/3.01  #SimpNegUnit  : 82
% 8.92/3.01  #BackRed      : 1
% 8.92/3.01  
% 8.92/3.01  #Partial instantiations: 5430
% 8.92/3.01  #Strategies tried      : 1
% 8.92/3.01  
% 8.92/3.01  Timing (in seconds)
% 8.92/3.01  ----------------------
% 8.92/3.01  Preprocessing        : 0.31
% 8.92/3.01  Parsing              : 0.16
% 8.92/3.01  CNF conversion       : 0.02
% 8.92/3.01  Main loop            : 1.84
% 8.92/3.01  Inferencing          : 0.72
% 8.92/3.01  Reduction            : 0.53
% 8.92/3.01  Demodulation         : 0.38
% 8.92/3.01  BG Simplification    : 0.08
% 8.92/3.01  Subsumption          : 0.38
% 8.92/3.01  Abstraction          : 0.12
% 8.92/3.02  MUC search           : 0.00
% 8.92/3.02  Cooper               : 0.00
% 8.92/3.02  Total                : 2.19
% 8.92/3.02  Index Insertion      : 0.00
% 8.92/3.02  Index Deletion       : 0.00
% 8.92/3.02  Index Matching       : 0.00
% 8.92/3.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
