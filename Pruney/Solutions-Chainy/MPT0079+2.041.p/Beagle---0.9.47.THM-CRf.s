%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:48 EST 2020

% Result     : Theorem 11.84s
% Output     : CNFRefutation 12.05s
% Verified   : 
% Statistics : Number of formulae       :  123 (2344 expanded)
%              Number of leaves         :   24 ( 825 expanded)
%              Depth                    :   21
%              Number of atoms          :  116 (2657 expanded)
%              Number of equality atoms :  109 (2366 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_49,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_26,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_165,plain,(
    ! [A_34,B_35] :
      ( k3_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_xboole_0(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_176,plain,(
    k3_xboole_0('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_165])).

tff(c_182,plain,(
    ! [A_36,B_37] : k4_xboole_0(A_36,k3_xboole_0(A_36,B_37)) = k4_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_195,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k4_xboole_0('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_182])).

tff(c_203,plain,(
    k4_xboole_0('#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_195])).

tff(c_16,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_221,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k4_xboole_0(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_234,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,k4_xboole_0(A_15,B_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_221])).

tff(c_271,plain,(
    ! [A_15,B_16] : k3_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,B_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_234])).

tff(c_20,plain,(
    ! [A_17] : k4_xboole_0(k1_xboole_0,A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1059,plain,(
    ! [A_64,B_65,C_66] : k2_xboole_0(k4_xboole_0(A_64,B_65),k3_xboole_0(A_64,C_66)) = k4_xboole_0(A_64,k4_xboole_0(B_65,C_66)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1179,plain,(
    ! [A_5,C_66] : k4_xboole_0(A_5,k4_xboole_0(k1_xboole_0,C_66)) = k2_xboole_0(A_5,k3_xboole_0(A_5,C_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1059])).

tff(c_1204,plain,(
    ! [A_67,C_68] : k2_xboole_0(A_67,k3_xboole_0(A_67,C_68)) = A_67 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_20,c_1179])).

tff(c_1245,plain,(
    ! [A_15,B_16] : k2_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = A_15 ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_1204])).

tff(c_310,plain,(
    ! [A_41,B_42] : k4_xboole_0(k2_xboole_0(A_41,B_42),B_42) = k4_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_320,plain,(
    ! [A_41] : k4_xboole_0(A_41,k1_xboole_0) = k2_xboole_0(A_41,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_8])).

tff(c_341,plain,(
    ! [A_43] : k2_xboole_0(A_43,k1_xboole_0) = A_43 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_320])).

tff(c_14,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_435,plain,(
    ! [A_45] : k4_xboole_0(A_45,A_45) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_14])).

tff(c_440,plain,(
    ! [A_45] : k4_xboole_0(A_45,k1_xboole_0) = k3_xboole_0(A_45,A_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_18])).

tff(c_458,plain,(
    ! [A_45] : k3_xboole_0(A_45,A_45) = A_45 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_440])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16304,plain,(
    ! [A_196,C_197,B_198] : k2_xboole_0(k3_xboole_0(A_196,C_197),k4_xboole_0(A_196,B_198)) = k4_xboole_0(A_196,k4_xboole_0(B_198,C_197)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1059,c_2])).

tff(c_16671,plain,(
    ! [A_45,B_198] : k4_xboole_0(A_45,k4_xboole_0(B_198,A_45)) = k2_xboole_0(A_45,k4_xboole_0(A_45,B_198)) ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_16304])).

tff(c_16841,plain,(
    ! [A_199,B_200] : k4_xboole_0(A_199,k4_xboole_0(B_200,A_199)) = A_199 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1245,c_16671])).

tff(c_17173,plain,(
    k4_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_16841])).

tff(c_370,plain,(
    ! [B_2] : k2_xboole_0(k1_xboole_0,B_2) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_341])).

tff(c_1155,plain,(
    ! [B_65] : k4_xboole_0('#skF_4',k4_xboole_0(B_65,'#skF_2')) = k2_xboole_0(k4_xboole_0('#skF_4',B_65),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_1059])).

tff(c_1197,plain,(
    ! [B_65] : k4_xboole_0('#skF_4',k4_xboole_0(B_65,'#skF_2')) = k4_xboole_0('#skF_4',B_65) ),
    inference(demodulation,[status(thm),theory(equality)],[c_370,c_2,c_1155])).

tff(c_32,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_33,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_32])).

tff(c_326,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_2') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_310])).

tff(c_1699,plain,(
    ! [B_76] : k4_xboole_0('#skF_4',k4_xboole_0(B_76,'#skF_2')) = k4_xboole_0('#skF_4',B_76) ),
    inference(demodulation,[status(thm),theory(equality)],[c_370,c_2,c_1155])).

tff(c_1750,plain,(
    k4_xboole_0('#skF_4',k4_xboole_0('#skF_1','#skF_2')) = k4_xboole_0('#skF_4',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_1699])).

tff(c_1779,plain,(
    k4_xboole_0('#skF_4','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1197,c_14,c_1750])).

tff(c_30,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_177,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_165])).

tff(c_1149,plain,(
    ! [B_65] : k4_xboole_0('#skF_3',k4_xboole_0(B_65,'#skF_1')) = k2_xboole_0(k4_xboole_0('#skF_3',B_65),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_1059])).

tff(c_2098,plain,(
    ! [B_81] : k4_xboole_0('#skF_3',k4_xboole_0(B_81,'#skF_1')) = k4_xboole_0('#skF_3',B_81) ),
    inference(demodulation,[status(thm),theory(equality)],[c_370,c_2,c_1149])).

tff(c_2129,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1779,c_2098])).

tff(c_2177,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2129])).

tff(c_329,plain,(
    ! [B_2,A_1] : k4_xboole_0(k2_xboole_0(B_2,A_1),B_2) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_310])).

tff(c_208,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_16])).

tff(c_211,plain,(
    k4_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_208])).

tff(c_17170,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_16841])).

tff(c_258,plain,(
    ! [A_11,B_12] : k3_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_221])).

tff(c_279,plain,(
    ! [A_11,B_12] : k3_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_258])).

tff(c_1264,plain,(
    ! [A_11] : k2_xboole_0(A_11,A_11) = A_11 ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_1204])).

tff(c_22,plain,(
    ! [A_18,B_19,C_20] : k2_xboole_0(k2_xboole_0(A_18,B_19),C_20) = k2_xboole_0(A_18,k2_xboole_0(B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_756,plain,(
    ! [A_55,B_56,C_57] : k2_xboole_0(k2_xboole_0(A_55,B_56),C_57) = k2_xboole_0(A_55,k2_xboole_0(B_56,C_57)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_806,plain,(
    ! [C_57] : k2_xboole_0(k2_xboole_0('#skF_4','#skF_3'),C_57) = k2_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_57)) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_756])).

tff(c_11208,plain,(
    ! [C_165] : k2_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_165)) = k2_xboole_0('#skF_4',k2_xboole_0('#skF_3',C_165)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_806])).

tff(c_11349,plain,(
    k2_xboole_0('#skF_4',k2_xboole_0('#skF_3','#skF_2')) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1264,c_11208])).

tff(c_11391,plain,(
    k2_xboole_0('#skF_4',k2_xboole_0('#skF_3','#skF_2')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_11349])).

tff(c_11594,plain,(
    k4_xboole_0(k2_xboole_0('#skF_3','#skF_2'),'#skF_4') = k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_11391,c_329])).

tff(c_11633,plain,(
    k4_xboole_0(k2_xboole_0('#skF_3','#skF_2'),'#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2177,c_329,c_11594])).

tff(c_11668,plain,(
    k4_xboole_0(k2_xboole_0('#skF_3','#skF_2'),'#skF_4') = k3_xboole_0(k2_xboole_0('#skF_3','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_11633,c_271])).

tff(c_11680,plain,(
    k3_xboole_0(k2_xboole_0('#skF_3','#skF_2'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11633,c_11668])).

tff(c_359,plain,(
    ! [A_43] : k4_xboole_0(A_43,A_43) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_14])).

tff(c_338,plain,(
    ! [A_41] : k2_xboole_0(A_41,k1_xboole_0) = A_41 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_320])).

tff(c_75,plain,(
    ! [B_28,A_29] : k2_xboole_0(B_28,A_29) = k2_xboole_0(A_29,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_121,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k2_xboole_0(B_31,A_30)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_14])).

tff(c_134,plain,(
    k4_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_121])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10] : k4_xboole_0(k4_xboole_0(A_8,B_9),C_10) = k4_xboole_0(A_8,k2_xboole_0(B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_466,plain,(
    ! [A_46,B_47,C_48] : k4_xboole_0(k4_xboole_0(A_46,B_47),C_48) = k4_xboole_0(A_46,k2_xboole_0(B_47,C_48)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_483,plain,(
    ! [A_46,B_47,B_16] : k4_xboole_0(A_46,k2_xboole_0(B_47,k4_xboole_0(k4_xboole_0(A_46,B_47),B_16))) = k3_xboole_0(k4_xboole_0(A_46,B_47),B_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_466,c_18])).

tff(c_26621,plain,(
    ! [A_252,B_253,B_254] : k4_xboole_0(A_252,k2_xboole_0(B_253,k4_xboole_0(A_252,k2_xboole_0(B_253,B_254)))) = k3_xboole_0(k4_xboole_0(A_252,B_253),B_254) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_483])).

tff(c_27086,plain,(
    k4_xboole_0('#skF_2',k2_xboole_0('#skF_4',k1_xboole_0)) = k3_xboole_0(k4_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_26621])).

tff(c_27196,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17173,c_17173,c_338,c_27086])).

tff(c_27256,plain,(
    k4_xboole_0('#skF_2','#skF_2') = k4_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_27196,c_16])).

tff(c_27277,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_27256])).

tff(c_316,plain,(
    ! [A_41,B_42] : k4_xboole_0(k2_xboole_0(A_41,B_42),k4_xboole_0(A_41,B_42)) = k3_xboole_0(k2_xboole_0(A_41,B_42),B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_18])).

tff(c_27381,plain,(
    k4_xboole_0(k2_xboole_0('#skF_2','#skF_3'),k1_xboole_0) = k3_xboole_0(k2_xboole_0('#skF_2','#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_27277,c_316])).

tff(c_27432,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11680,c_2,c_2,c_8,c_27381])).

tff(c_1195,plain,(
    ! [B_65] : k4_xboole_0('#skF_3',k4_xboole_0(B_65,'#skF_1')) = k4_xboole_0('#skF_3',B_65) ),
    inference(demodulation,[status(thm),theory(equality)],[c_370,c_2,c_1149])).

tff(c_90,plain,(
    ! [A_29,B_28] : k4_xboole_0(A_29,k2_xboole_0(B_28,A_29)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_14])).

tff(c_996,plain,(
    ! [B_62,A_63] : k4_xboole_0(k2_xboole_0(B_62,A_63),B_62) = k4_xboole_0(A_63,B_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_310])).

tff(c_1035,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_1') = k4_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_996])).

tff(c_2140,plain,(
    k4_xboole_0('#skF_3',k4_xboole_0('#skF_2','#skF_1')) = k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1035,c_2098])).

tff(c_2180,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1195,c_90,c_2140])).

tff(c_2190,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k4_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2180,c_1197])).

tff(c_2211,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2190])).

tff(c_10,plain,(
    ! [A_6,B_7] : k4_xboole_0(k2_xboole_0(A_6,B_7),B_7) = k4_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2911,plain,(
    ! [C_91,A_92,B_93] : k2_xboole_0(C_91,k2_xboole_0(A_92,B_93)) = k2_xboole_0(A_92,k2_xboole_0(B_93,C_91)) ),
    inference(superposition,[status(thm),theory(equality)],[c_756,c_2])).

tff(c_3098,plain,(
    ! [A_11,C_91] : k2_xboole_0(A_11,k2_xboole_0(A_11,C_91)) = k2_xboole_0(C_91,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_1264,c_2911])).

tff(c_27807,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k2_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_27432,c_3098])).

tff(c_27881,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1264,c_27807])).

tff(c_518,plain,(
    ! [A_6,B_7,C_48] : k4_xboole_0(k2_xboole_0(A_6,B_7),k2_xboole_0(B_7,C_48)) = k4_xboole_0(k4_xboole_0(A_6,B_7),C_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_466])).

tff(c_22355,plain,(
    ! [A_229,B_230,C_231] : k4_xboole_0(k2_xboole_0(A_229,B_230),k2_xboole_0(B_230,C_231)) = k4_xboole_0(A_229,k2_xboole_0(B_230,C_231)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_518])).

tff(c_22652,plain,(
    ! [C_231] : k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),k2_xboole_0('#skF_2',C_231)) = k4_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_231)) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_22355])).

tff(c_28870,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_3') = k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_27881,c_22652])).

tff(c_28978,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17170,c_27432,c_2211,c_10,c_2,c_28870])).

tff(c_29060,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_4') = k4_xboole_0('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28978,c_28978,c_1035])).

tff(c_29113,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17173,c_2177,c_329,c_29060])).

tff(c_29115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_29113])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:36:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.84/4.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.84/4.91  
% 11.84/4.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.84/4.91  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.84/4.91  
% 11.84/4.91  %Foreground sorts:
% 11.84/4.91  
% 11.84/4.91  
% 11.84/4.91  %Background operators:
% 11.84/4.91  
% 11.84/4.91  
% 11.84/4.91  %Foreground operators:
% 11.84/4.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.84/4.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.84/4.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.84/4.91  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.84/4.91  tff('#skF_2', type, '#skF_2': $i).
% 11.84/4.91  tff('#skF_3', type, '#skF_3': $i).
% 11.84/4.91  tff('#skF_1', type, '#skF_1': $i).
% 11.84/4.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.84/4.91  tff('#skF_4', type, '#skF_4': $i).
% 11.84/4.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.84/4.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.84/4.91  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.84/4.91  
% 12.05/4.94  tff(f_58, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 12.05/4.94  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 12.05/4.94  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 12.05/4.94  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 12.05/4.94  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 12.05/4.94  tff(f_45, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 12.05/4.94  tff(f_49, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 12.05/4.94  tff(f_35, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 12.05/4.94  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 12.05/4.94  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 12.05/4.94  tff(f_47, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 12.05/4.94  tff(f_37, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 12.05/4.94  tff(c_26, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_58])).
% 12.05/4.94  tff(c_8, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.05/4.94  tff(c_28, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 12.05/4.94  tff(c_165, plain, (![A_34, B_35]: (k3_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.05/4.94  tff(c_176, plain, (k3_xboole_0('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_165])).
% 12.05/4.94  tff(c_182, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k3_xboole_0(A_36, B_37))=k4_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.05/4.94  tff(c_195, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k4_xboole_0('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_176, c_182])).
% 12.05/4.94  tff(c_203, plain, (k4_xboole_0('#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_195])).
% 12.05/4.94  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.05/4.94  tff(c_18, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.05/4.94  tff(c_221, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k4_xboole_0(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.05/4.94  tff(c_234, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k3_xboole_0(A_15, k4_xboole_0(A_15, B_16)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_221])).
% 12.05/4.94  tff(c_271, plain, (![A_15, B_16]: (k3_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k4_xboole_0(A_15, B_16))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_234])).
% 12.05/4.94  tff(c_20, plain, (![A_17]: (k4_xboole_0(k1_xboole_0, A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.05/4.94  tff(c_1059, plain, (![A_64, B_65, C_66]: (k2_xboole_0(k4_xboole_0(A_64, B_65), k3_xboole_0(A_64, C_66))=k4_xboole_0(A_64, k4_xboole_0(B_65, C_66)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.05/4.94  tff(c_1179, plain, (![A_5, C_66]: (k4_xboole_0(A_5, k4_xboole_0(k1_xboole_0, C_66))=k2_xboole_0(A_5, k3_xboole_0(A_5, C_66)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1059])).
% 12.05/4.94  tff(c_1204, plain, (![A_67, C_68]: (k2_xboole_0(A_67, k3_xboole_0(A_67, C_68))=A_67)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_20, c_1179])).
% 12.05/4.94  tff(c_1245, plain, (![A_15, B_16]: (k2_xboole_0(A_15, k4_xboole_0(A_15, B_16))=A_15)), inference(superposition, [status(thm), theory('equality')], [c_271, c_1204])).
% 12.05/4.94  tff(c_310, plain, (![A_41, B_42]: (k4_xboole_0(k2_xboole_0(A_41, B_42), B_42)=k4_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.05/4.94  tff(c_320, plain, (![A_41]: (k4_xboole_0(A_41, k1_xboole_0)=k2_xboole_0(A_41, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_310, c_8])).
% 12.05/4.94  tff(c_341, plain, (![A_43]: (k2_xboole_0(A_43, k1_xboole_0)=A_43)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_320])).
% 12.05/4.94  tff(c_14, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k2_xboole_0(A_11, B_12))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.05/4.94  tff(c_435, plain, (![A_45]: (k4_xboole_0(A_45, A_45)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_341, c_14])).
% 12.05/4.94  tff(c_440, plain, (![A_45]: (k4_xboole_0(A_45, k1_xboole_0)=k3_xboole_0(A_45, A_45))), inference(superposition, [status(thm), theory('equality')], [c_435, c_18])).
% 12.05/4.94  tff(c_458, plain, (![A_45]: (k3_xboole_0(A_45, A_45)=A_45)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_440])).
% 12.05/4.94  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.05/4.94  tff(c_16304, plain, (![A_196, C_197, B_198]: (k2_xboole_0(k3_xboole_0(A_196, C_197), k4_xboole_0(A_196, B_198))=k4_xboole_0(A_196, k4_xboole_0(B_198, C_197)))), inference(superposition, [status(thm), theory('equality')], [c_1059, c_2])).
% 12.05/4.94  tff(c_16671, plain, (![A_45, B_198]: (k4_xboole_0(A_45, k4_xboole_0(B_198, A_45))=k2_xboole_0(A_45, k4_xboole_0(A_45, B_198)))), inference(superposition, [status(thm), theory('equality')], [c_458, c_16304])).
% 12.05/4.94  tff(c_16841, plain, (![A_199, B_200]: (k4_xboole_0(A_199, k4_xboole_0(B_200, A_199))=A_199)), inference(demodulation, [status(thm), theory('equality')], [c_1245, c_16671])).
% 12.05/4.94  tff(c_17173, plain, (k4_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_203, c_16841])).
% 12.05/4.94  tff(c_370, plain, (![B_2]: (k2_xboole_0(k1_xboole_0, B_2)=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_341])).
% 12.05/4.94  tff(c_1155, plain, (![B_65]: (k4_xboole_0('#skF_4', k4_xboole_0(B_65, '#skF_2'))=k2_xboole_0(k4_xboole_0('#skF_4', B_65), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_176, c_1059])).
% 12.05/4.94  tff(c_1197, plain, (![B_65]: (k4_xboole_0('#skF_4', k4_xboole_0(B_65, '#skF_2'))=k4_xboole_0('#skF_4', B_65))), inference(demodulation, [status(thm), theory('equality')], [c_370, c_2, c_1155])).
% 12.05/4.94  tff(c_32, plain, (k2_xboole_0('#skF_3', '#skF_4')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 12.05/4.94  tff(c_33, plain, (k2_xboole_0('#skF_1', '#skF_2')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_32])).
% 12.05/4.94  tff(c_326, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_2')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_33, c_310])).
% 12.05/4.94  tff(c_1699, plain, (![B_76]: (k4_xboole_0('#skF_4', k4_xboole_0(B_76, '#skF_2'))=k4_xboole_0('#skF_4', B_76))), inference(demodulation, [status(thm), theory('equality')], [c_370, c_2, c_1155])).
% 12.05/4.94  tff(c_1750, plain, (k4_xboole_0('#skF_4', k4_xboole_0('#skF_1', '#skF_2'))=k4_xboole_0('#skF_4', k2_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_326, c_1699])).
% 12.05/4.94  tff(c_1779, plain, (k4_xboole_0('#skF_4', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1197, c_14, c_1750])).
% 12.05/4.94  tff(c_30, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 12.05/4.94  tff(c_177, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_165])).
% 12.05/4.94  tff(c_1149, plain, (![B_65]: (k4_xboole_0('#skF_3', k4_xboole_0(B_65, '#skF_1'))=k2_xboole_0(k4_xboole_0('#skF_3', B_65), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_177, c_1059])).
% 12.05/4.94  tff(c_2098, plain, (![B_81]: (k4_xboole_0('#skF_3', k4_xboole_0(B_81, '#skF_1'))=k4_xboole_0('#skF_3', B_81))), inference(demodulation, [status(thm), theory('equality')], [c_370, c_2, c_1149])).
% 12.05/4.94  tff(c_2129, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1779, c_2098])).
% 12.05/4.94  tff(c_2177, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2129])).
% 12.05/4.94  tff(c_329, plain, (![B_2, A_1]: (k4_xboole_0(k2_xboole_0(B_2, A_1), B_2)=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_310])).
% 12.05/4.94  tff(c_208, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_177, c_16])).
% 12.05/4.94  tff(c_211, plain, (k4_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_208])).
% 12.05/4.94  tff(c_17170, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_211, c_16841])).
% 12.05/4.94  tff(c_258, plain, (![A_11, B_12]: (k3_xboole_0(A_11, k2_xboole_0(A_11, B_12))=k4_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_221])).
% 12.05/4.94  tff(c_279, plain, (![A_11, B_12]: (k3_xboole_0(A_11, k2_xboole_0(A_11, B_12))=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_258])).
% 12.05/4.94  tff(c_1264, plain, (![A_11]: (k2_xboole_0(A_11, A_11)=A_11)), inference(superposition, [status(thm), theory('equality')], [c_279, c_1204])).
% 12.05/4.94  tff(c_22, plain, (![A_18, B_19, C_20]: (k2_xboole_0(k2_xboole_0(A_18, B_19), C_20)=k2_xboole_0(A_18, k2_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.05/4.94  tff(c_756, plain, (![A_55, B_56, C_57]: (k2_xboole_0(k2_xboole_0(A_55, B_56), C_57)=k2_xboole_0(A_55, k2_xboole_0(B_56, C_57)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.05/4.94  tff(c_806, plain, (![C_57]: (k2_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), C_57)=k2_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_57)))), inference(superposition, [status(thm), theory('equality')], [c_33, c_756])).
% 12.05/4.94  tff(c_11208, plain, (![C_165]: (k2_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_165))=k2_xboole_0('#skF_4', k2_xboole_0('#skF_3', C_165)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_806])).
% 12.05/4.94  tff(c_11349, plain, (k2_xboole_0('#skF_4', k2_xboole_0('#skF_3', '#skF_2'))=k2_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1264, c_11208])).
% 12.05/4.94  tff(c_11391, plain, (k2_xboole_0('#skF_4', k2_xboole_0('#skF_3', '#skF_2'))=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_33, c_11349])).
% 12.05/4.94  tff(c_11594, plain, (k4_xboole_0(k2_xboole_0('#skF_3', '#skF_2'), '#skF_4')=k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_11391, c_329])).
% 12.05/4.94  tff(c_11633, plain, (k4_xboole_0(k2_xboole_0('#skF_3', '#skF_2'), '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2177, c_329, c_11594])).
% 12.05/4.94  tff(c_11668, plain, (k4_xboole_0(k2_xboole_0('#skF_3', '#skF_2'), '#skF_4')=k3_xboole_0(k2_xboole_0('#skF_3', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_11633, c_271])).
% 12.05/4.94  tff(c_11680, plain, (k3_xboole_0(k2_xboole_0('#skF_3', '#skF_2'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11633, c_11668])).
% 12.05/4.94  tff(c_359, plain, (![A_43]: (k4_xboole_0(A_43, A_43)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_341, c_14])).
% 12.05/4.94  tff(c_338, plain, (![A_41]: (k2_xboole_0(A_41, k1_xboole_0)=A_41)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_320])).
% 12.05/4.94  tff(c_75, plain, (![B_28, A_29]: (k2_xboole_0(B_28, A_29)=k2_xboole_0(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.05/4.94  tff(c_121, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k2_xboole_0(B_31, A_30))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_75, c_14])).
% 12.05/4.94  tff(c_134, plain, (k4_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_33, c_121])).
% 12.05/4.94  tff(c_12, plain, (![A_8, B_9, C_10]: (k4_xboole_0(k4_xboole_0(A_8, B_9), C_10)=k4_xboole_0(A_8, k2_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.05/4.94  tff(c_466, plain, (![A_46, B_47, C_48]: (k4_xboole_0(k4_xboole_0(A_46, B_47), C_48)=k4_xboole_0(A_46, k2_xboole_0(B_47, C_48)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.05/4.94  tff(c_483, plain, (![A_46, B_47, B_16]: (k4_xboole_0(A_46, k2_xboole_0(B_47, k4_xboole_0(k4_xboole_0(A_46, B_47), B_16)))=k3_xboole_0(k4_xboole_0(A_46, B_47), B_16))), inference(superposition, [status(thm), theory('equality')], [c_466, c_18])).
% 12.05/4.94  tff(c_26621, plain, (![A_252, B_253, B_254]: (k4_xboole_0(A_252, k2_xboole_0(B_253, k4_xboole_0(A_252, k2_xboole_0(B_253, B_254))))=k3_xboole_0(k4_xboole_0(A_252, B_253), B_254))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_483])).
% 12.05/4.94  tff(c_27086, plain, (k4_xboole_0('#skF_2', k2_xboole_0('#skF_4', k1_xboole_0))=k3_xboole_0(k4_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_134, c_26621])).
% 12.05/4.94  tff(c_27196, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_17173, c_17173, c_338, c_27086])).
% 12.05/4.94  tff(c_27256, plain, (k4_xboole_0('#skF_2', '#skF_2')=k4_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_27196, c_16])).
% 12.05/4.94  tff(c_27277, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_359, c_27256])).
% 12.05/4.94  tff(c_316, plain, (![A_41, B_42]: (k4_xboole_0(k2_xboole_0(A_41, B_42), k4_xboole_0(A_41, B_42))=k3_xboole_0(k2_xboole_0(A_41, B_42), B_42))), inference(superposition, [status(thm), theory('equality')], [c_310, c_18])).
% 12.05/4.94  tff(c_27381, plain, (k4_xboole_0(k2_xboole_0('#skF_2', '#skF_3'), k1_xboole_0)=k3_xboole_0(k2_xboole_0('#skF_2', '#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_27277, c_316])).
% 12.05/4.94  tff(c_27432, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11680, c_2, c_2, c_8, c_27381])).
% 12.05/4.94  tff(c_1195, plain, (![B_65]: (k4_xboole_0('#skF_3', k4_xboole_0(B_65, '#skF_1'))=k4_xboole_0('#skF_3', B_65))), inference(demodulation, [status(thm), theory('equality')], [c_370, c_2, c_1149])).
% 12.05/4.94  tff(c_90, plain, (![A_29, B_28]: (k4_xboole_0(A_29, k2_xboole_0(B_28, A_29))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_75, c_14])).
% 12.05/4.94  tff(c_996, plain, (![B_62, A_63]: (k4_xboole_0(k2_xboole_0(B_62, A_63), B_62)=k4_xboole_0(A_63, B_62))), inference(superposition, [status(thm), theory('equality')], [c_2, c_310])).
% 12.05/4.94  tff(c_1035, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_1')=k4_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_33, c_996])).
% 12.05/4.94  tff(c_2140, plain, (k4_xboole_0('#skF_3', k4_xboole_0('#skF_2', '#skF_1'))=k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1035, c_2098])).
% 12.05/4.94  tff(c_2180, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1195, c_90, c_2140])).
% 12.05/4.94  tff(c_2190, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k4_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2180, c_1197])).
% 12.05/4.94  tff(c_2211, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2190])).
% 12.05/4.94  tff(c_10, plain, (![A_6, B_7]: (k4_xboole_0(k2_xboole_0(A_6, B_7), B_7)=k4_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.05/4.94  tff(c_2911, plain, (![C_91, A_92, B_93]: (k2_xboole_0(C_91, k2_xboole_0(A_92, B_93))=k2_xboole_0(A_92, k2_xboole_0(B_93, C_91)))), inference(superposition, [status(thm), theory('equality')], [c_756, c_2])).
% 12.05/4.94  tff(c_3098, plain, (![A_11, C_91]: (k2_xboole_0(A_11, k2_xboole_0(A_11, C_91))=k2_xboole_0(C_91, A_11))), inference(superposition, [status(thm), theory('equality')], [c_1264, c_2911])).
% 12.05/4.94  tff(c_27807, plain, (k2_xboole_0('#skF_2', '#skF_3')=k2_xboole_0('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_27432, c_3098])).
% 12.05/4.94  tff(c_27881, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1264, c_27807])).
% 12.05/4.94  tff(c_518, plain, (![A_6, B_7, C_48]: (k4_xboole_0(k2_xboole_0(A_6, B_7), k2_xboole_0(B_7, C_48))=k4_xboole_0(k4_xboole_0(A_6, B_7), C_48))), inference(superposition, [status(thm), theory('equality')], [c_10, c_466])).
% 12.05/4.94  tff(c_22355, plain, (![A_229, B_230, C_231]: (k4_xboole_0(k2_xboole_0(A_229, B_230), k2_xboole_0(B_230, C_231))=k4_xboole_0(A_229, k2_xboole_0(B_230, C_231)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_518])).
% 12.05/4.94  tff(c_22652, plain, (![C_231]: (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), k2_xboole_0('#skF_2', C_231))=k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_231)))), inference(superposition, [status(thm), theory('equality')], [c_33, c_22355])).
% 12.05/4.94  tff(c_28870, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_3')=k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_27881, c_22652])).
% 12.05/4.94  tff(c_28978, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_17170, c_27432, c_2211, c_10, c_2, c_28870])).
% 12.05/4.94  tff(c_29060, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_4')=k4_xboole_0('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28978, c_28978, c_1035])).
% 12.05/4.94  tff(c_29113, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_17173, c_2177, c_329, c_29060])).
% 12.05/4.94  tff(c_29115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_29113])).
% 12.05/4.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.05/4.94  
% 12.05/4.94  Inference rules
% 12.05/4.94  ----------------------
% 12.05/4.94  #Ref     : 0
% 12.05/4.94  #Sup     : 7334
% 12.05/4.94  #Fact    : 0
% 12.05/4.94  #Define  : 0
% 12.05/4.94  #Split   : 0
% 12.05/4.94  #Chain   : 0
% 12.05/4.94  #Close   : 0
% 12.05/4.94  
% 12.05/4.94  Ordering : KBO
% 12.05/4.94  
% 12.05/4.94  Simplification rules
% 12.05/4.94  ----------------------
% 12.05/4.94  #Subsume      : 36
% 12.05/4.94  #Demod        : 8259
% 12.05/4.94  #Tautology    : 4907
% 12.05/4.94  #SimpNegUnit  : 1
% 12.05/4.94  #BackRed      : 71
% 12.05/4.94  
% 12.05/4.94  #Partial instantiations: 0
% 12.05/4.94  #Strategies tried      : 1
% 12.05/4.94  
% 12.05/4.94  Timing (in seconds)
% 12.05/4.94  ----------------------
% 12.05/4.94  Preprocessing        : 0.32
% 12.05/4.94  Parsing              : 0.18
% 12.05/4.94  CNF conversion       : 0.02
% 12.05/4.94  Main loop            : 3.75
% 12.05/4.94  Inferencing          : 0.65
% 12.05/4.94  Reduction            : 2.30
% 12.05/4.94  Demodulation         : 2.08
% 12.05/4.94  BG Simplification    : 0.08
% 12.05/4.94  Subsumption          : 0.56
% 12.05/4.94  Abstraction          : 0.13
% 12.05/4.94  MUC search           : 0.00
% 12.05/4.94  Cooper               : 0.00
% 12.05/4.94  Total                : 4.11
% 12.05/4.94  Index Insertion      : 0.00
% 12.05/4.94  Index Deletion       : 0.00
% 12.05/4.94  Index Matching       : 0.00
% 12.05/4.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
