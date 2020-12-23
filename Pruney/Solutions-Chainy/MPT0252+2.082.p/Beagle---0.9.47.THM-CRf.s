%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:11 EST 2020

% Result     : Theorem 16.47s
% Output     : CNFRefutation 16.69s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 202 expanded)
%              Number of leaves         :   36 (  84 expanded)
%              Depth                    :   16
%              Number of atoms          :   93 ( 224 expanded)
%              Number of equality atoms :   42 ( 127 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C] : k3_enumset1(A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_69,axiom,(
    ! [A] : k3_enumset1(A,A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C,D,E,F] : k6_enumset1(A,A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

tff(f_67,axiom,(
    ! [A,B,C,D] : k5_enumset1(A,A,A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,D,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_enumset1)).

tff(f_71,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_56,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_18,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_156,plain,(
    ! [B_98,C_99,A_100] :
      ( r2_hidden(B_98,C_99)
      | ~ r1_tarski(k2_tarski(A_100,B_98),C_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_166,plain,(
    ! [B_98,A_100] : r2_hidden(B_98,k2_tarski(A_100,B_98)) ),
    inference(resolution,[status(thm)],[c_6,c_156])).

tff(c_138,plain,(
    ! [A_90,C_91,B_92] :
      ( r2_hidden(A_90,C_91)
      | ~ r1_tarski(k2_tarski(A_90,B_92),C_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_148,plain,(
    ! [A_90,B_92] : r2_hidden(A_90,k2_tarski(A_90,B_92)) ),
    inference(resolution,[status(thm)],[c_6,c_138])).

tff(c_32,plain,(
    ! [A_38,B_39] : k1_enumset1(A_38,A_38,B_39) = k2_tarski(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_38,plain,(
    ! [A_52,B_53,C_54] : k3_enumset1(A_52,A_52,A_52,B_53,C_54) = k1_enumset1(A_52,B_53,C_54) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_34,plain,(
    ! [E_44,C_42,A_40,D_43,B_41] : k4_enumset1(A_40,A_40,B_41,C_42,D_43,E_44) = k3_enumset1(A_40,B_41,C_42,D_43,E_44) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_44,plain,(
    ! [A_65] : k3_enumset1(A_65,A_65,A_65,A_65,A_65) = k1_tarski(A_65) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1151,plain,(
    ! [D_173,G_171,E_175,A_172,F_176,C_174,B_170] : k6_enumset1(A_172,A_172,B_170,C_174,D_173,E_175,F_176,G_171) = k5_enumset1(A_172,B_170,C_174,D_173,E_175,F_176,G_171) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_40,plain,(
    ! [B_56,E_59,C_57,A_55,F_60,D_58] : k6_enumset1(A_55,A_55,A_55,B_56,C_57,D_58,E_59,F_60) = k4_enumset1(A_55,B_56,C_57,D_58,E_59,F_60) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1158,plain,(
    ! [D_173,G_171,E_175,F_176,C_174,B_170] : k5_enumset1(B_170,B_170,C_174,D_173,E_175,F_176,G_171) = k4_enumset1(B_170,C_174,D_173,E_175,F_176,G_171) ),
    inference(superposition,[status(thm),theory(equality)],[c_1151,c_40])).

tff(c_1387,plain,(
    ! [E_184,C_181,G_183,B_185,A_187,D_186,F_182] : k2_xboole_0(k4_enumset1(A_187,B_185,C_181,D_186,E_184,F_182),k1_tarski(G_183)) = k5_enumset1(A_187,B_185,C_181,D_186,E_184,F_182,G_183) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1408,plain,(
    ! [E_44,C_42,G_183,A_40,D_43,B_41] : k5_enumset1(A_40,A_40,B_41,C_42,D_43,E_44,G_183) = k2_xboole_0(k3_enumset1(A_40,B_41,C_42,D_43,E_44),k1_tarski(G_183)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1387])).

tff(c_22602,plain,(
    ! [C_402,B_403,G_401,E_398,A_399,D_400] : k2_xboole_0(k3_enumset1(A_399,B_403,C_402,D_400,E_398),k1_tarski(G_401)) = k4_enumset1(A_399,B_403,C_402,D_400,E_398,G_401) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1158,c_1408])).

tff(c_22668,plain,(
    ! [A_65,G_401] : k4_enumset1(A_65,A_65,A_65,A_65,A_65,G_401) = k2_xboole_0(k1_tarski(A_65),k1_tarski(G_401)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_22602])).

tff(c_42,plain,(
    ! [A_61,B_62,C_63,D_64] : k5_enumset1(A_61,A_61,A_61,A_61,B_62,C_63,D_64) = k2_enumset1(A_61,B_62,C_63,D_64) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_16708,plain,(
    ! [F_337,B_339,D_338,E_341,C_340,G_336] : k5_enumset1(B_339,B_339,C_340,D_338,E_341,F_337,G_336) = k4_enumset1(B_339,C_340,D_338,E_341,F_337,G_336) ),
    inference(superposition,[status(thm),theory(equality)],[c_1151,c_40])).

tff(c_40751,plain,(
    ! [A_567,B_568,C_569,D_570] : k4_enumset1(A_567,A_567,A_567,B_568,C_569,D_570) = k2_enumset1(A_567,B_568,C_569,D_570) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_16708])).

tff(c_40918,plain,(
    ! [C_572,D_573] : k2_xboole_0(k1_tarski(C_572),k1_tarski(D_573)) = k2_enumset1(C_572,C_572,C_572,D_573) ),
    inference(superposition,[status(thm),theory(equality)],[c_40751,c_22668])).

tff(c_26,plain,(
    ! [C_21,D_22,B_20,A_19] : k2_enumset1(C_21,D_22,B_20,A_19) = k2_enumset1(A_19,B_20,C_21,D_22) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22355,plain,(
    ! [E_368,C_365,B_369,G_363,A_366,D_367,F_364] : r1_tarski(k4_enumset1(A_366,B_369,C_365,D_367,E_368,F_364),k5_enumset1(A_366,B_369,C_365,D_367,E_368,F_364,G_363)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1387,c_18])).

tff(c_22363,plain,(
    ! [A_61,B_62,C_63,D_64] : r1_tarski(k4_enumset1(A_61,A_61,A_61,A_61,B_62,C_63),k2_enumset1(A_61,B_62,C_63,D_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_22355])).

tff(c_22371,plain,(
    ! [A_370,B_371,C_372,D_373] : r1_tarski(k1_enumset1(A_370,B_371,C_372),k2_enumset1(A_370,B_371,C_372,D_373)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_22363])).

tff(c_22382,plain,(
    ! [A_19,B_20,C_21,D_22] : r1_tarski(k1_enumset1(A_19,B_20,C_21),k2_enumset1(C_21,D_22,B_20,A_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_22371])).

tff(c_42061,plain,(
    ! [D_584,C_585] : r1_tarski(k1_enumset1(D_584,C_585,C_585),k2_xboole_0(k1_tarski(C_585),k1_tarski(D_584))) ),
    inference(superposition,[status(thm),theory(equality)],[c_40918,c_22382])).

tff(c_42078,plain,(
    ! [G_401,A_65] : r1_tarski(k1_enumset1(G_401,A_65,A_65),k4_enumset1(A_65,A_65,A_65,A_65,A_65,G_401)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22668,c_42061])).

tff(c_42095,plain,(
    ! [G_401,A_65] : r1_tarski(k1_enumset1(G_401,A_65,A_65),k2_tarski(A_65,G_401)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_38,c_34,c_42078])).

tff(c_42850,plain,(
    ! [A_594,B_595,C_596,D_597] : k3_enumset1(A_594,A_594,B_595,C_596,D_597) = k2_enumset1(A_594,B_595,C_596,D_597) ),
    inference(superposition,[status(thm),theory(equality)],[c_40751,c_34])).

tff(c_42898,plain,(
    ! [B_598,C_599,D_600] : k2_enumset1(B_598,B_598,C_599,D_600) = k1_enumset1(B_598,C_599,D_600) ),
    inference(superposition,[status(thm),theory(equality)],[c_42850,c_38])).

tff(c_22674,plain,(
    ! [A_404,B_405,D_406] : r1_tarski(k2_tarski(A_404,B_405),k2_enumset1(A_404,A_404,B_405,D_406)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_22371])).

tff(c_22694,plain,(
    ! [B_20,C_21,D_22] : r1_tarski(k2_tarski(B_20,C_21),k2_enumset1(C_21,D_22,B_20,B_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_22674])).

tff(c_43353,plain,(
    ! [D_618,B_619] : r1_tarski(k2_tarski(D_618,B_619),k1_enumset1(B_619,D_618,D_618)) ),
    inference(superposition,[status(thm),theory(equality)],[c_42898,c_22694])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_43355,plain,(
    ! [B_619,D_618] :
      ( k1_enumset1(B_619,D_618,D_618) = k2_tarski(D_618,B_619)
      | ~ r1_tarski(k1_enumset1(B_619,D_618,D_618),k2_tarski(D_618,B_619)) ) ),
    inference(resolution,[status(thm)],[c_43353,c_2])).

tff(c_43386,plain,(
    ! [B_620,D_621] : k1_enumset1(B_620,D_621,D_621) = k2_tarski(D_621,B_620) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42095,c_43355])).

tff(c_42863,plain,(
    ! [B_595,C_596,D_597] : k2_enumset1(B_595,B_595,C_596,D_597) = k1_enumset1(B_595,C_596,D_597) ),
    inference(superposition,[status(thm),theory(equality)],[c_42850,c_38])).

tff(c_22391,plain,(
    ! [A_38,B_39,D_373] : r1_tarski(k2_tarski(A_38,B_39),k2_enumset1(A_38,A_38,B_39,D_373)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_22371])).

tff(c_42890,plain,(
    ! [A_38,B_39,D_373] : r1_tarski(k2_tarski(A_38,B_39),k1_enumset1(A_38,B_39,D_373)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42863,c_22391])).

tff(c_43477,plain,(
    ! [B_624,D_625] : r1_tarski(k2_tarski(B_624,D_625),k2_tarski(D_625,B_624)) ),
    inference(superposition,[status(thm),theory(equality)],[c_43386,c_42890])).

tff(c_636,plain,(
    ! [A_137,B_138,C_139] :
      ( r1_tarski(k2_tarski(A_137,B_138),C_139)
      | ~ r2_hidden(B_138,C_139)
      | ~ r2_hidden(A_137,C_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_658,plain,(
    ! [A_137,B_138,C_139] :
      ( k2_tarski(A_137,B_138) = C_139
      | ~ r1_tarski(C_139,k2_tarski(A_137,B_138))
      | ~ r2_hidden(B_138,C_139)
      | ~ r2_hidden(A_137,C_139) ) ),
    inference(resolution,[status(thm)],[c_636,c_2])).

tff(c_43480,plain,(
    ! [D_625,B_624] :
      ( k2_tarski(D_625,B_624) = k2_tarski(B_624,D_625)
      | ~ r2_hidden(B_624,k2_tarski(B_624,D_625))
      | ~ r2_hidden(D_625,k2_tarski(B_624,D_625)) ) ),
    inference(resolution,[status(thm)],[c_43477,c_658])).

tff(c_43507,plain,(
    ! [D_626,B_627] : k2_tarski(D_626,B_627) = k2_tarski(B_627,D_626) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_148,c_43480])).

tff(c_46,plain,(
    ! [A_66,B_67] : k3_tarski(k2_tarski(A_66,B_67)) = k2_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_44479,plain,(
    ! [B_631,D_632] : k3_tarski(k2_tarski(B_631,D_632)) = k2_xboole_0(D_632,B_631) ),
    inference(superposition,[status(thm),theory(equality)],[c_43507,c_46])).

tff(c_44485,plain,(
    ! [D_632,B_631] : k2_xboole_0(D_632,B_631) = k2_xboole_0(B_631,D_632) ),
    inference(superposition,[status(thm),theory(equality)],[c_44479,c_46])).

tff(c_58,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_183,plain,(
    ! [B_107,A_108] :
      ( B_107 = A_108
      | ~ r1_tarski(B_107,A_108)
      | ~ r1_tarski(A_108,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_198,plain,
    ( k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_58,c_183])).

tff(c_305,plain,(
    ~ r1_tarski('#skF_3',k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_198])).

tff(c_44508,plain,(
    ~ r1_tarski('#skF_3',k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44485,c_305])).

tff(c_44512,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_44508])).

tff(c_44513,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_147,plain,(
    ! [A_90,B_92,B_12] : r2_hidden(A_90,k2_xboole_0(k2_tarski(A_90,B_92),B_12)) ),
    inference(resolution,[status(thm)],[c_18,c_138])).

tff(c_44526,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_44513,c_147])).

tff(c_44537,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_44526])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:10:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.47/9.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.47/9.77  
% 16.47/9.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.47/9.77  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 16.47/9.77  
% 16.47/9.77  %Foreground sorts:
% 16.47/9.77  
% 16.47/9.77  
% 16.47/9.77  %Background operators:
% 16.47/9.77  
% 16.47/9.77  
% 16.47/9.77  %Foreground operators:
% 16.47/9.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.47/9.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.47/9.77  tff(k1_tarski, type, k1_tarski: $i > $i).
% 16.47/9.77  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 16.47/9.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.47/9.77  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 16.47/9.77  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 16.47/9.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.47/9.77  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 16.47/9.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.47/9.77  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 16.47/9.77  tff('#skF_2', type, '#skF_2': $i).
% 16.47/9.77  tff('#skF_3', type, '#skF_3': $i).
% 16.47/9.77  tff('#skF_1', type, '#skF_1': $i).
% 16.47/9.77  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 16.47/9.77  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 16.47/9.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.47/9.77  tff(k3_tarski, type, k3_tarski: $i > $i).
% 16.47/9.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.47/9.77  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 16.47/9.77  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.47/9.77  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 16.47/9.77  
% 16.69/9.79  tff(f_84, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 16.69/9.79  tff(f_43, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 16.69/9.79  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 16.69/9.79  tff(f_79, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 16.69/9.79  tff(f_57, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 16.69/9.79  tff(f_63, axiom, (![A, B, C]: (k3_enumset1(A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_enumset1)).
% 16.69/9.79  tff(f_59, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 16.69/9.79  tff(f_69, axiom, (![A]: (k3_enumset1(A, A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_enumset1)).
% 16.69/9.79  tff(f_61, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 16.69/9.79  tff(f_65, axiom, (![A, B, C, D, E, F]: (k6_enumset1(A, A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_enumset1)).
% 16.69/9.79  tff(f_53, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_enumset1)).
% 16.69/9.79  tff(f_67, axiom, (![A, B, C, D]: (k5_enumset1(A, A, A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_enumset1)).
% 16.69/9.79  tff(f_51, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, D, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_enumset1)).
% 16.69/9.79  tff(f_71, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 16.69/9.79  tff(c_56, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 16.69/9.79  tff(c_18, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 16.69/9.79  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.69/9.79  tff(c_156, plain, (![B_98, C_99, A_100]: (r2_hidden(B_98, C_99) | ~r1_tarski(k2_tarski(A_100, B_98), C_99))), inference(cnfTransformation, [status(thm)], [f_79])).
% 16.69/9.79  tff(c_166, plain, (![B_98, A_100]: (r2_hidden(B_98, k2_tarski(A_100, B_98)))), inference(resolution, [status(thm)], [c_6, c_156])).
% 16.69/9.79  tff(c_138, plain, (![A_90, C_91, B_92]: (r2_hidden(A_90, C_91) | ~r1_tarski(k2_tarski(A_90, B_92), C_91))), inference(cnfTransformation, [status(thm)], [f_79])).
% 16.69/9.79  tff(c_148, plain, (![A_90, B_92]: (r2_hidden(A_90, k2_tarski(A_90, B_92)))), inference(resolution, [status(thm)], [c_6, c_138])).
% 16.69/9.79  tff(c_32, plain, (![A_38, B_39]: (k1_enumset1(A_38, A_38, B_39)=k2_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.69/9.79  tff(c_38, plain, (![A_52, B_53, C_54]: (k3_enumset1(A_52, A_52, A_52, B_53, C_54)=k1_enumset1(A_52, B_53, C_54))), inference(cnfTransformation, [status(thm)], [f_63])).
% 16.69/9.79  tff(c_34, plain, (![E_44, C_42, A_40, D_43, B_41]: (k4_enumset1(A_40, A_40, B_41, C_42, D_43, E_44)=k3_enumset1(A_40, B_41, C_42, D_43, E_44))), inference(cnfTransformation, [status(thm)], [f_59])).
% 16.69/9.79  tff(c_44, plain, (![A_65]: (k3_enumset1(A_65, A_65, A_65, A_65, A_65)=k1_tarski(A_65))), inference(cnfTransformation, [status(thm)], [f_69])).
% 16.69/9.79  tff(c_1151, plain, (![D_173, G_171, E_175, A_172, F_176, C_174, B_170]: (k6_enumset1(A_172, A_172, B_170, C_174, D_173, E_175, F_176, G_171)=k5_enumset1(A_172, B_170, C_174, D_173, E_175, F_176, G_171))), inference(cnfTransformation, [status(thm)], [f_61])).
% 16.69/9.79  tff(c_40, plain, (![B_56, E_59, C_57, A_55, F_60, D_58]: (k6_enumset1(A_55, A_55, A_55, B_56, C_57, D_58, E_59, F_60)=k4_enumset1(A_55, B_56, C_57, D_58, E_59, F_60))), inference(cnfTransformation, [status(thm)], [f_65])).
% 16.69/9.79  tff(c_1158, plain, (![D_173, G_171, E_175, F_176, C_174, B_170]: (k5_enumset1(B_170, B_170, C_174, D_173, E_175, F_176, G_171)=k4_enumset1(B_170, C_174, D_173, E_175, F_176, G_171))), inference(superposition, [status(thm), theory('equality')], [c_1151, c_40])).
% 16.69/9.79  tff(c_1387, plain, (![E_184, C_181, G_183, B_185, A_187, D_186, F_182]: (k2_xboole_0(k4_enumset1(A_187, B_185, C_181, D_186, E_184, F_182), k1_tarski(G_183))=k5_enumset1(A_187, B_185, C_181, D_186, E_184, F_182, G_183))), inference(cnfTransformation, [status(thm)], [f_53])).
% 16.69/9.79  tff(c_1408, plain, (![E_44, C_42, G_183, A_40, D_43, B_41]: (k5_enumset1(A_40, A_40, B_41, C_42, D_43, E_44, G_183)=k2_xboole_0(k3_enumset1(A_40, B_41, C_42, D_43, E_44), k1_tarski(G_183)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1387])).
% 16.69/9.79  tff(c_22602, plain, (![C_402, B_403, G_401, E_398, A_399, D_400]: (k2_xboole_0(k3_enumset1(A_399, B_403, C_402, D_400, E_398), k1_tarski(G_401))=k4_enumset1(A_399, B_403, C_402, D_400, E_398, G_401))), inference(demodulation, [status(thm), theory('equality')], [c_1158, c_1408])).
% 16.69/9.79  tff(c_22668, plain, (![A_65, G_401]: (k4_enumset1(A_65, A_65, A_65, A_65, A_65, G_401)=k2_xboole_0(k1_tarski(A_65), k1_tarski(G_401)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_22602])).
% 16.69/9.79  tff(c_42, plain, (![A_61, B_62, C_63, D_64]: (k5_enumset1(A_61, A_61, A_61, A_61, B_62, C_63, D_64)=k2_enumset1(A_61, B_62, C_63, D_64))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.69/9.79  tff(c_16708, plain, (![F_337, B_339, D_338, E_341, C_340, G_336]: (k5_enumset1(B_339, B_339, C_340, D_338, E_341, F_337, G_336)=k4_enumset1(B_339, C_340, D_338, E_341, F_337, G_336))), inference(superposition, [status(thm), theory('equality')], [c_1151, c_40])).
% 16.69/9.79  tff(c_40751, plain, (![A_567, B_568, C_569, D_570]: (k4_enumset1(A_567, A_567, A_567, B_568, C_569, D_570)=k2_enumset1(A_567, B_568, C_569, D_570))), inference(superposition, [status(thm), theory('equality')], [c_42, c_16708])).
% 16.69/9.79  tff(c_40918, plain, (![C_572, D_573]: (k2_xboole_0(k1_tarski(C_572), k1_tarski(D_573))=k2_enumset1(C_572, C_572, C_572, D_573))), inference(superposition, [status(thm), theory('equality')], [c_40751, c_22668])).
% 16.69/9.79  tff(c_26, plain, (![C_21, D_22, B_20, A_19]: (k2_enumset1(C_21, D_22, B_20, A_19)=k2_enumset1(A_19, B_20, C_21, D_22))), inference(cnfTransformation, [status(thm)], [f_51])).
% 16.69/9.79  tff(c_22355, plain, (![E_368, C_365, B_369, G_363, A_366, D_367, F_364]: (r1_tarski(k4_enumset1(A_366, B_369, C_365, D_367, E_368, F_364), k5_enumset1(A_366, B_369, C_365, D_367, E_368, F_364, G_363)))), inference(superposition, [status(thm), theory('equality')], [c_1387, c_18])).
% 16.69/9.79  tff(c_22363, plain, (![A_61, B_62, C_63, D_64]: (r1_tarski(k4_enumset1(A_61, A_61, A_61, A_61, B_62, C_63), k2_enumset1(A_61, B_62, C_63, D_64)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_22355])).
% 16.69/9.79  tff(c_22371, plain, (![A_370, B_371, C_372, D_373]: (r1_tarski(k1_enumset1(A_370, B_371, C_372), k2_enumset1(A_370, B_371, C_372, D_373)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_22363])).
% 16.69/9.79  tff(c_22382, plain, (![A_19, B_20, C_21, D_22]: (r1_tarski(k1_enumset1(A_19, B_20, C_21), k2_enumset1(C_21, D_22, B_20, A_19)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_22371])).
% 16.69/9.79  tff(c_42061, plain, (![D_584, C_585]: (r1_tarski(k1_enumset1(D_584, C_585, C_585), k2_xboole_0(k1_tarski(C_585), k1_tarski(D_584))))), inference(superposition, [status(thm), theory('equality')], [c_40918, c_22382])).
% 16.69/9.79  tff(c_42078, plain, (![G_401, A_65]: (r1_tarski(k1_enumset1(G_401, A_65, A_65), k4_enumset1(A_65, A_65, A_65, A_65, A_65, G_401)))), inference(superposition, [status(thm), theory('equality')], [c_22668, c_42061])).
% 16.69/9.79  tff(c_42095, plain, (![G_401, A_65]: (r1_tarski(k1_enumset1(G_401, A_65, A_65), k2_tarski(A_65, G_401)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_38, c_34, c_42078])).
% 16.69/9.79  tff(c_42850, plain, (![A_594, B_595, C_596, D_597]: (k3_enumset1(A_594, A_594, B_595, C_596, D_597)=k2_enumset1(A_594, B_595, C_596, D_597))), inference(superposition, [status(thm), theory('equality')], [c_40751, c_34])).
% 16.69/9.79  tff(c_42898, plain, (![B_598, C_599, D_600]: (k2_enumset1(B_598, B_598, C_599, D_600)=k1_enumset1(B_598, C_599, D_600))), inference(superposition, [status(thm), theory('equality')], [c_42850, c_38])).
% 16.69/9.79  tff(c_22674, plain, (![A_404, B_405, D_406]: (r1_tarski(k2_tarski(A_404, B_405), k2_enumset1(A_404, A_404, B_405, D_406)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_22371])).
% 16.69/9.79  tff(c_22694, plain, (![B_20, C_21, D_22]: (r1_tarski(k2_tarski(B_20, C_21), k2_enumset1(C_21, D_22, B_20, B_20)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_22674])).
% 16.69/9.79  tff(c_43353, plain, (![D_618, B_619]: (r1_tarski(k2_tarski(D_618, B_619), k1_enumset1(B_619, D_618, D_618)))), inference(superposition, [status(thm), theory('equality')], [c_42898, c_22694])).
% 16.69/9.79  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.69/9.79  tff(c_43355, plain, (![B_619, D_618]: (k1_enumset1(B_619, D_618, D_618)=k2_tarski(D_618, B_619) | ~r1_tarski(k1_enumset1(B_619, D_618, D_618), k2_tarski(D_618, B_619)))), inference(resolution, [status(thm)], [c_43353, c_2])).
% 16.69/9.79  tff(c_43386, plain, (![B_620, D_621]: (k1_enumset1(B_620, D_621, D_621)=k2_tarski(D_621, B_620))), inference(demodulation, [status(thm), theory('equality')], [c_42095, c_43355])).
% 16.69/9.79  tff(c_42863, plain, (![B_595, C_596, D_597]: (k2_enumset1(B_595, B_595, C_596, D_597)=k1_enumset1(B_595, C_596, D_597))), inference(superposition, [status(thm), theory('equality')], [c_42850, c_38])).
% 16.69/9.79  tff(c_22391, plain, (![A_38, B_39, D_373]: (r1_tarski(k2_tarski(A_38, B_39), k2_enumset1(A_38, A_38, B_39, D_373)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_22371])).
% 16.69/9.79  tff(c_42890, plain, (![A_38, B_39, D_373]: (r1_tarski(k2_tarski(A_38, B_39), k1_enumset1(A_38, B_39, D_373)))), inference(demodulation, [status(thm), theory('equality')], [c_42863, c_22391])).
% 16.69/9.79  tff(c_43477, plain, (![B_624, D_625]: (r1_tarski(k2_tarski(B_624, D_625), k2_tarski(D_625, B_624)))), inference(superposition, [status(thm), theory('equality')], [c_43386, c_42890])).
% 16.69/9.79  tff(c_636, plain, (![A_137, B_138, C_139]: (r1_tarski(k2_tarski(A_137, B_138), C_139) | ~r2_hidden(B_138, C_139) | ~r2_hidden(A_137, C_139))), inference(cnfTransformation, [status(thm)], [f_79])).
% 16.69/9.79  tff(c_658, plain, (![A_137, B_138, C_139]: (k2_tarski(A_137, B_138)=C_139 | ~r1_tarski(C_139, k2_tarski(A_137, B_138)) | ~r2_hidden(B_138, C_139) | ~r2_hidden(A_137, C_139))), inference(resolution, [status(thm)], [c_636, c_2])).
% 16.69/9.79  tff(c_43480, plain, (![D_625, B_624]: (k2_tarski(D_625, B_624)=k2_tarski(B_624, D_625) | ~r2_hidden(B_624, k2_tarski(B_624, D_625)) | ~r2_hidden(D_625, k2_tarski(B_624, D_625)))), inference(resolution, [status(thm)], [c_43477, c_658])).
% 16.69/9.79  tff(c_43507, plain, (![D_626, B_627]: (k2_tarski(D_626, B_627)=k2_tarski(B_627, D_626))), inference(demodulation, [status(thm), theory('equality')], [c_166, c_148, c_43480])).
% 16.69/9.79  tff(c_46, plain, (![A_66, B_67]: (k3_tarski(k2_tarski(A_66, B_67))=k2_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_71])).
% 16.69/9.79  tff(c_44479, plain, (![B_631, D_632]: (k3_tarski(k2_tarski(B_631, D_632))=k2_xboole_0(D_632, B_631))), inference(superposition, [status(thm), theory('equality')], [c_43507, c_46])).
% 16.69/9.79  tff(c_44485, plain, (![D_632, B_631]: (k2_xboole_0(D_632, B_631)=k2_xboole_0(B_631, D_632))), inference(superposition, [status(thm), theory('equality')], [c_44479, c_46])).
% 16.69/9.79  tff(c_58, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 16.69/9.79  tff(c_183, plain, (![B_107, A_108]: (B_107=A_108 | ~r1_tarski(B_107, A_108) | ~r1_tarski(A_108, B_107))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.69/9.79  tff(c_198, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'))), inference(resolution, [status(thm)], [c_58, c_183])).
% 16.69/9.79  tff(c_305, plain, (~r1_tarski('#skF_3', k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_198])).
% 16.69/9.79  tff(c_44508, plain, (~r1_tarski('#skF_3', k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_44485, c_305])).
% 16.69/9.79  tff(c_44512, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_44508])).
% 16.69/9.79  tff(c_44513, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_198])).
% 16.69/9.79  tff(c_147, plain, (![A_90, B_92, B_12]: (r2_hidden(A_90, k2_xboole_0(k2_tarski(A_90, B_92), B_12)))), inference(resolution, [status(thm)], [c_18, c_138])).
% 16.69/9.79  tff(c_44526, plain, (r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_44513, c_147])).
% 16.69/9.79  tff(c_44537, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_44526])).
% 16.69/9.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.69/9.79  
% 16.69/9.79  Inference rules
% 16.69/9.79  ----------------------
% 16.69/9.79  #Ref     : 0
% 16.69/9.79  #Sup     : 11632
% 16.69/9.79  #Fact    : 0
% 16.69/9.79  #Define  : 0
% 16.69/9.79  #Split   : 1
% 16.69/9.79  #Chain   : 0
% 16.69/9.79  #Close   : 0
% 16.69/9.79  
% 16.69/9.79  Ordering : KBO
% 16.69/9.79  
% 16.69/9.79  Simplification rules
% 16.69/9.79  ----------------------
% 16.69/9.79  #Subsume      : 715
% 16.69/9.79  #Demod        : 17184
% 16.69/9.79  #Tautology    : 4511
% 16.69/9.79  #SimpNegUnit  : 1
% 16.69/9.79  #BackRed      : 39
% 16.69/9.79  
% 16.69/9.79  #Partial instantiations: 0
% 16.69/9.79  #Strategies tried      : 1
% 16.69/9.79  
% 16.69/9.79  Timing (in seconds)
% 16.69/9.79  ----------------------
% 16.69/9.79  Preprocessing        : 0.34
% 16.69/9.79  Parsing              : 0.19
% 16.69/9.79  CNF conversion       : 0.02
% 16.69/9.79  Main loop            : 8.70
% 16.69/9.79  Inferencing          : 1.16
% 16.69/9.79  Reduction            : 6.01
% 16.69/9.79  Demodulation         : 5.68
% 16.69/9.79  BG Simplification    : 0.21
% 16.69/9.79  Subsumption          : 1.03
% 16.69/9.79  Abstraction          : 0.33
% 16.69/9.79  MUC search           : 0.00
% 16.69/9.79  Cooper               : 0.00
% 16.69/9.79  Total                : 9.08
% 16.69/9.79  Index Insertion      : 0.00
% 16.69/9.79  Index Deletion       : 0.00
% 16.69/9.80  Index Matching       : 0.00
% 16.69/9.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
