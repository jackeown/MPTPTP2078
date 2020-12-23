%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:29 EST 2020

% Result     : Theorem 5.00s
% Output     : CNFRefutation 5.33s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 396 expanded)
%              Number of leaves         :   38 ( 161 expanded)
%              Depth                    :   17
%              Number of atoms          :  111 ( 624 expanded)
%              Number of equality atoms :   46 ( 306 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_113,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_67,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_103,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(c_52,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_58,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_54,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_40,plain,(
    ! [A_48] : v1_relat_1(k6_relat_1(A_48)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_32,plain,(
    ! [A_43] : k1_relat_1(k6_relat_1(A_43)) = A_43 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_925,plain,(
    ! [B_160,A_161] :
      ( k7_relat_1(B_160,A_161) = B_160
      | ~ r1_tarski(k1_relat_1(B_160),A_161)
      | ~ v1_relat_1(B_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_951,plain,(
    ! [B_162] :
      ( k7_relat_1(B_162,k1_relat_1(B_162)) = B_162
      | ~ v1_relat_1(B_162) ) ),
    inference(resolution,[status(thm)],[c_6,c_925])).

tff(c_562,plain,(
    ! [B_126,A_127] : k5_relat_1(k6_relat_1(B_126),k6_relat_1(A_127)) = k6_relat_1(k3_xboole_0(A_127,B_126)) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_36,plain,(
    ! [A_44,B_45] :
      ( k5_relat_1(k6_relat_1(A_44),B_45) = k7_relat_1(B_45,A_44)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_568,plain,(
    ! [A_127,B_126] :
      ( k7_relat_1(k6_relat_1(A_127),B_126) = k6_relat_1(k3_xboole_0(A_127,B_126))
      | ~ v1_relat_1(k6_relat_1(A_127)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_562,c_36])).

tff(c_578,plain,(
    ! [A_127,B_126] : k7_relat_1(k6_relat_1(A_127),B_126) = k6_relat_1(k3_xboole_0(A_127,B_126)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_568])).

tff(c_958,plain,(
    ! [A_127] :
      ( k6_relat_1(k3_xboole_0(A_127,k1_relat_1(k6_relat_1(A_127)))) = k6_relat_1(A_127)
      | ~ v1_relat_1(k6_relat_1(A_127)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_951,c_578])).

tff(c_980,plain,(
    ! [A_163] : k6_relat_1(k3_xboole_0(A_163,A_163)) = k6_relat_1(A_163) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_958])).

tff(c_1022,plain,(
    ! [A_163] : k3_xboole_0(A_163,A_163) = k1_relat_1(k6_relat_1(A_163)) ),
    inference(superposition,[status(thm),theory(equality)],[c_980,c_32])).

tff(c_1039,plain,(
    ! [A_163] : k3_xboole_0(A_163,A_163) = A_163 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1022])).

tff(c_42,plain,(
    ! [A_48] : v1_funct_1(k6_relat_1(A_48)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_34,plain,(
    ! [A_43] : k2_relat_1(k6_relat_1(A_43)) = A_43 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_582,plain,(
    ! [A_128,B_129] : k7_relat_1(k6_relat_1(A_128),B_129) = k6_relat_1(k3_xboole_0(A_128,B_129)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_568])).

tff(c_28,plain,(
    ! [B_40,A_39] :
      ( k2_relat_1(k7_relat_1(B_40,A_39)) = k9_relat_1(B_40,A_39)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_588,plain,(
    ! [A_128,B_129] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_128,B_129))) = k9_relat_1(k6_relat_1(A_128),B_129)
      | ~ v1_relat_1(k6_relat_1(A_128)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_582,c_28])).

tff(c_594,plain,(
    ! [A_128,B_129] : k9_relat_1(k6_relat_1(A_128),B_129) = k3_xboole_0(A_128,B_129) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34,c_588])).

tff(c_2926,plain,(
    ! [A_239,B_240] :
      ( k3_xboole_0(A_239,k9_relat_1(B_240,k1_relat_1(B_240))) = k9_relat_1(B_240,k10_relat_1(B_240,A_239))
      | ~ v1_funct_1(B_240)
      | ~ v1_relat_1(B_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3068,plain,(
    ! [A_43,A_239] :
      ( k9_relat_1(k6_relat_1(A_43),k10_relat_1(k6_relat_1(A_43),A_239)) = k3_xboole_0(A_239,k9_relat_1(k6_relat_1(A_43),A_43))
      | ~ v1_funct_1(k6_relat_1(A_43))
      | ~ v1_relat_1(k6_relat_1(A_43)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2926])).

tff(c_3318,plain,(
    ! [A_248,A_249] : k3_xboole_0(A_248,k10_relat_1(k6_relat_1(A_248),A_249)) = k3_xboole_0(A_249,A_248) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_1039,c_594,c_594,c_3068])).

tff(c_44,plain,(
    ! [A_49,C_51,B_50] :
      ( k3_xboole_0(A_49,k10_relat_1(C_51,B_50)) = k10_relat_1(k7_relat_1(C_51,A_49),B_50)
      | ~ v1_relat_1(C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3369,plain,(
    ! [A_248,A_249] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_248),A_248),A_249) = k3_xboole_0(A_249,A_248)
      | ~ v1_relat_1(k6_relat_1(A_248)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3318,c_44])).

tff(c_3443,plain,(
    ! [A_248,A_249] : k10_relat_1(k6_relat_1(A_248),A_249) = k3_xboole_0(A_249,A_248) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1039,c_578,c_3369])).

tff(c_3074,plain,(
    ! [A_43,A_239] : k3_xboole_0(A_43,k10_relat_1(k6_relat_1(A_43),A_239)) = k3_xboole_0(A_239,A_43) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_1039,c_594,c_594,c_3068])).

tff(c_3659,plain,(
    ! [A_43,A_239] : k3_xboole_0(A_43,k3_xboole_0(A_239,A_43)) = k3_xboole_0(A_239,A_43) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3443,c_3074])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_940,plain,(
    ! [A_43,A_161] :
      ( k7_relat_1(k6_relat_1(A_43),A_161) = k6_relat_1(A_43)
      | ~ r1_tarski(A_43,A_161)
      | ~ v1_relat_1(k6_relat_1(A_43)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_925])).

tff(c_1174,plain,(
    ! [A_170,A_171] :
      ( k6_relat_1(k3_xboole_0(A_170,A_171)) = k6_relat_1(A_170)
      | ~ r1_tarski(A_170,A_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_578,c_940])).

tff(c_1216,plain,(
    ! [A_170,A_171] :
      ( k3_xboole_0(A_170,A_171) = k1_relat_1(k6_relat_1(A_170))
      | ~ r1_tarski(A_170,A_171) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1174,c_32])).

tff(c_1244,plain,(
    ! [A_172,A_173] :
      ( k3_xboole_0(A_172,A_173) = A_172
      | ~ r1_tarski(A_172,A_173) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1216])).

tff(c_1334,plain,(
    ! [A_8,B_9] : k3_xboole_0(k3_xboole_0(A_8,B_9),A_8) = k3_xboole_0(A_8,B_9) ),
    inference(resolution,[status(thm)],[c_12,c_1244])).

tff(c_4020,plain,(
    ! [A_276,C_277,B_278] :
      ( r1_tarski(A_276,k10_relat_1(C_277,B_278))
      | ~ r1_tarski(k9_relat_1(C_277,A_276),B_278)
      | ~ r1_tarski(A_276,k1_relat_1(C_277))
      | ~ v1_funct_1(C_277)
      | ~ v1_relat_1(C_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_5444,plain,(
    ! [A_305,C_306] :
      ( r1_tarski(A_305,k10_relat_1(C_306,k9_relat_1(C_306,A_305)))
      | ~ r1_tarski(A_305,k1_relat_1(C_306))
      | ~ v1_funct_1(C_306)
      | ~ v1_relat_1(C_306) ) ),
    inference(resolution,[status(thm)],[c_6,c_4020])).

tff(c_5478,plain,(
    ! [B_129,A_128] :
      ( r1_tarski(B_129,k10_relat_1(k6_relat_1(A_128),k3_xboole_0(A_128,B_129)))
      | ~ r1_tarski(B_129,k1_relat_1(k6_relat_1(A_128)))
      | ~ v1_funct_1(k6_relat_1(A_128))
      | ~ v1_relat_1(k6_relat_1(A_128)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_594,c_5444])).

tff(c_5494,plain,(
    ! [B_307,A_308] :
      ( r1_tarski(B_307,k3_xboole_0(A_308,B_307))
      | ~ r1_tarski(B_307,A_308) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_32,c_1334,c_3443,c_5478])).

tff(c_1236,plain,(
    ! [A_170,A_171] :
      ( k3_xboole_0(A_170,A_171) = A_170
      | ~ r1_tarski(A_170,A_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1216])).

tff(c_5504,plain,(
    ! [B_307,A_308] :
      ( k3_xboole_0(B_307,k3_xboole_0(A_308,B_307)) = B_307
      | ~ r1_tarski(B_307,A_308) ) ),
    inference(resolution,[status(thm)],[c_5494,c_1236])).

tff(c_5575,plain,(
    ! [A_309,B_310] :
      ( k3_xboole_0(A_309,B_310) = B_310
      | ~ r1_tarski(B_310,A_309) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3659,c_5504])).

tff(c_5717,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_5575])).

tff(c_5781,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5717,c_44])).

tff(c_5839,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_5781])).

tff(c_5841,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_5839])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:37:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.00/1.97  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.00/1.97  
% 5.00/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.00/1.98  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.00/1.98  
% 5.00/1.98  %Foreground sorts:
% 5.00/1.98  
% 5.00/1.98  
% 5.00/1.98  %Background operators:
% 5.00/1.98  
% 5.00/1.98  
% 5.00/1.98  %Foreground operators:
% 5.00/1.98  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.00/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.00/1.98  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.00/1.98  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.00/1.98  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.00/1.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.00/1.98  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.00/1.98  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.00/1.98  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.00/1.98  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.00/1.98  tff('#skF_2', type, '#skF_2': $i).
% 5.00/1.98  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.00/1.98  tff('#skF_3', type, '#skF_3': $i).
% 5.00/1.98  tff('#skF_1', type, '#skF_1': $i).
% 5.00/1.98  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.00/1.98  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.00/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.00/1.98  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.00/1.98  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.00/1.98  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.00/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.00/1.98  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.00/1.98  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.00/1.98  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.00/1.98  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.00/1.98  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.00/1.98  
% 5.33/1.99  tff(f_113, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 5.33/1.99  tff(f_81, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 5.33/1.99  tff(f_67, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 5.33/1.99  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.33/1.99  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 5.33/1.99  tff(f_103, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 5.33/1.99  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 5.33/1.99  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 5.33/1.99  tff(f_91, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_funct_1)).
% 5.33/1.99  tff(f_85, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 5.33/1.99  tff(f_41, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.33/1.99  tff(f_101, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 5.33/1.99  tff(c_52, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.33/1.99  tff(c_58, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.33/1.99  tff(c_54, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.33/1.99  tff(c_40, plain, (![A_48]: (v1_relat_1(k6_relat_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.33/1.99  tff(c_32, plain, (![A_43]: (k1_relat_1(k6_relat_1(A_43))=A_43)), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.33/1.99  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.33/1.99  tff(c_925, plain, (![B_160, A_161]: (k7_relat_1(B_160, A_161)=B_160 | ~r1_tarski(k1_relat_1(B_160), A_161) | ~v1_relat_1(B_160))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.33/1.99  tff(c_951, plain, (![B_162]: (k7_relat_1(B_162, k1_relat_1(B_162))=B_162 | ~v1_relat_1(B_162))), inference(resolution, [status(thm)], [c_6, c_925])).
% 5.33/1.99  tff(c_562, plain, (![B_126, A_127]: (k5_relat_1(k6_relat_1(B_126), k6_relat_1(A_127))=k6_relat_1(k3_xboole_0(A_127, B_126)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.33/1.99  tff(c_36, plain, (![A_44, B_45]: (k5_relat_1(k6_relat_1(A_44), B_45)=k7_relat_1(B_45, A_44) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.33/1.99  tff(c_568, plain, (![A_127, B_126]: (k7_relat_1(k6_relat_1(A_127), B_126)=k6_relat_1(k3_xboole_0(A_127, B_126)) | ~v1_relat_1(k6_relat_1(A_127)))), inference(superposition, [status(thm), theory('equality')], [c_562, c_36])).
% 5.33/1.99  tff(c_578, plain, (![A_127, B_126]: (k7_relat_1(k6_relat_1(A_127), B_126)=k6_relat_1(k3_xboole_0(A_127, B_126)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_568])).
% 5.33/1.99  tff(c_958, plain, (![A_127]: (k6_relat_1(k3_xboole_0(A_127, k1_relat_1(k6_relat_1(A_127))))=k6_relat_1(A_127) | ~v1_relat_1(k6_relat_1(A_127)))), inference(superposition, [status(thm), theory('equality')], [c_951, c_578])).
% 5.33/1.99  tff(c_980, plain, (![A_163]: (k6_relat_1(k3_xboole_0(A_163, A_163))=k6_relat_1(A_163))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32, c_958])).
% 5.33/1.99  tff(c_1022, plain, (![A_163]: (k3_xboole_0(A_163, A_163)=k1_relat_1(k6_relat_1(A_163)))), inference(superposition, [status(thm), theory('equality')], [c_980, c_32])).
% 5.33/1.99  tff(c_1039, plain, (![A_163]: (k3_xboole_0(A_163, A_163)=A_163)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1022])).
% 5.33/1.99  tff(c_42, plain, (![A_48]: (v1_funct_1(k6_relat_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.33/1.99  tff(c_34, plain, (![A_43]: (k2_relat_1(k6_relat_1(A_43))=A_43)), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.33/1.99  tff(c_582, plain, (![A_128, B_129]: (k7_relat_1(k6_relat_1(A_128), B_129)=k6_relat_1(k3_xboole_0(A_128, B_129)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_568])).
% 5.33/1.99  tff(c_28, plain, (![B_40, A_39]: (k2_relat_1(k7_relat_1(B_40, A_39))=k9_relat_1(B_40, A_39) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.33/1.99  tff(c_588, plain, (![A_128, B_129]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_128, B_129)))=k9_relat_1(k6_relat_1(A_128), B_129) | ~v1_relat_1(k6_relat_1(A_128)))), inference(superposition, [status(thm), theory('equality')], [c_582, c_28])).
% 5.33/1.99  tff(c_594, plain, (![A_128, B_129]: (k9_relat_1(k6_relat_1(A_128), B_129)=k3_xboole_0(A_128, B_129))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_34, c_588])).
% 5.33/1.99  tff(c_2926, plain, (![A_239, B_240]: (k3_xboole_0(A_239, k9_relat_1(B_240, k1_relat_1(B_240)))=k9_relat_1(B_240, k10_relat_1(B_240, A_239)) | ~v1_funct_1(B_240) | ~v1_relat_1(B_240))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.33/1.99  tff(c_3068, plain, (![A_43, A_239]: (k9_relat_1(k6_relat_1(A_43), k10_relat_1(k6_relat_1(A_43), A_239))=k3_xboole_0(A_239, k9_relat_1(k6_relat_1(A_43), A_43)) | ~v1_funct_1(k6_relat_1(A_43)) | ~v1_relat_1(k6_relat_1(A_43)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_2926])).
% 5.33/1.99  tff(c_3318, plain, (![A_248, A_249]: (k3_xboole_0(A_248, k10_relat_1(k6_relat_1(A_248), A_249))=k3_xboole_0(A_249, A_248))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_1039, c_594, c_594, c_3068])).
% 5.33/1.99  tff(c_44, plain, (![A_49, C_51, B_50]: (k3_xboole_0(A_49, k10_relat_1(C_51, B_50))=k10_relat_1(k7_relat_1(C_51, A_49), B_50) | ~v1_relat_1(C_51))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.33/1.99  tff(c_3369, plain, (![A_248, A_249]: (k10_relat_1(k7_relat_1(k6_relat_1(A_248), A_248), A_249)=k3_xboole_0(A_249, A_248) | ~v1_relat_1(k6_relat_1(A_248)))), inference(superposition, [status(thm), theory('equality')], [c_3318, c_44])).
% 5.33/1.99  tff(c_3443, plain, (![A_248, A_249]: (k10_relat_1(k6_relat_1(A_248), A_249)=k3_xboole_0(A_249, A_248))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1039, c_578, c_3369])).
% 5.33/1.99  tff(c_3074, plain, (![A_43, A_239]: (k3_xboole_0(A_43, k10_relat_1(k6_relat_1(A_43), A_239))=k3_xboole_0(A_239, A_43))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_1039, c_594, c_594, c_3068])).
% 5.33/1.99  tff(c_3659, plain, (![A_43, A_239]: (k3_xboole_0(A_43, k3_xboole_0(A_239, A_43))=k3_xboole_0(A_239, A_43))), inference(demodulation, [status(thm), theory('equality')], [c_3443, c_3074])).
% 5.33/1.99  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.33/1.99  tff(c_940, plain, (![A_43, A_161]: (k7_relat_1(k6_relat_1(A_43), A_161)=k6_relat_1(A_43) | ~r1_tarski(A_43, A_161) | ~v1_relat_1(k6_relat_1(A_43)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_925])).
% 5.33/1.99  tff(c_1174, plain, (![A_170, A_171]: (k6_relat_1(k3_xboole_0(A_170, A_171))=k6_relat_1(A_170) | ~r1_tarski(A_170, A_171))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_578, c_940])).
% 5.33/1.99  tff(c_1216, plain, (![A_170, A_171]: (k3_xboole_0(A_170, A_171)=k1_relat_1(k6_relat_1(A_170)) | ~r1_tarski(A_170, A_171))), inference(superposition, [status(thm), theory('equality')], [c_1174, c_32])).
% 5.33/1.99  tff(c_1244, plain, (![A_172, A_173]: (k3_xboole_0(A_172, A_173)=A_172 | ~r1_tarski(A_172, A_173))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1216])).
% 5.33/1.99  tff(c_1334, plain, (![A_8, B_9]: (k3_xboole_0(k3_xboole_0(A_8, B_9), A_8)=k3_xboole_0(A_8, B_9))), inference(resolution, [status(thm)], [c_12, c_1244])).
% 5.33/1.99  tff(c_4020, plain, (![A_276, C_277, B_278]: (r1_tarski(A_276, k10_relat_1(C_277, B_278)) | ~r1_tarski(k9_relat_1(C_277, A_276), B_278) | ~r1_tarski(A_276, k1_relat_1(C_277)) | ~v1_funct_1(C_277) | ~v1_relat_1(C_277))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.33/1.99  tff(c_5444, plain, (![A_305, C_306]: (r1_tarski(A_305, k10_relat_1(C_306, k9_relat_1(C_306, A_305))) | ~r1_tarski(A_305, k1_relat_1(C_306)) | ~v1_funct_1(C_306) | ~v1_relat_1(C_306))), inference(resolution, [status(thm)], [c_6, c_4020])).
% 5.33/1.99  tff(c_5478, plain, (![B_129, A_128]: (r1_tarski(B_129, k10_relat_1(k6_relat_1(A_128), k3_xboole_0(A_128, B_129))) | ~r1_tarski(B_129, k1_relat_1(k6_relat_1(A_128))) | ~v1_funct_1(k6_relat_1(A_128)) | ~v1_relat_1(k6_relat_1(A_128)))), inference(superposition, [status(thm), theory('equality')], [c_594, c_5444])).
% 5.33/1.99  tff(c_5494, plain, (![B_307, A_308]: (r1_tarski(B_307, k3_xboole_0(A_308, B_307)) | ~r1_tarski(B_307, A_308))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_32, c_1334, c_3443, c_5478])).
% 5.33/1.99  tff(c_1236, plain, (![A_170, A_171]: (k3_xboole_0(A_170, A_171)=A_170 | ~r1_tarski(A_170, A_171))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1216])).
% 5.33/1.99  tff(c_5504, plain, (![B_307, A_308]: (k3_xboole_0(B_307, k3_xboole_0(A_308, B_307))=B_307 | ~r1_tarski(B_307, A_308))), inference(resolution, [status(thm)], [c_5494, c_1236])).
% 5.33/1.99  tff(c_5575, plain, (![A_309, B_310]: (k3_xboole_0(A_309, B_310)=B_310 | ~r1_tarski(B_310, A_309))), inference(demodulation, [status(thm), theory('equality')], [c_3659, c_5504])).
% 5.33/1.99  tff(c_5717, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_5575])).
% 5.33/1.99  tff(c_5781, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5717, c_44])).
% 5.33/1.99  tff(c_5839, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_5781])).
% 5.33/1.99  tff(c_5841, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_5839])).
% 5.33/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.33/1.99  
% 5.33/1.99  Inference rules
% 5.33/1.99  ----------------------
% 5.33/1.99  #Ref     : 0
% 5.33/1.99  #Sup     : 1447
% 5.33/1.99  #Fact    : 0
% 5.33/1.99  #Define  : 0
% 5.33/1.99  #Split   : 1
% 5.33/1.99  #Chain   : 0
% 5.33/1.99  #Close   : 0
% 5.33/1.99  
% 5.33/1.99  Ordering : KBO
% 5.33/1.99  
% 5.33/1.99  Simplification rules
% 5.33/1.99  ----------------------
% 5.33/1.99  #Subsume      : 53
% 5.33/1.99  #Demod        : 732
% 5.33/1.99  #Tautology    : 702
% 5.33/1.99  #SimpNegUnit  : 2
% 5.33/1.99  #BackRed      : 15
% 5.33/1.99  
% 5.33/1.99  #Partial instantiations: 0
% 5.33/1.99  #Strategies tried      : 1
% 5.33/1.99  
% 5.33/1.99  Timing (in seconds)
% 5.33/1.99  ----------------------
% 5.33/1.99  Preprocessing        : 0.33
% 5.33/1.99  Parsing              : 0.18
% 5.33/1.99  CNF conversion       : 0.02
% 5.33/1.99  Main loop            : 0.90
% 5.33/1.99  Inferencing          : 0.29
% 5.33/1.99  Reduction            : 0.34
% 5.33/1.99  Demodulation         : 0.26
% 5.33/1.99  BG Simplification    : 0.04
% 5.33/1.99  Subsumption          : 0.17
% 5.33/1.99  Abstraction          : 0.05
% 5.33/2.00  MUC search           : 0.00
% 5.33/2.00  Cooper               : 0.00
% 5.33/2.00  Total                : 1.26
% 5.33/2.00  Index Insertion      : 0.00
% 5.33/2.00  Index Deletion       : 0.00
% 5.33/2.00  Index Matching       : 0.00
% 5.33/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
