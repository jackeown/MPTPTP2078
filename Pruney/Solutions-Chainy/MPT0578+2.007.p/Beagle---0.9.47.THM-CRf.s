%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:56 EST 2020

% Result     : Theorem 44.96s
% Output     : CNFRefutation 44.96s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 109 expanded)
%              Number of leaves         :   21 (  45 expanded)
%              Depth                    :   16
%              Number of atoms          :  142 ( 237 expanded)
%              Number of equality atoms :   27 (  56 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k5_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(k5_relat_1(A_8,B_9))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_12] :
      ( k10_relat_1(A_12,k2_relat_1(A_12)) = k1_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    ! [B_17,C_19,A_16] :
      ( k10_relat_1(k5_relat_1(B_17,C_19),A_16) = k10_relat_1(B_17,k10_relat_1(C_19,A_16))
      | ~ v1_relat_1(C_19)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_114,plain,(
    ! [C_44,A_45,B_46] :
      ( k2_xboole_0(k10_relat_1(C_44,A_45),k10_relat_1(C_44,B_46)) = k10_relat_1(C_44,k2_xboole_0(A_45,B_46))
      | ~ v1_relat_1(C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_147,plain,(
    ! [C_47,A_48,B_49] :
      ( r1_tarski(k10_relat_1(C_47,A_48),k10_relat_1(C_47,k2_xboole_0(A_48,B_49)))
      | ~ v1_relat_1(C_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_10])).

tff(c_159,plain,(
    ! [B_17,C_19,A_48,B_49] :
      ( r1_tarski(k10_relat_1(k5_relat_1(B_17,C_19),A_48),k10_relat_1(B_17,k10_relat_1(C_19,k2_xboole_0(A_48,B_49))))
      | ~ v1_relat_1(k5_relat_1(B_17,C_19))
      | ~ v1_relat_1(C_19)
      | ~ v1_relat_1(B_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_147])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_218,plain,(
    ! [A_54,C_55,A_56,B_57] :
      ( r1_tarski(A_54,k10_relat_1(C_55,k2_xboole_0(A_56,B_57)))
      | ~ r1_tarski(A_54,k10_relat_1(C_55,B_57))
      | ~ v1_relat_1(C_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_8])).

tff(c_54,plain,(
    ! [B_32,A_33] :
      ( r1_tarski(k10_relat_1(B_32,A_33),k1_relat_1(B_32))
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ! [B_32,A_33] :
      ( k10_relat_1(B_32,A_33) = k1_relat_1(B_32)
      | ~ r1_tarski(k1_relat_1(B_32),k10_relat_1(B_32,A_33))
      | ~ v1_relat_1(B_32) ) ),
    inference(resolution,[status(thm)],[c_54,c_2])).

tff(c_289,plain,(
    ! [C_64,A_65,B_66] :
      ( k10_relat_1(C_64,k2_xboole_0(A_65,B_66)) = k1_relat_1(C_64)
      | ~ r1_tarski(k1_relat_1(C_64),k10_relat_1(C_64,B_66))
      | ~ v1_relat_1(C_64) ) ),
    inference(resolution,[status(thm)],[c_218,c_60])).

tff(c_300,plain,(
    ! [A_12,A_65] :
      ( k10_relat_1(A_12,k2_xboole_0(A_65,k2_relat_1(A_12))) = k1_relat_1(A_12)
      | ~ r1_tarski(k1_relat_1(A_12),k1_relat_1(A_12))
      | ~ v1_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_289])).

tff(c_307,plain,(
    ! [A_67,A_68] :
      ( k10_relat_1(A_67,k2_xboole_0(A_68,k2_relat_1(A_67))) = k1_relat_1(A_67)
      | ~ v1_relat_1(A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_300])).

tff(c_18,plain,(
    ! [C_15,A_13,B_14] :
      ( k2_xboole_0(k10_relat_1(C_15,A_13),k10_relat_1(C_15,B_14)) = k10_relat_1(C_15,k2_xboole_0(A_13,B_14))
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4525,plain,(
    ! [A_205,A_206,B_207] :
      ( k10_relat_1(A_205,k2_xboole_0(k2_xboole_0(A_206,k2_relat_1(A_205)),B_207)) = k2_xboole_0(k1_relat_1(A_205),k10_relat_1(A_205,B_207))
      | ~ v1_relat_1(A_205)
      | ~ v1_relat_1(A_205) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_18])).

tff(c_164,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(k1_relat_1(A_50),k10_relat_1(A_50,k2_xboole_0(k2_relat_1(A_50),B_51)))
      | ~ v1_relat_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_147])).

tff(c_176,plain,(
    ! [A_52,B_53] :
      ( k10_relat_1(A_52,k2_xboole_0(k2_relat_1(A_52),B_53)) = k1_relat_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(resolution,[status(thm)],[c_164,c_60])).

tff(c_129,plain,(
    ! [C_44,A_45,B_46] :
      ( r1_tarski(k10_relat_1(C_44,A_45),k10_relat_1(C_44,k2_xboole_0(A_45,B_46)))
      | ~ v1_relat_1(C_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_10])).

tff(c_1075,plain,(
    ! [A_100,B_101,B_102] :
      ( r1_tarski(k1_relat_1(A_100),k10_relat_1(A_100,k2_xboole_0(k2_xboole_0(k2_relat_1(A_100),B_101),B_102)))
      | ~ v1_relat_1(A_100)
      | ~ v1_relat_1(A_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_129])).

tff(c_1121,plain,(
    ! [A_100,B_101,B_102] :
      ( k10_relat_1(A_100,k2_xboole_0(k2_xboole_0(k2_relat_1(A_100),B_101),B_102)) = k1_relat_1(A_100)
      | ~ v1_relat_1(A_100) ) ),
    inference(resolution,[status(thm)],[c_1075,c_60])).

tff(c_5014,plain,(
    ! [A_212,B_213] :
      ( k2_xboole_0(k1_relat_1(A_212),k10_relat_1(A_212,B_213)) = k1_relat_1(A_212)
      | ~ v1_relat_1(A_212)
      | ~ v1_relat_1(A_212)
      | ~ v1_relat_1(A_212) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4525,c_1121])).

tff(c_32,plain,(
    ! [B_29,A_30] :
      ( B_29 = A_30
      | ~ r1_tarski(B_29,A_30)
      | ~ r1_tarski(A_30,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(k2_xboole_0(A_6,B_7),A_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_32])).

tff(c_5046,plain,(
    ! [A_212,B_213] :
      ( k2_xboole_0(k1_relat_1(A_212),k10_relat_1(A_212,B_213)) = k1_relat_1(A_212)
      | ~ r1_tarski(k1_relat_1(A_212),k1_relat_1(A_212))
      | ~ v1_relat_1(A_212)
      | ~ v1_relat_1(A_212)
      | ~ v1_relat_1(A_212) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5014,c_40])).

tff(c_5140,plain,(
    ! [A_214,B_215] :
      ( k2_xboole_0(k1_relat_1(A_214),k10_relat_1(A_214,B_215)) = k1_relat_1(A_214)
      | ~ v1_relat_1(A_214) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5046])).

tff(c_126,plain,(
    ! [A_3,C_44,A_45,B_46] :
      ( r1_tarski(A_3,k10_relat_1(C_44,k2_xboole_0(A_45,B_46)))
      | ~ r1_tarski(A_3,k10_relat_1(C_44,B_46))
      | ~ v1_relat_1(C_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_8])).

tff(c_71502,plain,(
    ! [A_820,C_821,A_822,B_823] :
      ( r1_tarski(A_820,k10_relat_1(C_821,k1_relat_1(A_822)))
      | ~ r1_tarski(A_820,k10_relat_1(C_821,k10_relat_1(A_822,B_823)))
      | ~ v1_relat_1(C_821)
      | ~ v1_relat_1(A_822) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5140,c_126])).

tff(c_154618,plain,(
    ! [B_1285,C_1286,A_1287] :
      ( r1_tarski(k10_relat_1(k5_relat_1(B_1285,C_1286),A_1287),k10_relat_1(B_1285,k1_relat_1(C_1286)))
      | ~ v1_relat_1(k5_relat_1(B_1285,C_1286))
      | ~ v1_relat_1(C_1286)
      | ~ v1_relat_1(B_1285) ) ),
    inference(resolution,[status(thm)],[c_159,c_71502])).

tff(c_166712,plain,(
    ! [B_1352,C_1353] :
      ( r1_tarski(k1_relat_1(k5_relat_1(B_1352,C_1353)),k10_relat_1(B_1352,k1_relat_1(C_1353)))
      | ~ v1_relat_1(k5_relat_1(B_1352,C_1353))
      | ~ v1_relat_1(C_1353)
      | ~ v1_relat_1(B_1352)
      | ~ v1_relat_1(k5_relat_1(B_1352,C_1353)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_154618])).

tff(c_91,plain,(
    ! [B_41,C_42,A_43] :
      ( k10_relat_1(k5_relat_1(B_41,C_42),A_43) = k10_relat_1(B_41,k10_relat_1(C_42,A_43))
      | ~ v1_relat_1(C_42)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k10_relat_1(B_11,A_10),k1_relat_1(B_11))
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1037,plain,(
    ! [B_97,C_98,A_99] :
      ( r1_tarski(k10_relat_1(B_97,k10_relat_1(C_98,A_99)),k1_relat_1(k5_relat_1(B_97,C_98)))
      | ~ v1_relat_1(k5_relat_1(B_97,C_98))
      | ~ v1_relat_1(C_98)
      | ~ v1_relat_1(B_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_14])).

tff(c_4320,plain,(
    ! [B_197,A_198] :
      ( r1_tarski(k10_relat_1(B_197,k1_relat_1(A_198)),k1_relat_1(k5_relat_1(B_197,A_198)))
      | ~ v1_relat_1(k5_relat_1(B_197,A_198))
      | ~ v1_relat_1(A_198)
      | ~ v1_relat_1(B_197)
      | ~ v1_relat_1(A_198) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1037])).

tff(c_4327,plain,(
    ! [B_197,A_198] :
      ( k10_relat_1(B_197,k1_relat_1(A_198)) = k1_relat_1(k5_relat_1(B_197,A_198))
      | ~ r1_tarski(k1_relat_1(k5_relat_1(B_197,A_198)),k10_relat_1(B_197,k1_relat_1(A_198)))
      | ~ v1_relat_1(k5_relat_1(B_197,A_198))
      | ~ v1_relat_1(B_197)
      | ~ v1_relat_1(A_198) ) ),
    inference(resolution,[status(thm)],[c_4320,c_2])).

tff(c_166761,plain,(
    ! [B_1354,C_1355] :
      ( k10_relat_1(B_1354,k1_relat_1(C_1355)) = k1_relat_1(k5_relat_1(B_1354,C_1355))
      | ~ v1_relat_1(C_1355)
      | ~ v1_relat_1(B_1354)
      | ~ v1_relat_1(k5_relat_1(B_1354,C_1355)) ) ),
    inference(resolution,[status(thm)],[c_166712,c_4327])).

tff(c_166766,plain,(
    ! [A_1356,B_1357] :
      ( k10_relat_1(A_1356,k1_relat_1(B_1357)) = k1_relat_1(k5_relat_1(A_1356,B_1357))
      | ~ v1_relat_1(B_1357)
      | ~ v1_relat_1(A_1356) ) ),
    inference(resolution,[status(thm)],[c_12,c_166761])).

tff(c_22,plain,(
    k10_relat_1('#skF_1',k1_relat_1('#skF_2')) != k1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_167505,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_166766,c_22])).

tff(c_167519,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_167505])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:03:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 44.96/31.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 44.96/31.99  
% 44.96/31.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 44.96/31.99  %$ r1_tarski > v1_relat_1 > k5_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 44.96/31.99  
% 44.96/31.99  %Foreground sorts:
% 44.96/31.99  
% 44.96/31.99  
% 44.96/31.99  %Background operators:
% 44.96/31.99  
% 44.96/31.99  
% 44.96/31.99  %Foreground operators:
% 44.96/31.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 44.96/31.99  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 44.96/31.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 44.96/31.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 44.96/31.99  tff('#skF_2', type, '#skF_2': $i).
% 44.96/31.99  tff('#skF_1', type, '#skF_1': $i).
% 44.96/31.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 44.96/31.99  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 44.96/31.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 44.96/31.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 44.96/31.99  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 44.96/31.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 44.96/31.99  
% 44.96/32.01  tff(f_70, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 44.96/32.01  tff(f_43, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 44.96/32.01  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 44.96/32.01  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t181_relat_1)).
% 44.96/32.01  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_relat_1)).
% 44.96/32.01  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 44.96/32.01  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 44.96/32.01  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 44.96/32.01  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 44.96/32.01  tff(c_26, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 44.96/32.01  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 44.96/32.01  tff(c_12, plain, (![A_8, B_9]: (v1_relat_1(k5_relat_1(A_8, B_9)) | ~v1_relat_1(B_9) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 44.96/32.01  tff(c_16, plain, (![A_12]: (k10_relat_1(A_12, k2_relat_1(A_12))=k1_relat_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 44.96/32.01  tff(c_20, plain, (![B_17, C_19, A_16]: (k10_relat_1(k5_relat_1(B_17, C_19), A_16)=k10_relat_1(B_17, k10_relat_1(C_19, A_16)) | ~v1_relat_1(C_19) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 44.96/32.01  tff(c_114, plain, (![C_44, A_45, B_46]: (k2_xboole_0(k10_relat_1(C_44, A_45), k10_relat_1(C_44, B_46))=k10_relat_1(C_44, k2_xboole_0(A_45, B_46)) | ~v1_relat_1(C_44))), inference(cnfTransformation, [status(thm)], [f_55])).
% 44.96/32.01  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 44.96/32.01  tff(c_147, plain, (![C_47, A_48, B_49]: (r1_tarski(k10_relat_1(C_47, A_48), k10_relat_1(C_47, k2_xboole_0(A_48, B_49))) | ~v1_relat_1(C_47))), inference(superposition, [status(thm), theory('equality')], [c_114, c_10])).
% 44.96/32.01  tff(c_159, plain, (![B_17, C_19, A_48, B_49]: (r1_tarski(k10_relat_1(k5_relat_1(B_17, C_19), A_48), k10_relat_1(B_17, k10_relat_1(C_19, k2_xboole_0(A_48, B_49)))) | ~v1_relat_1(k5_relat_1(B_17, C_19)) | ~v1_relat_1(C_19) | ~v1_relat_1(B_17))), inference(superposition, [status(thm), theory('equality')], [c_20, c_147])).
% 44.96/32.01  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 44.96/32.01  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 44.96/32.01  tff(c_218, plain, (![A_54, C_55, A_56, B_57]: (r1_tarski(A_54, k10_relat_1(C_55, k2_xboole_0(A_56, B_57))) | ~r1_tarski(A_54, k10_relat_1(C_55, B_57)) | ~v1_relat_1(C_55))), inference(superposition, [status(thm), theory('equality')], [c_114, c_8])).
% 44.96/32.01  tff(c_54, plain, (![B_32, A_33]: (r1_tarski(k10_relat_1(B_32, A_33), k1_relat_1(B_32)) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_47])).
% 44.96/32.01  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 44.96/32.01  tff(c_60, plain, (![B_32, A_33]: (k10_relat_1(B_32, A_33)=k1_relat_1(B_32) | ~r1_tarski(k1_relat_1(B_32), k10_relat_1(B_32, A_33)) | ~v1_relat_1(B_32))), inference(resolution, [status(thm)], [c_54, c_2])).
% 44.96/32.01  tff(c_289, plain, (![C_64, A_65, B_66]: (k10_relat_1(C_64, k2_xboole_0(A_65, B_66))=k1_relat_1(C_64) | ~r1_tarski(k1_relat_1(C_64), k10_relat_1(C_64, B_66)) | ~v1_relat_1(C_64))), inference(resolution, [status(thm)], [c_218, c_60])).
% 44.96/32.01  tff(c_300, plain, (![A_12, A_65]: (k10_relat_1(A_12, k2_xboole_0(A_65, k2_relat_1(A_12)))=k1_relat_1(A_12) | ~r1_tarski(k1_relat_1(A_12), k1_relat_1(A_12)) | ~v1_relat_1(A_12) | ~v1_relat_1(A_12))), inference(superposition, [status(thm), theory('equality')], [c_16, c_289])).
% 44.96/32.01  tff(c_307, plain, (![A_67, A_68]: (k10_relat_1(A_67, k2_xboole_0(A_68, k2_relat_1(A_67)))=k1_relat_1(A_67) | ~v1_relat_1(A_67))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_300])).
% 44.96/32.01  tff(c_18, plain, (![C_15, A_13, B_14]: (k2_xboole_0(k10_relat_1(C_15, A_13), k10_relat_1(C_15, B_14))=k10_relat_1(C_15, k2_xboole_0(A_13, B_14)) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 44.96/32.01  tff(c_4525, plain, (![A_205, A_206, B_207]: (k10_relat_1(A_205, k2_xboole_0(k2_xboole_0(A_206, k2_relat_1(A_205)), B_207))=k2_xboole_0(k1_relat_1(A_205), k10_relat_1(A_205, B_207)) | ~v1_relat_1(A_205) | ~v1_relat_1(A_205))), inference(superposition, [status(thm), theory('equality')], [c_307, c_18])).
% 44.96/32.01  tff(c_164, plain, (![A_50, B_51]: (r1_tarski(k1_relat_1(A_50), k10_relat_1(A_50, k2_xboole_0(k2_relat_1(A_50), B_51))) | ~v1_relat_1(A_50) | ~v1_relat_1(A_50))), inference(superposition, [status(thm), theory('equality')], [c_16, c_147])).
% 44.96/32.01  tff(c_176, plain, (![A_52, B_53]: (k10_relat_1(A_52, k2_xboole_0(k2_relat_1(A_52), B_53))=k1_relat_1(A_52) | ~v1_relat_1(A_52))), inference(resolution, [status(thm)], [c_164, c_60])).
% 44.96/32.01  tff(c_129, plain, (![C_44, A_45, B_46]: (r1_tarski(k10_relat_1(C_44, A_45), k10_relat_1(C_44, k2_xboole_0(A_45, B_46))) | ~v1_relat_1(C_44))), inference(superposition, [status(thm), theory('equality')], [c_114, c_10])).
% 44.96/32.01  tff(c_1075, plain, (![A_100, B_101, B_102]: (r1_tarski(k1_relat_1(A_100), k10_relat_1(A_100, k2_xboole_0(k2_xboole_0(k2_relat_1(A_100), B_101), B_102))) | ~v1_relat_1(A_100) | ~v1_relat_1(A_100))), inference(superposition, [status(thm), theory('equality')], [c_176, c_129])).
% 44.96/32.01  tff(c_1121, plain, (![A_100, B_101, B_102]: (k10_relat_1(A_100, k2_xboole_0(k2_xboole_0(k2_relat_1(A_100), B_101), B_102))=k1_relat_1(A_100) | ~v1_relat_1(A_100))), inference(resolution, [status(thm)], [c_1075, c_60])).
% 44.96/32.01  tff(c_5014, plain, (![A_212, B_213]: (k2_xboole_0(k1_relat_1(A_212), k10_relat_1(A_212, B_213))=k1_relat_1(A_212) | ~v1_relat_1(A_212) | ~v1_relat_1(A_212) | ~v1_relat_1(A_212))), inference(superposition, [status(thm), theory('equality')], [c_4525, c_1121])).
% 44.96/32.01  tff(c_32, plain, (![B_29, A_30]: (B_29=A_30 | ~r1_tarski(B_29, A_30) | ~r1_tarski(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 44.96/32.01  tff(c_40, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(k2_xboole_0(A_6, B_7), A_6))), inference(resolution, [status(thm)], [c_10, c_32])).
% 44.96/32.01  tff(c_5046, plain, (![A_212, B_213]: (k2_xboole_0(k1_relat_1(A_212), k10_relat_1(A_212, B_213))=k1_relat_1(A_212) | ~r1_tarski(k1_relat_1(A_212), k1_relat_1(A_212)) | ~v1_relat_1(A_212) | ~v1_relat_1(A_212) | ~v1_relat_1(A_212))), inference(superposition, [status(thm), theory('equality')], [c_5014, c_40])).
% 44.96/32.01  tff(c_5140, plain, (![A_214, B_215]: (k2_xboole_0(k1_relat_1(A_214), k10_relat_1(A_214, B_215))=k1_relat_1(A_214) | ~v1_relat_1(A_214))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_5046])).
% 44.96/32.01  tff(c_126, plain, (![A_3, C_44, A_45, B_46]: (r1_tarski(A_3, k10_relat_1(C_44, k2_xboole_0(A_45, B_46))) | ~r1_tarski(A_3, k10_relat_1(C_44, B_46)) | ~v1_relat_1(C_44))), inference(superposition, [status(thm), theory('equality')], [c_114, c_8])).
% 44.96/32.01  tff(c_71502, plain, (![A_820, C_821, A_822, B_823]: (r1_tarski(A_820, k10_relat_1(C_821, k1_relat_1(A_822))) | ~r1_tarski(A_820, k10_relat_1(C_821, k10_relat_1(A_822, B_823))) | ~v1_relat_1(C_821) | ~v1_relat_1(A_822))), inference(superposition, [status(thm), theory('equality')], [c_5140, c_126])).
% 44.96/32.01  tff(c_154618, plain, (![B_1285, C_1286, A_1287]: (r1_tarski(k10_relat_1(k5_relat_1(B_1285, C_1286), A_1287), k10_relat_1(B_1285, k1_relat_1(C_1286))) | ~v1_relat_1(k5_relat_1(B_1285, C_1286)) | ~v1_relat_1(C_1286) | ~v1_relat_1(B_1285))), inference(resolution, [status(thm)], [c_159, c_71502])).
% 44.96/32.01  tff(c_166712, plain, (![B_1352, C_1353]: (r1_tarski(k1_relat_1(k5_relat_1(B_1352, C_1353)), k10_relat_1(B_1352, k1_relat_1(C_1353))) | ~v1_relat_1(k5_relat_1(B_1352, C_1353)) | ~v1_relat_1(C_1353) | ~v1_relat_1(B_1352) | ~v1_relat_1(k5_relat_1(B_1352, C_1353)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_154618])).
% 44.96/32.01  tff(c_91, plain, (![B_41, C_42, A_43]: (k10_relat_1(k5_relat_1(B_41, C_42), A_43)=k10_relat_1(B_41, k10_relat_1(C_42, A_43)) | ~v1_relat_1(C_42) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_62])).
% 44.96/32.01  tff(c_14, plain, (![B_11, A_10]: (r1_tarski(k10_relat_1(B_11, A_10), k1_relat_1(B_11)) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 44.96/32.01  tff(c_1037, plain, (![B_97, C_98, A_99]: (r1_tarski(k10_relat_1(B_97, k10_relat_1(C_98, A_99)), k1_relat_1(k5_relat_1(B_97, C_98))) | ~v1_relat_1(k5_relat_1(B_97, C_98)) | ~v1_relat_1(C_98) | ~v1_relat_1(B_97))), inference(superposition, [status(thm), theory('equality')], [c_91, c_14])).
% 44.96/32.01  tff(c_4320, plain, (![B_197, A_198]: (r1_tarski(k10_relat_1(B_197, k1_relat_1(A_198)), k1_relat_1(k5_relat_1(B_197, A_198))) | ~v1_relat_1(k5_relat_1(B_197, A_198)) | ~v1_relat_1(A_198) | ~v1_relat_1(B_197) | ~v1_relat_1(A_198))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1037])).
% 44.96/32.01  tff(c_4327, plain, (![B_197, A_198]: (k10_relat_1(B_197, k1_relat_1(A_198))=k1_relat_1(k5_relat_1(B_197, A_198)) | ~r1_tarski(k1_relat_1(k5_relat_1(B_197, A_198)), k10_relat_1(B_197, k1_relat_1(A_198))) | ~v1_relat_1(k5_relat_1(B_197, A_198)) | ~v1_relat_1(B_197) | ~v1_relat_1(A_198))), inference(resolution, [status(thm)], [c_4320, c_2])).
% 44.96/32.01  tff(c_166761, plain, (![B_1354, C_1355]: (k10_relat_1(B_1354, k1_relat_1(C_1355))=k1_relat_1(k5_relat_1(B_1354, C_1355)) | ~v1_relat_1(C_1355) | ~v1_relat_1(B_1354) | ~v1_relat_1(k5_relat_1(B_1354, C_1355)))), inference(resolution, [status(thm)], [c_166712, c_4327])).
% 44.96/32.01  tff(c_166766, plain, (![A_1356, B_1357]: (k10_relat_1(A_1356, k1_relat_1(B_1357))=k1_relat_1(k5_relat_1(A_1356, B_1357)) | ~v1_relat_1(B_1357) | ~v1_relat_1(A_1356))), inference(resolution, [status(thm)], [c_12, c_166761])).
% 44.96/32.01  tff(c_22, plain, (k10_relat_1('#skF_1', k1_relat_1('#skF_2'))!=k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 44.96/32.01  tff(c_167505, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_166766, c_22])).
% 44.96/32.01  tff(c_167519, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_167505])).
% 44.96/32.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 44.96/32.01  
% 44.96/32.01  Inference rules
% 44.96/32.01  ----------------------
% 44.96/32.01  #Ref     : 0
% 44.96/32.01  #Sup     : 50660
% 44.96/32.01  #Fact    : 0
% 44.96/32.01  #Define  : 0
% 44.96/32.01  #Split   : 0
% 44.96/32.01  #Chain   : 0
% 44.96/32.01  #Close   : 0
% 44.96/32.01  
% 44.96/32.01  Ordering : KBO
% 44.96/32.01  
% 44.96/32.01  Simplification rules
% 44.96/32.01  ----------------------
% 44.96/32.01  #Subsume      : 22373
% 44.96/32.01  #Demod        : 2028
% 44.96/32.01  #Tautology    : 3297
% 44.96/32.01  #SimpNegUnit  : 0
% 44.96/32.01  #BackRed      : 0
% 44.96/32.01  
% 44.96/32.01  #Partial instantiations: 0
% 44.96/32.01  #Strategies tried      : 1
% 44.96/32.01  
% 44.96/32.01  Timing (in seconds)
% 44.96/32.01  ----------------------
% 44.96/32.01  Preprocessing        : 0.31
% 44.96/32.01  Parsing              : 0.17
% 44.96/32.01  CNF conversion       : 0.02
% 44.96/32.01  Main loop            : 30.86
% 44.96/32.01  Inferencing          : 6.52
% 44.96/32.01  Reduction            : 3.84
% 44.96/32.01  Demodulation         : 2.46
% 44.96/32.01  BG Simplification    : 1.02
% 44.96/32.01  Subsumption          : 18.02
% 44.96/32.01  Abstraction          : 1.33
% 44.96/32.01  MUC search           : 0.00
% 44.96/32.01  Cooper               : 0.00
% 44.96/32.01  Total                : 31.21
% 44.96/32.01  Index Insertion      : 0.00
% 44.96/32.01  Index Deletion       : 0.00
% 44.96/32.01  Index Matching       : 0.00
% 44.96/32.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
