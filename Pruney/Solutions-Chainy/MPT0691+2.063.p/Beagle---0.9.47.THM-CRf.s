%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:47 EST 2020

% Result     : Theorem 5.84s
% Output     : CNFRefutation 5.84s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 260 expanded)
%              Number of leaves         :   32 (  99 expanded)
%              Depth                    :   20
%              Number of atoms          :  124 ( 503 expanded)
%              Number of equality atoms :   39 ( 123 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_36,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_81,plain,(
    k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_36])).

tff(c_40,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_18,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( v1_relat_1(k7_relat_1(A_15,B_16))
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_34,plain,(
    ! [A_27,C_29,B_28] :
      ( k3_xboole_0(A_27,k10_relat_1(C_29,B_28)) = k10_relat_1(k7_relat_1(C_29,A_27),B_28)
      | ~ v1_relat_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ! [A_21] :
      ( k10_relat_1(A_21,k2_relat_1(A_21)) = k1_relat_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_424,plain,(
    ! [C_73,A_74,B_75] :
      ( r1_tarski(k10_relat_1(C_73,A_74),k10_relat_1(C_73,B_75))
      | ~ r1_tarski(A_74,B_75)
      | ~ v1_relat_1(C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1799,plain,(
    ! [A_170,B_171] :
      ( r1_tarski(k1_relat_1(A_170),k10_relat_1(A_170,B_171))
      | ~ r1_tarski(k2_relat_1(A_170),B_171)
      | ~ v1_relat_1(A_170)
      | ~ v1_relat_1(A_170) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_424])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1913,plain,(
    ! [A_178,B_179] :
      ( k4_xboole_0(k1_relat_1(A_178),k10_relat_1(A_178,B_179)) = k1_xboole_0
      | ~ r1_tarski(k2_relat_1(A_178),B_179)
      | ~ v1_relat_1(A_178) ) ),
    inference(resolution,[status(thm)],[c_1799,c_10])).

tff(c_38,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_198,plain,(
    ! [A_55,C_56,B_57] :
      ( r1_tarski(A_55,C_56)
      | ~ r1_tarski(B_57,C_56)
      | ~ r1_tarski(A_55,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_405,plain,(
    ! [A_70,B_71,A_72] :
      ( r1_tarski(A_70,B_71)
      | ~ r1_tarski(A_70,A_72)
      | k4_xboole_0(A_72,B_71) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_198])).

tff(c_422,plain,(
    ! [B_71] :
      ( r1_tarski('#skF_1',B_71)
      | k4_xboole_0(k1_relat_1('#skF_2'),B_71) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_38,c_405])).

tff(c_1948,plain,(
    ! [B_179] :
      ( r1_tarski('#skF_1',k10_relat_1('#skF_2',B_179))
      | ~ r1_tarski(k2_relat_1('#skF_2'),B_179)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1913,c_422])).

tff(c_1993,plain,(
    ! [B_180] :
      ( r1_tarski('#skF_1',k10_relat_1('#skF_2',B_180))
      | ~ r1_tarski(k2_relat_1('#skF_2'),B_180) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1948])).

tff(c_2013,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k2_relat_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_6,c_1993])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2051,plain,(
    k3_xboole_0('#skF_1',k10_relat_1('#skF_2',k2_relat_1('#skF_2'))) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2013,c_16])).

tff(c_2092,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1('#skF_2')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2051])).

tff(c_2102,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2092])).

tff(c_26,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k10_relat_1(B_20,A_19),k1_relat_1(B_20))
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2260,plain,
    ( r1_tarski('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2102,c_26])).

tff(c_2921,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_2260])).

tff(c_2989,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_2921])).

tff(c_2993,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2989])).

tff(c_2995,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_2260])).

tff(c_52,plain,(
    ! [A_36,B_37] :
      ( k3_xboole_0(A_36,B_37) = A_36
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_64,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_52])).

tff(c_2994,plain,(
    r1_tarski('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_2260])).

tff(c_32,plain,(
    ! [B_26,A_25] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_26,A_25)),A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_133,plain,(
    ! [B_48,A_49] :
      ( B_48 = A_49
      | ~ r1_tarski(B_48,A_49)
      | ~ r1_tarski(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_145,plain,(
    ! [B_26,A_25] :
      ( k1_relat_1(k7_relat_1(B_26,A_25)) = A_25
      | ~ r1_tarski(A_25,k1_relat_1(k7_relat_1(B_26,A_25)))
      | ~ v1_relat_1(B_26) ) ),
    inference(resolution,[status(thm)],[c_32,c_133])).

tff(c_2998,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2994,c_145])).

tff(c_3023,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2998])).

tff(c_214,plain,(
    ! [B_58,A_59] :
      ( k2_relat_1(k7_relat_1(B_58,A_59)) = k9_relat_1(B_58,A_59)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_220,plain,(
    ! [B_58,A_59] :
      ( k10_relat_1(k7_relat_1(B_58,A_59),k9_relat_1(B_58,A_59)) = k1_relat_1(k7_relat_1(B_58,A_59))
      | ~ v1_relat_1(k7_relat_1(B_58,A_59))
      | ~ v1_relat_1(B_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_28])).

tff(c_124,plain,(
    ! [B_46,A_47] :
      ( r1_tarski(k10_relat_1(B_46,A_47),k1_relat_1(B_46))
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_132,plain,(
    ! [B_46,A_47] :
      ( k3_xboole_0(k10_relat_1(B_46,A_47),k1_relat_1(B_46)) = k10_relat_1(B_46,A_47)
      | ~ v1_relat_1(B_46) ) ),
    inference(resolution,[status(thm)],[c_124,c_16])).

tff(c_3086,plain,(
    ! [A_47] :
      ( k3_xboole_0(k10_relat_1(k7_relat_1('#skF_2','#skF_1'),A_47),'#skF_1') = k10_relat_1(k7_relat_1('#skF_2','#skF_1'),A_47)
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3023,c_132])).

tff(c_5247,plain,(
    ! [A_251] : k3_xboole_0(k10_relat_1(k7_relat_1('#skF_2','#skF_1'),A_251),'#skF_1') = k10_relat_1(k7_relat_1('#skF_2','#skF_1'),A_251) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2995,c_3086])).

tff(c_5264,plain,
    ( k3_xboole_0(k1_relat_1(k7_relat_1('#skF_2','#skF_1')),'#skF_1') = k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_5247])).

tff(c_5286,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2995,c_64,c_3023,c_5264])).

tff(c_639,plain,(
    ! [A_94,C_95,B_96] :
      ( k3_xboole_0(A_94,k10_relat_1(C_95,B_96)) = k10_relat_1(k7_relat_1(C_95,A_94),B_96)
      | ~ v1_relat_1(C_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_12,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_645,plain,(
    ! [A_94,C_95,B_96] :
      ( k5_xboole_0(A_94,k10_relat_1(k7_relat_1(C_95,A_94),B_96)) = k4_xboole_0(A_94,k10_relat_1(C_95,B_96))
      | ~ v1_relat_1(C_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_639,c_12])).

tff(c_5365,plain,
    ( k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = k5_xboole_0('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5286,c_645])).

tff(c_5458,plain,(
    k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_18,c_5365])).

tff(c_5460,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_5458])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:39:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.84/2.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.84/2.14  
% 5.84/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.84/2.14  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 5.84/2.14  
% 5.84/2.14  %Foreground sorts:
% 5.84/2.14  
% 5.84/2.14  
% 5.84/2.14  %Background operators:
% 5.84/2.14  
% 5.84/2.14  
% 5.84/2.14  %Foreground operators:
% 5.84/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.84/2.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.84/2.14  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.84/2.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.84/2.14  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.84/2.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.84/2.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.84/2.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.84/2.14  tff('#skF_2', type, '#skF_2': $i).
% 5.84/2.14  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.84/2.14  tff('#skF_1', type, '#skF_1': $i).
% 5.84/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.84/2.14  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.84/2.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.84/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.84/2.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.84/2.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.84/2.14  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.84/2.14  
% 5.84/2.15  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.84/2.15  tff(f_88, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 5.84/2.15  tff(f_49, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.84/2.15  tff(f_55, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 5.84/2.15  tff(f_81, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 5.84/2.15  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.84/2.15  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 5.84/2.15  tff(f_73, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_relat_1)).
% 5.84/2.15  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.84/2.15  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.84/2.15  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 5.84/2.15  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 5.84/2.15  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 5.84/2.15  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.84/2.15  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.84/2.15  tff(c_36, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.84/2.15  tff(c_81, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_36])).
% 5.84/2.15  tff(c_40, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.84/2.15  tff(c_18, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.84/2.15  tff(c_22, plain, (![A_15, B_16]: (v1_relat_1(k7_relat_1(A_15, B_16)) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.84/2.15  tff(c_34, plain, (![A_27, C_29, B_28]: (k3_xboole_0(A_27, k10_relat_1(C_29, B_28))=k10_relat_1(k7_relat_1(C_29, A_27), B_28) | ~v1_relat_1(C_29))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.84/2.15  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.84/2.15  tff(c_28, plain, (![A_21]: (k10_relat_1(A_21, k2_relat_1(A_21))=k1_relat_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.84/2.15  tff(c_424, plain, (![C_73, A_74, B_75]: (r1_tarski(k10_relat_1(C_73, A_74), k10_relat_1(C_73, B_75)) | ~r1_tarski(A_74, B_75) | ~v1_relat_1(C_73))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.84/2.15  tff(c_1799, plain, (![A_170, B_171]: (r1_tarski(k1_relat_1(A_170), k10_relat_1(A_170, B_171)) | ~r1_tarski(k2_relat_1(A_170), B_171) | ~v1_relat_1(A_170) | ~v1_relat_1(A_170))), inference(superposition, [status(thm), theory('equality')], [c_28, c_424])).
% 5.84/2.15  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.84/2.15  tff(c_1913, plain, (![A_178, B_179]: (k4_xboole_0(k1_relat_1(A_178), k10_relat_1(A_178, B_179))=k1_xboole_0 | ~r1_tarski(k2_relat_1(A_178), B_179) | ~v1_relat_1(A_178))), inference(resolution, [status(thm)], [c_1799, c_10])).
% 5.84/2.15  tff(c_38, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.84/2.15  tff(c_198, plain, (![A_55, C_56, B_57]: (r1_tarski(A_55, C_56) | ~r1_tarski(B_57, C_56) | ~r1_tarski(A_55, B_57))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.84/2.15  tff(c_405, plain, (![A_70, B_71, A_72]: (r1_tarski(A_70, B_71) | ~r1_tarski(A_70, A_72) | k4_xboole_0(A_72, B_71)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_198])).
% 5.84/2.15  tff(c_422, plain, (![B_71]: (r1_tarski('#skF_1', B_71) | k4_xboole_0(k1_relat_1('#skF_2'), B_71)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_405])).
% 5.84/2.15  tff(c_1948, plain, (![B_179]: (r1_tarski('#skF_1', k10_relat_1('#skF_2', B_179)) | ~r1_tarski(k2_relat_1('#skF_2'), B_179) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1913, c_422])).
% 5.84/2.15  tff(c_1993, plain, (![B_180]: (r1_tarski('#skF_1', k10_relat_1('#skF_2', B_180)) | ~r1_tarski(k2_relat_1('#skF_2'), B_180))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1948])).
% 5.84/2.15  tff(c_2013, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k2_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_6, c_1993])).
% 5.84/2.15  tff(c_16, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.84/2.15  tff(c_2051, plain, (k3_xboole_0('#skF_1', k10_relat_1('#skF_2', k2_relat_1('#skF_2')))='#skF_1'), inference(resolution, [status(thm)], [c_2013, c_16])).
% 5.84/2.15  tff(c_2092, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1('#skF_2'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_34, c_2051])).
% 5.84/2.15  tff(c_2102, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2092])).
% 5.84/2.15  tff(c_26, plain, (![B_20, A_19]: (r1_tarski(k10_relat_1(B_20, A_19), k1_relat_1(B_20)) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.84/2.15  tff(c_2260, plain, (r1_tarski('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2102, c_26])).
% 5.84/2.15  tff(c_2921, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_2260])).
% 5.84/2.15  tff(c_2989, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_22, c_2921])).
% 5.84/2.15  tff(c_2993, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_2989])).
% 5.84/2.15  tff(c_2995, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_2260])).
% 5.84/2.15  tff(c_52, plain, (![A_36, B_37]: (k3_xboole_0(A_36, B_37)=A_36 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.84/2.15  tff(c_64, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_52])).
% 5.84/2.15  tff(c_2994, plain, (r1_tarski('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_2260])).
% 5.84/2.15  tff(c_32, plain, (![B_26, A_25]: (r1_tarski(k1_relat_1(k7_relat_1(B_26, A_25)), A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.84/2.15  tff(c_133, plain, (![B_48, A_49]: (B_48=A_49 | ~r1_tarski(B_48, A_49) | ~r1_tarski(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.84/2.15  tff(c_145, plain, (![B_26, A_25]: (k1_relat_1(k7_relat_1(B_26, A_25))=A_25 | ~r1_tarski(A_25, k1_relat_1(k7_relat_1(B_26, A_25))) | ~v1_relat_1(B_26))), inference(resolution, [status(thm)], [c_32, c_133])).
% 5.84/2.15  tff(c_2998, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2994, c_145])).
% 5.84/2.15  tff(c_3023, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2998])).
% 5.84/2.15  tff(c_214, plain, (![B_58, A_59]: (k2_relat_1(k7_relat_1(B_58, A_59))=k9_relat_1(B_58, A_59) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.84/2.15  tff(c_220, plain, (![B_58, A_59]: (k10_relat_1(k7_relat_1(B_58, A_59), k9_relat_1(B_58, A_59))=k1_relat_1(k7_relat_1(B_58, A_59)) | ~v1_relat_1(k7_relat_1(B_58, A_59)) | ~v1_relat_1(B_58))), inference(superposition, [status(thm), theory('equality')], [c_214, c_28])).
% 5.84/2.15  tff(c_124, plain, (![B_46, A_47]: (r1_tarski(k10_relat_1(B_46, A_47), k1_relat_1(B_46)) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.84/2.15  tff(c_132, plain, (![B_46, A_47]: (k3_xboole_0(k10_relat_1(B_46, A_47), k1_relat_1(B_46))=k10_relat_1(B_46, A_47) | ~v1_relat_1(B_46))), inference(resolution, [status(thm)], [c_124, c_16])).
% 5.84/2.15  tff(c_3086, plain, (![A_47]: (k3_xboole_0(k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_47), '#skF_1')=k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_47) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_3023, c_132])).
% 5.84/2.15  tff(c_5247, plain, (![A_251]: (k3_xboole_0(k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_251), '#skF_1')=k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_251))), inference(demodulation, [status(thm), theory('equality')], [c_2995, c_3086])).
% 5.84/2.15  tff(c_5264, plain, (k3_xboole_0(k1_relat_1(k7_relat_1('#skF_2', '#skF_1')), '#skF_1')=k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_220, c_5247])).
% 5.84/2.15  tff(c_5286, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2995, c_64, c_3023, c_5264])).
% 5.84/2.15  tff(c_639, plain, (![A_94, C_95, B_96]: (k3_xboole_0(A_94, k10_relat_1(C_95, B_96))=k10_relat_1(k7_relat_1(C_95, A_94), B_96) | ~v1_relat_1(C_95))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.84/2.15  tff(c_12, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.84/2.15  tff(c_645, plain, (![A_94, C_95, B_96]: (k5_xboole_0(A_94, k10_relat_1(k7_relat_1(C_95, A_94), B_96))=k4_xboole_0(A_94, k10_relat_1(C_95, B_96)) | ~v1_relat_1(C_95))), inference(superposition, [status(thm), theory('equality')], [c_639, c_12])).
% 5.84/2.15  tff(c_5365, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))=k5_xboole_0('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5286, c_645])).
% 5.84/2.15  tff(c_5458, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_18, c_5365])).
% 5.84/2.15  tff(c_5460, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_5458])).
% 5.84/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.84/2.15  
% 5.84/2.15  Inference rules
% 5.84/2.15  ----------------------
% 5.84/2.15  #Ref     : 0
% 5.84/2.15  #Sup     : 1279
% 5.84/2.15  #Fact    : 0
% 5.84/2.15  #Define  : 0
% 5.84/2.15  #Split   : 4
% 5.84/2.15  #Chain   : 0
% 5.84/2.15  #Close   : 0
% 5.84/2.16  
% 5.84/2.16  Ordering : KBO
% 5.84/2.16  
% 5.84/2.16  Simplification rules
% 5.84/2.16  ----------------------
% 5.84/2.16  #Subsume      : 310
% 5.84/2.16  #Demod        : 637
% 5.84/2.16  #Tautology    : 404
% 5.84/2.16  #SimpNegUnit  : 1
% 5.84/2.16  #BackRed      : 1
% 5.84/2.16  
% 5.84/2.16  #Partial instantiations: 0
% 5.84/2.16  #Strategies tried      : 1
% 5.84/2.16  
% 5.84/2.16  Timing (in seconds)
% 5.84/2.16  ----------------------
% 5.84/2.16  Preprocessing        : 0.31
% 5.84/2.16  Parsing              : 0.16
% 5.84/2.16  CNF conversion       : 0.02
% 5.84/2.16  Main loop            : 1.08
% 5.84/2.16  Inferencing          : 0.34
% 5.84/2.16  Reduction            : 0.33
% 5.84/2.16  Demodulation         : 0.23
% 5.84/2.16  BG Simplification    : 0.04
% 5.84/2.16  Subsumption          : 0.29
% 5.84/2.16  Abstraction          : 0.05
% 5.84/2.16  MUC search           : 0.00
% 5.84/2.16  Cooper               : 0.00
% 5.84/2.16  Total                : 1.42
% 5.84/2.16  Index Insertion      : 0.00
% 5.84/2.16  Index Deletion       : 0.00
% 5.84/2.16  Index Matching       : 0.00
% 5.84/2.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
