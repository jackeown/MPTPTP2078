%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:10 EST 2020

% Result     : Theorem 44.31s
% Output     : CNFRefutation 44.31s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 136 expanded)
%              Number of leaves         :   35 (  64 expanded)
%              Depth                    :   17
%              Number of atoms          :  143 ( 267 expanded)
%              Number of equality atoms :   20 (  46 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_127,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_77,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_116,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(c_50,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_18,plain,(
    ! [A_14] :
      ( k9_relat_1(A_14,k1_relat_1(A_14)) = k2_relat_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_9759,plain,(
    ! [C_312,A_313,B_314] :
      ( r1_tarski(k9_relat_1(C_312,A_313),k9_relat_1(C_312,B_314))
      | ~ r1_tarski(A_313,B_314)
      | ~ v1_relat_1(C_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_9780,plain,(
    ! [A_14,B_314] :
      ( r1_tarski(k2_relat_1(A_14),k9_relat_1(A_14,B_314))
      | ~ r1_tarski(k1_relat_1(A_14),B_314)
      | ~ v1_relat_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_9759])).

tff(c_32,plain,(
    ! [A_27] : v1_relat_1(k6_relat_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_28,plain,(
    ! [A_26] : k1_relat_1(k6_relat_1(A_26)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_151,plain,(
    ! [B_54,A_55] :
      ( r1_tarski(k10_relat_1(B_54,A_55),k1_relat_1(B_54))
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_160,plain,(
    ! [A_26,A_55] :
      ( r1_tarski(k10_relat_1(k6_relat_1(A_26),A_55),A_26)
      | ~ v1_relat_1(k6_relat_1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_151])).

tff(c_164,plain,(
    ! [A_26,A_55] : r1_tarski(k10_relat_1(k6_relat_1(A_26),A_55),A_26) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_160])).

tff(c_30,plain,(
    ! [A_26] : k2_relat_1(k6_relat_1(A_26)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_187,plain,(
    ! [A_60] :
      ( k9_relat_1(A_60,k1_relat_1(A_60)) = k2_relat_1(A_60)
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_196,plain,(
    ! [A_26] :
      ( k9_relat_1(k6_relat_1(A_26),A_26) = k2_relat_1(k6_relat_1(A_26))
      | ~ v1_relat_1(k6_relat_1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_187])).

tff(c_200,plain,(
    ! [A_26] : k9_relat_1(k6_relat_1(A_26),A_26) = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_196])).

tff(c_10240,plain,(
    ! [A_335,B_336] :
      ( r1_tarski(A_335,k10_relat_1(B_336,k9_relat_1(B_336,A_335)))
      | ~ r1_tarski(A_335,k1_relat_1(B_336))
      | ~ v1_relat_1(B_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_10263,plain,(
    ! [A_26] :
      ( r1_tarski(A_26,k10_relat_1(k6_relat_1(A_26),A_26))
      | ~ r1_tarski(A_26,k1_relat_1(k6_relat_1(A_26)))
      | ~ v1_relat_1(k6_relat_1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_10240])).

tff(c_10280,plain,(
    ! [A_337] : r1_tarski(A_337,k10_relat_1(k6_relat_1(A_337),A_337)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_6,c_28,c_10263])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10293,plain,(
    ! [A_337] :
      ( k10_relat_1(k6_relat_1(A_337),A_337) = A_337
      | ~ r1_tarski(k10_relat_1(k6_relat_1(A_337),A_337),A_337) ) ),
    inference(resolution,[status(thm)],[c_10280,c_2])).

tff(c_10311,plain,(
    ! [A_337] : k10_relat_1(k6_relat_1(A_337),A_337) = A_337 ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_10293])).

tff(c_52,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(B_6,C_7)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_30515,plain,(
    ! [A_638,B_639,A_640] :
      ( r1_tarski(A_638,k10_relat_1(B_639,k9_relat_1(B_639,A_640)))
      | ~ r1_tarski(A_638,A_640)
      | ~ r1_tarski(A_640,k1_relat_1(B_639))
      | ~ v1_relat_1(B_639) ) ),
    inference(resolution,[status(thm)],[c_10240,c_10])).

tff(c_194037,plain,(
    ! [A_1490,B_1491,A_1492,A_1493] :
      ( r1_tarski(A_1490,k10_relat_1(B_1491,k9_relat_1(B_1491,A_1492)))
      | ~ r1_tarski(A_1490,A_1493)
      | ~ r1_tarski(A_1493,A_1492)
      | ~ r1_tarski(A_1492,k1_relat_1(B_1491))
      | ~ v1_relat_1(B_1491) ) ),
    inference(resolution,[status(thm)],[c_30515,c_10])).

tff(c_195569,plain,(
    ! [B_1498,A_1499] :
      ( r1_tarski('#skF_2',k10_relat_1(B_1498,k9_relat_1(B_1498,A_1499)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_1499)
      | ~ r1_tarski(A_1499,k1_relat_1(B_1498))
      | ~ v1_relat_1(B_1498) ) ),
    inference(resolution,[status(thm)],[c_52,c_194037])).

tff(c_195723,plain,(
    ! [A_26] :
      ( r1_tarski('#skF_2',k10_relat_1(k6_relat_1(A_26),A_26))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_26)
      | ~ r1_tarski(A_26,k1_relat_1(k6_relat_1(A_26)))
      | ~ v1_relat_1(k6_relat_1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_195569])).

tff(c_195824,plain,(
    ! [A_1500] :
      ( r1_tarski('#skF_2',A_1500)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_1500) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_6,c_28,c_10311,c_195723])).

tff(c_195892,plain,(
    ! [B_314] :
      ( r1_tarski('#skF_2',k9_relat_1('#skF_4',B_314))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_314)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_9780,c_195824])).

tff(c_196085,plain,(
    ! [B_1502] :
      ( r1_tarski('#skF_2',k9_relat_1('#skF_4',B_1502))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_1502) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_195892])).

tff(c_196209,plain,(
    r1_tarski('#skF_2',k9_relat_1('#skF_4',k1_relat_1('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_6,c_196085])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_196278,plain,(
    k3_xboole_0('#skF_2',k9_relat_1('#skF_4',k1_relat_1('#skF_4'))) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_196209,c_12])).

tff(c_48,plain,(
    ! [A_37,B_38] :
      ( k3_xboole_0(A_37,k9_relat_1(B_38,k1_relat_1(B_38))) = k9_relat_1(B_38,k10_relat_1(B_38,A_37))
      | ~ v1_funct_1(B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_197457,plain,
    ( k9_relat_1('#skF_4',k10_relat_1('#skF_4','#skF_2')) = '#skF_2'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_196278,c_48])).

tff(c_197540,plain,(
    k9_relat_1('#skF_4',k10_relat_1('#skF_4','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_197457])).

tff(c_54,plain,(
    r1_tarski(k10_relat_1('#skF_4','#skF_2'),k10_relat_1('#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_20,plain,(
    ! [C_17,A_15,B_16] :
      ( r1_tarski(k9_relat_1(C_17,A_15),k9_relat_1(C_17,B_16))
      | ~ r1_tarski(A_15,B_16)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_25417,plain,(
    ! [A_578,C_579,B_580,A_581] :
      ( r1_tarski(A_578,k9_relat_1(C_579,B_580))
      | ~ r1_tarski(A_578,k9_relat_1(C_579,A_581))
      | ~ r1_tarski(A_581,B_580)
      | ~ v1_relat_1(C_579) ) ),
    inference(resolution,[status(thm)],[c_9759,c_10])).

tff(c_110925,plain,(
    ! [C_1136,A_1137,B_1138,B_1139] :
      ( r1_tarski(k9_relat_1(C_1136,A_1137),k9_relat_1(C_1136,B_1138))
      | ~ r1_tarski(B_1139,B_1138)
      | ~ r1_tarski(A_1137,B_1139)
      | ~ v1_relat_1(C_1136) ) ),
    inference(resolution,[status(thm)],[c_20,c_25417])).

tff(c_119524,plain,(
    ! [C_1169,A_1170] :
      ( r1_tarski(k9_relat_1(C_1169,A_1170),k9_relat_1(C_1169,k10_relat_1('#skF_4','#skF_3')))
      | ~ r1_tarski(A_1170,k10_relat_1('#skF_4','#skF_2'))
      | ~ v1_relat_1(C_1169) ) ),
    inference(resolution,[status(thm)],[c_54,c_110925])).

tff(c_619,plain,(
    ! [B_105,A_106] :
      ( r1_tarski(k9_relat_1(B_105,k10_relat_1(B_105,A_106)),A_106)
      | ~ v1_funct_1(B_105)
      | ~ v1_relat_1(B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_650,plain,(
    ! [A_5,A_106,B_105] :
      ( r1_tarski(A_5,A_106)
      | ~ r1_tarski(A_5,k9_relat_1(B_105,k10_relat_1(B_105,A_106)))
      | ~ v1_funct_1(B_105)
      | ~ v1_relat_1(B_105) ) ),
    inference(resolution,[status(thm)],[c_619,c_10])).

tff(c_119553,plain,(
    ! [A_1170] :
      ( r1_tarski(k9_relat_1('#skF_4',A_1170),'#skF_3')
      | ~ v1_funct_1('#skF_4')
      | ~ r1_tarski(A_1170,k10_relat_1('#skF_4','#skF_2'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_119524,c_650])).

tff(c_119643,plain,(
    ! [A_1170] :
      ( r1_tarski(k9_relat_1('#skF_4',A_1170),'#skF_3')
      | ~ r1_tarski(A_1170,k10_relat_1('#skF_4','#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_119553])).

tff(c_197562,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | ~ r1_tarski(k10_relat_1('#skF_4','#skF_2'),k10_relat_1('#skF_4','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_197540,c_119643])).

tff(c_197693,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_197562])).

tff(c_197695,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_197693])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:50:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 44.31/33.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 44.31/33.95  
% 44.31/33.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 44.31/33.95  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 44.31/33.95  
% 44.31/33.95  %Foreground sorts:
% 44.31/33.95  
% 44.31/33.95  
% 44.31/33.95  %Background operators:
% 44.31/33.95  
% 44.31/33.95  
% 44.31/33.95  %Foreground operators:
% 44.31/33.95  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 44.31/33.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 44.31/33.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 44.31/33.95  tff(k1_tarski, type, k1_tarski: $i > $i).
% 44.31/33.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 44.31/33.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 44.31/33.95  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 44.31/33.95  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 44.31/33.95  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 44.31/33.95  tff('#skF_2', type, '#skF_2': $i).
% 44.31/33.95  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 44.31/33.95  tff('#skF_3', type, '#skF_3': $i).
% 44.31/33.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 44.31/33.95  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 44.31/33.95  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 44.31/33.95  tff('#skF_4', type, '#skF_4': $i).
% 44.31/33.95  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 44.31/33.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 44.31/33.95  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 44.31/33.95  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 44.31/33.95  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 44.31/33.95  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 44.31/33.95  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 44.31/33.95  
% 44.31/33.97  tff(f_127, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_1)).
% 44.31/33.97  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 44.31/33.97  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 44.31/33.97  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 44.31/33.97  tff(f_81, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 44.31/33.97  tff(f_77, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 44.31/33.97  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 44.31/33.97  tff(f_110, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 44.31/33.97  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 44.31/33.97  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 44.31/33.97  tff(f_116, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_funct_1)).
% 44.31/33.97  tff(f_104, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 44.31/33.97  tff(c_50, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 44.31/33.97  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 44.31/33.97  tff(c_58, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 44.31/33.97  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 44.31/33.97  tff(c_18, plain, (![A_14]: (k9_relat_1(A_14, k1_relat_1(A_14))=k2_relat_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 44.31/33.97  tff(c_9759, plain, (![C_312, A_313, B_314]: (r1_tarski(k9_relat_1(C_312, A_313), k9_relat_1(C_312, B_314)) | ~r1_tarski(A_313, B_314) | ~v1_relat_1(C_312))), inference(cnfTransformation, [status(thm)], [f_59])).
% 44.31/33.97  tff(c_9780, plain, (![A_14, B_314]: (r1_tarski(k2_relat_1(A_14), k9_relat_1(A_14, B_314)) | ~r1_tarski(k1_relat_1(A_14), B_314) | ~v1_relat_1(A_14) | ~v1_relat_1(A_14))), inference(superposition, [status(thm), theory('equality')], [c_18, c_9759])).
% 44.31/33.97  tff(c_32, plain, (![A_27]: (v1_relat_1(k6_relat_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 44.31/33.97  tff(c_28, plain, (![A_26]: (k1_relat_1(k6_relat_1(A_26))=A_26)), inference(cnfTransformation, [status(thm)], [f_77])).
% 44.31/33.97  tff(c_151, plain, (![B_54, A_55]: (r1_tarski(k10_relat_1(B_54, A_55), k1_relat_1(B_54)) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_63])).
% 44.31/33.97  tff(c_160, plain, (![A_26, A_55]: (r1_tarski(k10_relat_1(k6_relat_1(A_26), A_55), A_26) | ~v1_relat_1(k6_relat_1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_151])).
% 44.31/33.97  tff(c_164, plain, (![A_26, A_55]: (r1_tarski(k10_relat_1(k6_relat_1(A_26), A_55), A_26))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_160])).
% 44.31/33.97  tff(c_30, plain, (![A_26]: (k2_relat_1(k6_relat_1(A_26))=A_26)), inference(cnfTransformation, [status(thm)], [f_77])).
% 44.31/33.97  tff(c_187, plain, (![A_60]: (k9_relat_1(A_60, k1_relat_1(A_60))=k2_relat_1(A_60) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_53])).
% 44.31/33.97  tff(c_196, plain, (![A_26]: (k9_relat_1(k6_relat_1(A_26), A_26)=k2_relat_1(k6_relat_1(A_26)) | ~v1_relat_1(k6_relat_1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_187])).
% 44.31/33.97  tff(c_200, plain, (![A_26]: (k9_relat_1(k6_relat_1(A_26), A_26)=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_196])).
% 44.31/33.97  tff(c_10240, plain, (![A_335, B_336]: (r1_tarski(A_335, k10_relat_1(B_336, k9_relat_1(B_336, A_335))) | ~r1_tarski(A_335, k1_relat_1(B_336)) | ~v1_relat_1(B_336))), inference(cnfTransformation, [status(thm)], [f_110])).
% 44.31/33.97  tff(c_10263, plain, (![A_26]: (r1_tarski(A_26, k10_relat_1(k6_relat_1(A_26), A_26)) | ~r1_tarski(A_26, k1_relat_1(k6_relat_1(A_26))) | ~v1_relat_1(k6_relat_1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_200, c_10240])).
% 44.31/33.97  tff(c_10280, plain, (![A_337]: (r1_tarski(A_337, k10_relat_1(k6_relat_1(A_337), A_337)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_6, c_28, c_10263])).
% 44.31/33.97  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 44.31/33.97  tff(c_10293, plain, (![A_337]: (k10_relat_1(k6_relat_1(A_337), A_337)=A_337 | ~r1_tarski(k10_relat_1(k6_relat_1(A_337), A_337), A_337))), inference(resolution, [status(thm)], [c_10280, c_2])).
% 44.31/33.97  tff(c_10311, plain, (![A_337]: (k10_relat_1(k6_relat_1(A_337), A_337)=A_337)), inference(demodulation, [status(thm), theory('equality')], [c_164, c_10293])).
% 44.31/33.97  tff(c_52, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 44.31/33.97  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(B_6, C_7) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 44.31/33.97  tff(c_30515, plain, (![A_638, B_639, A_640]: (r1_tarski(A_638, k10_relat_1(B_639, k9_relat_1(B_639, A_640))) | ~r1_tarski(A_638, A_640) | ~r1_tarski(A_640, k1_relat_1(B_639)) | ~v1_relat_1(B_639))), inference(resolution, [status(thm)], [c_10240, c_10])).
% 44.31/33.97  tff(c_194037, plain, (![A_1490, B_1491, A_1492, A_1493]: (r1_tarski(A_1490, k10_relat_1(B_1491, k9_relat_1(B_1491, A_1492))) | ~r1_tarski(A_1490, A_1493) | ~r1_tarski(A_1493, A_1492) | ~r1_tarski(A_1492, k1_relat_1(B_1491)) | ~v1_relat_1(B_1491))), inference(resolution, [status(thm)], [c_30515, c_10])).
% 44.31/33.97  tff(c_195569, plain, (![B_1498, A_1499]: (r1_tarski('#skF_2', k10_relat_1(B_1498, k9_relat_1(B_1498, A_1499))) | ~r1_tarski(k2_relat_1('#skF_4'), A_1499) | ~r1_tarski(A_1499, k1_relat_1(B_1498)) | ~v1_relat_1(B_1498))), inference(resolution, [status(thm)], [c_52, c_194037])).
% 44.31/33.97  tff(c_195723, plain, (![A_26]: (r1_tarski('#skF_2', k10_relat_1(k6_relat_1(A_26), A_26)) | ~r1_tarski(k2_relat_1('#skF_4'), A_26) | ~r1_tarski(A_26, k1_relat_1(k6_relat_1(A_26))) | ~v1_relat_1(k6_relat_1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_200, c_195569])).
% 44.31/33.97  tff(c_195824, plain, (![A_1500]: (r1_tarski('#skF_2', A_1500) | ~r1_tarski(k2_relat_1('#skF_4'), A_1500))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_6, c_28, c_10311, c_195723])).
% 44.31/33.97  tff(c_195892, plain, (![B_314]: (r1_tarski('#skF_2', k9_relat_1('#skF_4', B_314)) | ~r1_tarski(k1_relat_1('#skF_4'), B_314) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_9780, c_195824])).
% 44.31/33.97  tff(c_196085, plain, (![B_1502]: (r1_tarski('#skF_2', k9_relat_1('#skF_4', B_1502)) | ~r1_tarski(k1_relat_1('#skF_4'), B_1502))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_195892])).
% 44.31/33.97  tff(c_196209, plain, (r1_tarski('#skF_2', k9_relat_1('#skF_4', k1_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_6, c_196085])).
% 44.31/33.97  tff(c_12, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 44.31/33.97  tff(c_196278, plain, (k3_xboole_0('#skF_2', k9_relat_1('#skF_4', k1_relat_1('#skF_4')))='#skF_2'), inference(resolution, [status(thm)], [c_196209, c_12])).
% 44.31/33.97  tff(c_48, plain, (![A_37, B_38]: (k3_xboole_0(A_37, k9_relat_1(B_38, k1_relat_1(B_38)))=k9_relat_1(B_38, k10_relat_1(B_38, A_37)) | ~v1_funct_1(B_38) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_116])).
% 44.31/33.97  tff(c_197457, plain, (k9_relat_1('#skF_4', k10_relat_1('#skF_4', '#skF_2'))='#skF_2' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_196278, c_48])).
% 44.31/33.97  tff(c_197540, plain, (k9_relat_1('#skF_4', k10_relat_1('#skF_4', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_197457])).
% 44.31/33.97  tff(c_54, plain, (r1_tarski(k10_relat_1('#skF_4', '#skF_2'), k10_relat_1('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 44.31/33.97  tff(c_20, plain, (![C_17, A_15, B_16]: (r1_tarski(k9_relat_1(C_17, A_15), k9_relat_1(C_17, B_16)) | ~r1_tarski(A_15, B_16) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 44.31/33.97  tff(c_25417, plain, (![A_578, C_579, B_580, A_581]: (r1_tarski(A_578, k9_relat_1(C_579, B_580)) | ~r1_tarski(A_578, k9_relat_1(C_579, A_581)) | ~r1_tarski(A_581, B_580) | ~v1_relat_1(C_579))), inference(resolution, [status(thm)], [c_9759, c_10])).
% 44.31/33.97  tff(c_110925, plain, (![C_1136, A_1137, B_1138, B_1139]: (r1_tarski(k9_relat_1(C_1136, A_1137), k9_relat_1(C_1136, B_1138)) | ~r1_tarski(B_1139, B_1138) | ~r1_tarski(A_1137, B_1139) | ~v1_relat_1(C_1136))), inference(resolution, [status(thm)], [c_20, c_25417])).
% 44.31/33.97  tff(c_119524, plain, (![C_1169, A_1170]: (r1_tarski(k9_relat_1(C_1169, A_1170), k9_relat_1(C_1169, k10_relat_1('#skF_4', '#skF_3'))) | ~r1_tarski(A_1170, k10_relat_1('#skF_4', '#skF_2')) | ~v1_relat_1(C_1169))), inference(resolution, [status(thm)], [c_54, c_110925])).
% 44.31/33.97  tff(c_619, plain, (![B_105, A_106]: (r1_tarski(k9_relat_1(B_105, k10_relat_1(B_105, A_106)), A_106) | ~v1_funct_1(B_105) | ~v1_relat_1(B_105))), inference(cnfTransformation, [status(thm)], [f_104])).
% 44.31/33.97  tff(c_650, plain, (![A_5, A_106, B_105]: (r1_tarski(A_5, A_106) | ~r1_tarski(A_5, k9_relat_1(B_105, k10_relat_1(B_105, A_106))) | ~v1_funct_1(B_105) | ~v1_relat_1(B_105))), inference(resolution, [status(thm)], [c_619, c_10])).
% 44.31/33.97  tff(c_119553, plain, (![A_1170]: (r1_tarski(k9_relat_1('#skF_4', A_1170), '#skF_3') | ~v1_funct_1('#skF_4') | ~r1_tarski(A_1170, k10_relat_1('#skF_4', '#skF_2')) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_119524, c_650])).
% 44.31/33.97  tff(c_119643, plain, (![A_1170]: (r1_tarski(k9_relat_1('#skF_4', A_1170), '#skF_3') | ~r1_tarski(A_1170, k10_relat_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_119553])).
% 44.31/33.97  tff(c_197562, plain, (r1_tarski('#skF_2', '#skF_3') | ~r1_tarski(k10_relat_1('#skF_4', '#skF_2'), k10_relat_1('#skF_4', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_197540, c_119643])).
% 44.31/33.97  tff(c_197693, plain, (r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_197562])).
% 44.31/33.97  tff(c_197695, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_197693])).
% 44.31/33.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 44.31/33.97  
% 44.31/33.97  Inference rules
% 44.31/33.97  ----------------------
% 44.31/33.97  #Ref     : 0
% 44.31/33.97  #Sup     : 46430
% 44.31/33.97  #Fact    : 20
% 44.31/33.97  #Define  : 0
% 44.31/33.97  #Split   : 17
% 44.31/33.97  #Chain   : 0
% 44.31/33.97  #Close   : 0
% 44.31/33.97  
% 44.31/33.97  Ordering : KBO
% 44.31/33.97  
% 44.31/33.97  Simplification rules
% 44.31/33.97  ----------------------
% 44.31/33.97  #Subsume      : 7865
% 44.31/33.97  #Demod        : 41544
% 44.31/33.97  #Tautology    : 23708
% 44.31/33.97  #SimpNegUnit  : 112
% 44.31/33.97  #BackRed      : 22
% 44.31/33.97  
% 44.31/33.97  #Partial instantiations: 0
% 44.31/33.97  #Strategies tried      : 1
% 44.31/33.97  
% 44.31/33.97  Timing (in seconds)
% 44.31/33.97  ----------------------
% 44.31/33.97  Preprocessing        : 0.33
% 44.31/33.97  Parsing              : 0.17
% 44.31/33.97  CNF conversion       : 0.02
% 44.31/33.97  Main loop            : 32.86
% 44.31/33.97  Inferencing          : 3.07
% 44.31/33.97  Reduction            : 19.58
% 44.31/33.97  Demodulation         : 17.63
% 44.31/33.97  BG Simplification    : 0.33
% 44.31/33.97  Subsumption          : 8.62
% 44.31/33.97  Abstraction          : 0.61
% 44.31/33.97  MUC search           : 0.00
% 44.31/33.97  Cooper               : 0.00
% 44.31/33.97  Total                : 33.23
% 44.31/33.97  Index Insertion      : 0.00
% 44.31/33.97  Index Deletion       : 0.00
% 44.31/33.97  Index Matching       : 0.00
% 44.31/33.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
