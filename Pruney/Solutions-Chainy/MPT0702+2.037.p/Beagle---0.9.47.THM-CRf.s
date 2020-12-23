%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:07 EST 2020

% Result     : Theorem 5.06s
% Output     : CNFRefutation 5.48s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 314 expanded)
%              Number of leaves         :   27 ( 128 expanded)
%              Depth                    :   13
%              Number of atoms          :  131 ( 850 expanded)
%              Number of equality atoms :   40 ( 125 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).

tff(c_40,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | k4_xboole_0(A_23,B_24) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_44,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_26])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_79,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_99,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_79])).

tff(c_45,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = A_25
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_65,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_45])).

tff(c_110,plain,(
    ! [A_31,B_32] : k5_xboole_0(A_31,k3_xboole_0(A_31,B_32)) = k4_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_122,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k4_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_110])).

tff(c_125,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_122])).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_30,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_268,plain,(
    ! [A_42,B_43] : k4_xboole_0(A_42,k4_xboole_0(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_284,plain,(
    ! [A_42,B_43] : r1_tarski(k3_xboole_0(A_42,B_43),A_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_16])).

tff(c_98,plain,(
    k4_xboole_0('#skF_1',k1_relat_1('#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_79])).

tff(c_34,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_24,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k10_relat_1(B_19,k9_relat_1(B_19,A_18)),A_18)
      | ~ v2_funct_1(B_19)
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_721,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(A_59,k10_relat_1(B_60,k9_relat_1(B_60,A_59)))
      | ~ r1_tarski(A_59,k1_relat_1(B_60))
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3132,plain,(
    ! [B_113,A_114] :
      ( k10_relat_1(B_113,k9_relat_1(B_113,A_114)) = A_114
      | ~ r1_tarski(k10_relat_1(B_113,k9_relat_1(B_113,A_114)),A_114)
      | ~ r1_tarski(A_114,k1_relat_1(B_113))
      | ~ v1_relat_1(B_113) ) ),
    inference(resolution,[status(thm)],[c_721,c_2])).

tff(c_5890,plain,(
    ! [B_154,A_155] :
      ( k10_relat_1(B_154,k9_relat_1(B_154,A_155)) = A_155
      | ~ r1_tarski(A_155,k1_relat_1(B_154))
      | ~ v2_funct_1(B_154)
      | ~ v1_funct_1(B_154)
      | ~ v1_relat_1(B_154) ) ),
    inference(resolution,[status(thm)],[c_24,c_3132])).

tff(c_5907,plain,
    ( k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_5890])).

tff(c_5918,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_28,c_5907])).

tff(c_910,plain,(
    ! [C_65,A_66,B_67] :
      ( k3_xboole_0(k9_relat_1(C_65,A_66),k9_relat_1(C_65,B_67)) = k9_relat_1(C_65,k3_xboole_0(A_66,B_67))
      | ~ v2_funct_1(C_65)
      | ~ v1_funct_1(C_65)
      | ~ v1_relat_1(C_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_32,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_61,plain,(
    k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) = k9_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_45])).

tff(c_916,plain,
    ( k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k9_relat_1('#skF_3','#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_910,c_61])).

tff(c_945,plain,(
    k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k9_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_28,c_916])).

tff(c_963,plain,
    ( r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),k3_xboole_0('#skF_1','#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_945,c_24])).

tff(c_973,plain,(
    r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_28,c_963])).

tff(c_5922,plain,(
    r1_tarski('#skF_1',k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5918,c_973])).

tff(c_449,plain,(
    ! [A_47,B_48] : r1_tarski(k3_xboole_0(A_47,B_48),A_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_16])).

tff(c_476,plain,(
    ! [A_47,B_48] :
      ( k3_xboole_0(A_47,B_48) = A_47
      | ~ r1_tarski(A_47,k3_xboole_0(A_47,B_48)) ) ),
    inference(resolution,[status(thm)],[c_449,c_2])).

tff(c_5981,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_5922,c_476])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_22,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,k10_relat_1(B_17,k9_relat_1(B_17,A_16)))
      | ~ r1_tarski(A_16,k1_relat_1(B_17))
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_960,plain,
    ( r1_tarski(k3_xboole_0('#skF_1','#skF_2'),k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')))
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_945,c_22])).

tff(c_971,plain,
    ( r1_tarski(k3_xboole_0('#skF_1','#skF_2'),k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')))
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_960])).

tff(c_3124,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_971])).

tff(c_3128,plain,(
    k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k1_relat_1('#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_3124])).

tff(c_5991,plain,(
    k4_xboole_0('#skF_1',k1_relat_1('#skF_3')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5981,c_3128])).

tff(c_6000,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_5991])).

tff(c_6002,plain,(
    r1_tarski(k3_xboole_0('#skF_1','#skF_2'),k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_971])).

tff(c_6117,plain,(
    ! [B_156,A_157] :
      ( k10_relat_1(B_156,k9_relat_1(B_156,A_157)) = A_157
      | ~ r1_tarski(k10_relat_1(B_156,k9_relat_1(B_156,A_157)),A_157)
      | ~ r1_tarski(A_157,k1_relat_1(B_156))
      | ~ v1_relat_1(B_156) ) ),
    inference(resolution,[status(thm)],[c_721,c_2])).

tff(c_6129,plain,
    ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) = k3_xboole_0('#skF_1','#skF_2')
    | ~ r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),k3_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_945,c_6117])).

tff(c_6144,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6002,c_973,c_945,c_6129])).

tff(c_730,plain,(
    ! [B_60,A_59] :
      ( k10_relat_1(B_60,k9_relat_1(B_60,A_59)) = A_59
      | ~ r1_tarski(k10_relat_1(B_60,k9_relat_1(B_60,A_59)),A_59)
      | ~ r1_tarski(A_59,k1_relat_1(B_60))
      | ~ v1_relat_1(B_60) ) ),
    inference(resolution,[status(thm)],[c_721,c_2])).

tff(c_6161,plain,
    ( k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6144,c_730])).

tff(c_6186,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_284,c_6144,c_6161])).

tff(c_12,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6244,plain,(
    k5_xboole_0('#skF_1','#skF_1') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6186,c_12])).

tff(c_6257,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_6244])).

tff(c_6259,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_6257])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.08  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.07/0.26  % Computer   : n009.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % DateTime   : Tue Dec  1 13:42:41 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.07/0.27  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.06/2.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.48/2.04  
% 5.48/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.48/2.04  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.48/2.04  
% 5.48/2.04  %Foreground sorts:
% 5.48/2.04  
% 5.48/2.04  
% 5.48/2.04  %Background operators:
% 5.48/2.04  
% 5.48/2.04  
% 5.48/2.04  %Foreground operators:
% 5.48/2.04  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.48/2.04  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.48/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.48/2.04  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.48/2.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.48/2.04  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.48/2.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.48/2.04  tff('#skF_2', type, '#skF_2': $i).
% 5.48/2.04  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.48/2.04  tff('#skF_3', type, '#skF_3': $i).
% 5.48/2.04  tff('#skF_1', type, '#skF_1': $i).
% 5.48/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.48/2.04  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.48/2.04  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.48/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.48/2.04  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.48/2.04  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.48/2.04  
% 5.48/2.06  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.48/2.06  tff(f_80, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_funct_1)).
% 5.48/2.06  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.48/2.06  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.48/2.06  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.48/2.06  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.48/2.06  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.48/2.06  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_1)).
% 5.48/2.06  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 5.48/2.06  tff(f_53, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_1)).
% 5.48/2.06  tff(c_40, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | k4_xboole_0(A_23, B_24)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.48/2.06  tff(c_26, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.48/2.06  tff(c_44, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_26])).
% 5.48/2.06  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.48/2.06  tff(c_79, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.48/2.06  tff(c_99, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_79])).
% 5.48/2.06  tff(c_45, plain, (![A_25, B_26]: (k3_xboole_0(A_25, B_26)=A_25 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.48/2.06  tff(c_65, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_45])).
% 5.48/2.06  tff(c_110, plain, (![A_31, B_32]: (k5_xboole_0(A_31, k3_xboole_0(A_31, B_32))=k4_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.48/2.06  tff(c_122, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k4_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_65, c_110])).
% 5.48/2.06  tff(c_125, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_99, c_122])).
% 5.48/2.06  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.48/2.06  tff(c_30, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.48/2.06  tff(c_268, plain, (![A_42, B_43]: (k4_xboole_0(A_42, k4_xboole_0(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.48/2.06  tff(c_16, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.48/2.06  tff(c_284, plain, (![A_42, B_43]: (r1_tarski(k3_xboole_0(A_42, B_43), A_42))), inference(superposition, [status(thm), theory('equality')], [c_268, c_16])).
% 5.48/2.06  tff(c_98, plain, (k4_xboole_0('#skF_1', k1_relat_1('#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_79])).
% 5.48/2.06  tff(c_34, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.48/2.06  tff(c_28, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.48/2.06  tff(c_24, plain, (![B_19, A_18]: (r1_tarski(k10_relat_1(B_19, k9_relat_1(B_19, A_18)), A_18) | ~v2_funct_1(B_19) | ~v1_funct_1(B_19) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.48/2.06  tff(c_721, plain, (![A_59, B_60]: (r1_tarski(A_59, k10_relat_1(B_60, k9_relat_1(B_60, A_59))) | ~r1_tarski(A_59, k1_relat_1(B_60)) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.48/2.06  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.48/2.06  tff(c_3132, plain, (![B_113, A_114]: (k10_relat_1(B_113, k9_relat_1(B_113, A_114))=A_114 | ~r1_tarski(k10_relat_1(B_113, k9_relat_1(B_113, A_114)), A_114) | ~r1_tarski(A_114, k1_relat_1(B_113)) | ~v1_relat_1(B_113))), inference(resolution, [status(thm)], [c_721, c_2])).
% 5.48/2.06  tff(c_5890, plain, (![B_154, A_155]: (k10_relat_1(B_154, k9_relat_1(B_154, A_155))=A_155 | ~r1_tarski(A_155, k1_relat_1(B_154)) | ~v2_funct_1(B_154) | ~v1_funct_1(B_154) | ~v1_relat_1(B_154))), inference(resolution, [status(thm)], [c_24, c_3132])).
% 5.48/2.06  tff(c_5907, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_5890])).
% 5.48/2.06  tff(c_5918, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_28, c_5907])).
% 5.48/2.06  tff(c_910, plain, (![C_65, A_66, B_67]: (k3_xboole_0(k9_relat_1(C_65, A_66), k9_relat_1(C_65, B_67))=k9_relat_1(C_65, k3_xboole_0(A_66, B_67)) | ~v2_funct_1(C_65) | ~v1_funct_1(C_65) | ~v1_relat_1(C_65))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.48/2.06  tff(c_32, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.48/2.06  tff(c_61, plain, (k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_45])).
% 5.48/2.06  tff(c_916, plain, (k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_910, c_61])).
% 5.48/2.06  tff(c_945, plain, (k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_28, c_916])).
% 5.48/2.06  tff(c_963, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), k3_xboole_0('#skF_1', '#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_945, c_24])).
% 5.48/2.06  tff(c_973, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_28, c_963])).
% 5.48/2.06  tff(c_5922, plain, (r1_tarski('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5918, c_973])).
% 5.48/2.06  tff(c_449, plain, (![A_47, B_48]: (r1_tarski(k3_xboole_0(A_47, B_48), A_47))), inference(superposition, [status(thm), theory('equality')], [c_268, c_16])).
% 5.48/2.06  tff(c_476, plain, (![A_47, B_48]: (k3_xboole_0(A_47, B_48)=A_47 | ~r1_tarski(A_47, k3_xboole_0(A_47, B_48)))), inference(resolution, [status(thm)], [c_449, c_2])).
% 5.48/2.06  tff(c_5981, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_5922, c_476])).
% 5.48/2.06  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.48/2.06  tff(c_22, plain, (![A_16, B_17]: (r1_tarski(A_16, k10_relat_1(B_17, k9_relat_1(B_17, A_16))) | ~r1_tarski(A_16, k1_relat_1(B_17)) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.48/2.06  tff(c_960, plain, (r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))) | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_945, c_22])).
% 5.48/2.06  tff(c_971, plain, (r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))) | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_960])).
% 5.48/2.06  tff(c_3124, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_971])).
% 5.48/2.06  tff(c_3128, plain, (k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k1_relat_1('#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_3124])).
% 5.48/2.06  tff(c_5991, plain, (k4_xboole_0('#skF_1', k1_relat_1('#skF_3'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5981, c_3128])).
% 5.48/2.06  tff(c_6000, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_5991])).
% 5.48/2.06  tff(c_6002, plain, (r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_971])).
% 5.48/2.06  tff(c_6117, plain, (![B_156, A_157]: (k10_relat_1(B_156, k9_relat_1(B_156, A_157))=A_157 | ~r1_tarski(k10_relat_1(B_156, k9_relat_1(B_156, A_157)), A_157) | ~r1_tarski(A_157, k1_relat_1(B_156)) | ~v1_relat_1(B_156))), inference(resolution, [status(thm)], [c_721, c_2])).
% 5.48/2.06  tff(c_6129, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))=k3_xboole_0('#skF_1', '#skF_2') | ~r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), k3_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_945, c_6117])).
% 5.48/2.06  tff(c_6144, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))=k3_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_6002, c_973, c_945, c_6129])).
% 5.48/2.06  tff(c_730, plain, (![B_60, A_59]: (k10_relat_1(B_60, k9_relat_1(B_60, A_59))=A_59 | ~r1_tarski(k10_relat_1(B_60, k9_relat_1(B_60, A_59)), A_59) | ~r1_tarski(A_59, k1_relat_1(B_60)) | ~v1_relat_1(B_60))), inference(resolution, [status(thm)], [c_721, c_2])).
% 5.48/2.06  tff(c_6161, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski('#skF_1', k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6144, c_730])).
% 5.48/2.06  tff(c_6186, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_30, c_284, c_6144, c_6161])).
% 5.48/2.06  tff(c_12, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.48/2.06  tff(c_6244, plain, (k5_xboole_0('#skF_1', '#skF_1')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6186, c_12])).
% 5.48/2.06  tff(c_6257, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_125, c_6244])).
% 5.48/2.06  tff(c_6259, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_6257])).
% 5.48/2.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.48/2.06  
% 5.48/2.06  Inference rules
% 5.48/2.06  ----------------------
% 5.48/2.06  #Ref     : 0
% 5.48/2.06  #Sup     : 1468
% 5.48/2.06  #Fact    : 0
% 5.48/2.06  #Define  : 0
% 5.48/2.06  #Split   : 9
% 5.48/2.06  #Chain   : 0
% 5.48/2.06  #Close   : 0
% 5.48/2.06  
% 5.48/2.06  Ordering : KBO
% 5.48/2.06  
% 5.48/2.06  Simplification rules
% 5.48/2.06  ----------------------
% 5.48/2.06  #Subsume      : 206
% 5.48/2.06  #Demod        : 1642
% 5.48/2.06  #Tautology    : 776
% 5.48/2.06  #SimpNegUnit  : 31
% 5.48/2.06  #BackRed      : 20
% 5.48/2.06  
% 5.48/2.06  #Partial instantiations: 0
% 5.48/2.06  #Strategies tried      : 1
% 5.48/2.06  
% 5.48/2.06  Timing (in seconds)
% 5.48/2.06  ----------------------
% 5.48/2.06  Preprocessing        : 0.32
% 5.48/2.06  Parsing              : 0.18
% 5.48/2.06  CNF conversion       : 0.02
% 5.48/2.06  Main loop            : 1.05
% 5.48/2.06  Inferencing          : 0.32
% 5.48/2.06  Reduction            : 0.43
% 5.48/2.06  Demodulation         : 0.32
% 5.48/2.06  BG Simplification    : 0.04
% 5.48/2.06  Subsumption          : 0.20
% 5.48/2.06  Abstraction          : 0.06
% 5.48/2.06  MUC search           : 0.00
% 5.48/2.06  Cooper               : 0.00
% 5.48/2.06  Total                : 1.40
% 5.48/2.06  Index Insertion      : 0.00
% 5.48/2.06  Index Deletion       : 0.00
% 5.48/2.06  Index Matching       : 0.00
% 5.48/2.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
