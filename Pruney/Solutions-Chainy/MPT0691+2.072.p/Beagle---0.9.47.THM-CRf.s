%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:48 EST 2020

% Result     : Theorem 36.25s
% Output     : CNFRefutation 36.39s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 197 expanded)
%              Number of leaves         :   29 (  76 expanded)
%              Depth                    :   18
%              Number of atoms          :  140 ( 394 expanded)
%              Number of equality atoms :   20 (  58 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k10_relat_1(B,A),k10_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t179_relat_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_43,plain,(
    ! [A_38,B_39] :
      ( k2_xboole_0(A_38,B_39) = B_39
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_55,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_43])).

tff(c_30,plain,(
    ! [B_29,A_28] :
      ( r1_tarski(k7_relat_1(B_29,A_28),B_29)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_14,plain,(
    ! [A_10,B_11] : r1_tarski(A_10,k2_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_247,plain,(
    ! [A_61,C_62,B_63] :
      ( r1_tarski(A_61,C_62)
      | ~ r1_tarski(B_63,C_62)
      | ~ r1_tarski(A_61,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_302,plain,(
    ! [A_68,A_69,B_70] :
      ( r1_tarski(A_68,k2_xboole_0(A_69,B_70))
      | ~ r1_tarski(A_68,A_69) ) ),
    inference(resolution,[status(thm)],[c_14,c_247])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(B_6,C_7)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_833,plain,(
    ! [A_109,A_110,B_111,A_112] :
      ( r1_tarski(A_109,k2_xboole_0(A_110,B_111))
      | ~ r1_tarski(A_109,A_112)
      | ~ r1_tarski(A_112,A_110) ) ),
    inference(resolution,[status(thm)],[c_302,c_10])).

tff(c_9807,plain,(
    ! [B_375,A_376,A_377,B_378] :
      ( r1_tarski(k7_relat_1(B_375,A_376),k2_xboole_0(A_377,B_378))
      | ~ r1_tarski(B_375,A_377)
      | ~ v1_relat_1(B_375) ) ),
    inference(resolution,[status(thm)],[c_30,c_833])).

tff(c_9872,plain,(
    ! [B_375,A_376,B_2] :
      ( r1_tarski(k7_relat_1(B_375,A_376),B_2)
      | ~ r1_tarski(B_375,B_2)
      | ~ v1_relat_1(B_375) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_9807])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k7_relat_1(A_12,B_13))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [A_18] :
      ( k10_relat_1(A_18,k2_relat_1(A_18)) = k1_relat_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_281,plain,(
    ! [C_65,A_66,B_67] :
      ( r1_tarski(k10_relat_1(C_65,A_66),k10_relat_1(C_65,B_67))
      | ~ r1_tarski(A_66,B_67)
      | ~ v1_relat_1(C_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2389,plain,(
    ! [A_185,B_186] :
      ( r1_tarski(k1_relat_1(A_185),k10_relat_1(A_185,B_186))
      | ~ r1_tarski(k2_relat_1(A_185),B_186)
      | ~ v1_relat_1(A_185)
      | ~ v1_relat_1(A_185) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_281])).

tff(c_36,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_862,plain,(
    ! [A_110,B_111] :
      ( r1_tarski('#skF_1',k2_xboole_0(A_110,B_111))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_110) ) ),
    inference(resolution,[status(thm)],[c_36,c_833])).

tff(c_2400,plain,(
    ! [B_186,B_111] :
      ( r1_tarski('#skF_1',k2_xboole_0(k10_relat_1('#skF_2',B_186),B_111))
      | ~ r1_tarski(k2_relat_1('#skF_2'),B_186)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_2389,c_862])).

tff(c_2625,plain,(
    ! [B_196,B_197] :
      ( r1_tarski('#skF_1',k2_xboole_0(k10_relat_1('#skF_2',B_196),B_197))
      | ~ r1_tarski(k2_relat_1('#skF_2'),B_196) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2400])).

tff(c_2686,plain,(
    ! [B_198] :
      ( r1_tarski('#skF_1',k10_relat_1('#skF_2',B_198))
      | ~ r1_tarski(k2_relat_1('#skF_2'),B_198) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_2625])).

tff(c_2726,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k2_relat_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_6,c_2686])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2759,plain,(
    k3_xboole_0('#skF_1',k10_relat_1('#skF_2',k2_relat_1('#skF_2'))) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2726,c_12])).

tff(c_32,plain,(
    ! [A_30,C_32,B_31] :
      ( k3_xboole_0(A_30,k10_relat_1(C_32,B_31)) = k10_relat_1(k7_relat_1(C_32,A_30),B_31)
      | ~ v1_relat_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2766,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1('#skF_2')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2759,c_32])).

tff(c_2776,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2766])).

tff(c_20,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k10_relat_1(B_17,A_16),k1_relat_1(B_17))
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2818,plain,
    ( r1_tarski('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2776,c_20])).

tff(c_3620,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_2818])).

tff(c_3623,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_3620])).

tff(c_3627,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_3623])).

tff(c_3629,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_2818])).

tff(c_3628,plain,(
    r1_tarski('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_2818])).

tff(c_28,plain,(
    ! [B_27,A_26] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_27,A_26)),A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_160,plain,(
    ! [B_53,A_54] :
      ( B_53 = A_54
      | ~ r1_tarski(B_53,A_54)
      | ~ r1_tarski(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_174,plain,(
    ! [B_27,A_26] :
      ( k1_relat_1(k7_relat_1(B_27,A_26)) = A_26
      | ~ r1_tarski(A_26,k1_relat_1(k7_relat_1(B_27,A_26)))
      | ~ v1_relat_1(B_27) ) ),
    inference(resolution,[status(thm)],[c_28,c_160])).

tff(c_3736,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_3628,c_174])).

tff(c_3758,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_3736])).

tff(c_235,plain,(
    ! [B_59,A_60] :
      ( k2_relat_1(k7_relat_1(B_59,A_60)) = k9_relat_1(B_59,A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_241,plain,(
    ! [B_59,A_60] :
      ( k10_relat_1(k7_relat_1(B_59,A_60),k9_relat_1(B_59,A_60)) = k1_relat_1(k7_relat_1(B_59,A_60))
      | ~ v1_relat_1(k7_relat_1(B_59,A_60))
      | ~ v1_relat_1(B_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_22])).

tff(c_766,plain,(
    ! [B_102,A_103,C_104] :
      ( r1_tarski(k10_relat_1(B_102,A_103),k10_relat_1(C_104,A_103))
      | ~ r1_tarski(B_102,C_104)
      | ~ v1_relat_1(C_104)
      | ~ v1_relat_1(B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_7023,plain,(
    ! [A_307,C_308,A_309,B_310] :
      ( r1_tarski(A_307,k10_relat_1(C_308,A_309))
      | ~ r1_tarski(A_307,k10_relat_1(B_310,A_309))
      | ~ r1_tarski(B_310,C_308)
      | ~ v1_relat_1(C_308)
      | ~ v1_relat_1(B_310) ) ),
    inference(resolution,[status(thm)],[c_766,c_10])).

tff(c_119061,plain,(
    ! [A_1529,C_1530,B_1531,A_1532] :
      ( r1_tarski(A_1529,k10_relat_1(C_1530,k9_relat_1(B_1531,A_1532)))
      | ~ r1_tarski(A_1529,k1_relat_1(k7_relat_1(B_1531,A_1532)))
      | ~ r1_tarski(k7_relat_1(B_1531,A_1532),C_1530)
      | ~ v1_relat_1(C_1530)
      | ~ v1_relat_1(k7_relat_1(B_1531,A_1532))
      | ~ v1_relat_1(k7_relat_1(B_1531,A_1532))
      | ~ v1_relat_1(B_1531) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_7023])).

tff(c_34,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_119461,plain,
    ( ~ r1_tarski('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1')))
    | ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_119061,c_34])).

tff(c_119677,plain,(
    ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_3629,c_6,c_3758,c_119461])).

tff(c_119694,plain,
    ( ~ r1_tarski('#skF_2','#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_9872,c_119677])).

tff(c_119704,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_6,c_119694])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:51:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 36.25/26.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 36.25/26.43  
% 36.25/26.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 36.25/26.43  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 36.25/26.43  
% 36.25/26.43  %Foreground sorts:
% 36.25/26.43  
% 36.25/26.43  
% 36.25/26.43  %Background operators:
% 36.25/26.43  
% 36.25/26.43  
% 36.25/26.43  %Foreground operators:
% 36.25/26.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 36.25/26.43  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 36.25/26.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 36.25/26.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 36.25/26.43  tff('#skF_2', type, '#skF_2': $i).
% 36.25/26.43  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 36.25/26.43  tff('#skF_1', type, '#skF_1': $i).
% 36.25/26.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 36.25/26.43  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 36.25/26.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 36.25/26.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 36.25/26.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 36.25/26.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 36.25/26.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 36.25/26.43  
% 36.39/26.45  tff(f_97, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 36.39/26.45  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 36.39/26.45  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 36.39/26.45  tff(f_86, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 36.39/26.45  tff(f_47, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 36.39/26.45  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 36.39/26.45  tff(f_51, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 36.39/26.45  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 36.39/26.45  tff(f_69, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_relat_1)).
% 36.39/26.45  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 36.39/26.45  tff(f_90, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 36.39/26.45  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 36.39/26.45  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 36.39/26.45  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 36.39/26.45  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k10_relat_1(B, A), k10_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t179_relat_1)).
% 36.39/26.45  tff(c_38, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 36.39/26.45  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 36.39/26.45  tff(c_43, plain, (![A_38, B_39]: (k2_xboole_0(A_38, B_39)=B_39 | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_35])).
% 36.39/26.45  tff(c_55, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_43])).
% 36.39/26.45  tff(c_30, plain, (![B_29, A_28]: (r1_tarski(k7_relat_1(B_29, A_28), B_29) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_86])).
% 36.39/26.45  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(A_10, k2_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 36.39/26.45  tff(c_247, plain, (![A_61, C_62, B_63]: (r1_tarski(A_61, C_62) | ~r1_tarski(B_63, C_62) | ~r1_tarski(A_61, B_63))), inference(cnfTransformation, [status(thm)], [f_41])).
% 36.39/26.45  tff(c_302, plain, (![A_68, A_69, B_70]: (r1_tarski(A_68, k2_xboole_0(A_69, B_70)) | ~r1_tarski(A_68, A_69))), inference(resolution, [status(thm)], [c_14, c_247])).
% 36.39/26.45  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(B_6, C_7) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 36.39/26.45  tff(c_833, plain, (![A_109, A_110, B_111, A_112]: (r1_tarski(A_109, k2_xboole_0(A_110, B_111)) | ~r1_tarski(A_109, A_112) | ~r1_tarski(A_112, A_110))), inference(resolution, [status(thm)], [c_302, c_10])).
% 36.39/26.45  tff(c_9807, plain, (![B_375, A_376, A_377, B_378]: (r1_tarski(k7_relat_1(B_375, A_376), k2_xboole_0(A_377, B_378)) | ~r1_tarski(B_375, A_377) | ~v1_relat_1(B_375))), inference(resolution, [status(thm)], [c_30, c_833])).
% 36.39/26.45  tff(c_9872, plain, (![B_375, A_376, B_2]: (r1_tarski(k7_relat_1(B_375, A_376), B_2) | ~r1_tarski(B_375, B_2) | ~v1_relat_1(B_375))), inference(superposition, [status(thm), theory('equality')], [c_55, c_9807])).
% 36.39/26.45  tff(c_16, plain, (![A_12, B_13]: (v1_relat_1(k7_relat_1(A_12, B_13)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 36.39/26.45  tff(c_22, plain, (![A_18]: (k10_relat_1(A_18, k2_relat_1(A_18))=k1_relat_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 36.39/26.45  tff(c_281, plain, (![C_65, A_66, B_67]: (r1_tarski(k10_relat_1(C_65, A_66), k10_relat_1(C_65, B_67)) | ~r1_tarski(A_66, B_67) | ~v1_relat_1(C_65))), inference(cnfTransformation, [status(thm)], [f_69])).
% 36.39/26.45  tff(c_2389, plain, (![A_185, B_186]: (r1_tarski(k1_relat_1(A_185), k10_relat_1(A_185, B_186)) | ~r1_tarski(k2_relat_1(A_185), B_186) | ~v1_relat_1(A_185) | ~v1_relat_1(A_185))), inference(superposition, [status(thm), theory('equality')], [c_22, c_281])).
% 36.39/26.45  tff(c_36, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 36.39/26.45  tff(c_862, plain, (![A_110, B_111]: (r1_tarski('#skF_1', k2_xboole_0(A_110, B_111)) | ~r1_tarski(k1_relat_1('#skF_2'), A_110))), inference(resolution, [status(thm)], [c_36, c_833])).
% 36.39/26.45  tff(c_2400, plain, (![B_186, B_111]: (r1_tarski('#skF_1', k2_xboole_0(k10_relat_1('#skF_2', B_186), B_111)) | ~r1_tarski(k2_relat_1('#skF_2'), B_186) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_2389, c_862])).
% 36.39/26.45  tff(c_2625, plain, (![B_196, B_197]: (r1_tarski('#skF_1', k2_xboole_0(k10_relat_1('#skF_2', B_196), B_197)) | ~r1_tarski(k2_relat_1('#skF_2'), B_196))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2400])).
% 36.39/26.45  tff(c_2686, plain, (![B_198]: (r1_tarski('#skF_1', k10_relat_1('#skF_2', B_198)) | ~r1_tarski(k2_relat_1('#skF_2'), B_198))), inference(superposition, [status(thm), theory('equality')], [c_55, c_2625])).
% 36.39/26.45  tff(c_2726, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k2_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_6, c_2686])).
% 36.39/26.45  tff(c_12, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 36.39/26.45  tff(c_2759, plain, (k3_xboole_0('#skF_1', k10_relat_1('#skF_2', k2_relat_1('#skF_2')))='#skF_1'), inference(resolution, [status(thm)], [c_2726, c_12])).
% 36.39/26.45  tff(c_32, plain, (![A_30, C_32, B_31]: (k3_xboole_0(A_30, k10_relat_1(C_32, B_31))=k10_relat_1(k7_relat_1(C_32, A_30), B_31) | ~v1_relat_1(C_32))), inference(cnfTransformation, [status(thm)], [f_90])).
% 36.39/26.45  tff(c_2766, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1('#skF_2'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2759, c_32])).
% 36.39/26.45  tff(c_2776, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2766])).
% 36.39/26.45  tff(c_20, plain, (![B_17, A_16]: (r1_tarski(k10_relat_1(B_17, A_16), k1_relat_1(B_17)) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 36.39/26.45  tff(c_2818, plain, (r1_tarski('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2776, c_20])).
% 36.39/26.45  tff(c_3620, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_2818])).
% 36.39/26.45  tff(c_3623, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_3620])).
% 36.39/26.45  tff(c_3627, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_3623])).
% 36.39/26.45  tff(c_3629, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_2818])).
% 36.39/26.45  tff(c_3628, plain, (r1_tarski('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_2818])).
% 36.39/26.45  tff(c_28, plain, (![B_27, A_26]: (r1_tarski(k1_relat_1(k7_relat_1(B_27, A_26)), A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_82])).
% 36.39/26.45  tff(c_160, plain, (![B_53, A_54]: (B_53=A_54 | ~r1_tarski(B_53, A_54) | ~r1_tarski(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_31])).
% 36.39/26.45  tff(c_174, plain, (![B_27, A_26]: (k1_relat_1(k7_relat_1(B_27, A_26))=A_26 | ~r1_tarski(A_26, k1_relat_1(k7_relat_1(B_27, A_26))) | ~v1_relat_1(B_27))), inference(resolution, [status(thm)], [c_28, c_160])).
% 36.39/26.45  tff(c_3736, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_3628, c_174])).
% 36.39/26.45  tff(c_3758, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_3736])).
% 36.39/26.45  tff(c_235, plain, (![B_59, A_60]: (k2_relat_1(k7_relat_1(B_59, A_60))=k9_relat_1(B_59, A_60) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_55])).
% 36.39/26.45  tff(c_241, plain, (![B_59, A_60]: (k10_relat_1(k7_relat_1(B_59, A_60), k9_relat_1(B_59, A_60))=k1_relat_1(k7_relat_1(B_59, A_60)) | ~v1_relat_1(k7_relat_1(B_59, A_60)) | ~v1_relat_1(B_59))), inference(superposition, [status(thm), theory('equality')], [c_235, c_22])).
% 36.39/26.45  tff(c_766, plain, (![B_102, A_103, C_104]: (r1_tarski(k10_relat_1(B_102, A_103), k10_relat_1(C_104, A_103)) | ~r1_tarski(B_102, C_104) | ~v1_relat_1(C_104) | ~v1_relat_1(B_102))), inference(cnfTransformation, [status(thm)], [f_78])).
% 36.39/26.45  tff(c_7023, plain, (![A_307, C_308, A_309, B_310]: (r1_tarski(A_307, k10_relat_1(C_308, A_309)) | ~r1_tarski(A_307, k10_relat_1(B_310, A_309)) | ~r1_tarski(B_310, C_308) | ~v1_relat_1(C_308) | ~v1_relat_1(B_310))), inference(resolution, [status(thm)], [c_766, c_10])).
% 36.39/26.45  tff(c_119061, plain, (![A_1529, C_1530, B_1531, A_1532]: (r1_tarski(A_1529, k10_relat_1(C_1530, k9_relat_1(B_1531, A_1532))) | ~r1_tarski(A_1529, k1_relat_1(k7_relat_1(B_1531, A_1532))) | ~r1_tarski(k7_relat_1(B_1531, A_1532), C_1530) | ~v1_relat_1(C_1530) | ~v1_relat_1(k7_relat_1(B_1531, A_1532)) | ~v1_relat_1(k7_relat_1(B_1531, A_1532)) | ~v1_relat_1(B_1531))), inference(superposition, [status(thm), theory('equality')], [c_241, c_7023])).
% 36.39/26.45  tff(c_34, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 36.39/26.45  tff(c_119461, plain, (~r1_tarski('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))) | ~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_119061, c_34])).
% 36.39/26.45  tff(c_119677, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_3629, c_6, c_3758, c_119461])).
% 36.39/26.45  tff(c_119694, plain, (~r1_tarski('#skF_2', '#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_9872, c_119677])).
% 36.39/26.45  tff(c_119704, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_6, c_119694])).
% 36.39/26.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 36.39/26.45  
% 36.39/26.45  Inference rules
% 36.39/26.45  ----------------------
% 36.39/26.45  #Ref     : 0
% 36.39/26.45  #Sup     : 30491
% 36.39/26.45  #Fact    : 0
% 36.39/26.45  #Define  : 0
% 36.39/26.45  #Split   : 14
% 36.39/26.45  #Chain   : 0
% 36.39/26.45  #Close   : 0
% 36.39/26.45  
% 36.39/26.45  Ordering : KBO
% 36.39/26.45  
% 36.39/26.45  Simplification rules
% 36.39/26.45  ----------------------
% 36.39/26.45  #Subsume      : 6453
% 36.39/26.45  #Demod        : 16932
% 36.39/26.45  #Tautology    : 5557
% 36.39/26.45  #SimpNegUnit  : 18
% 36.39/26.45  #BackRed      : 9
% 36.39/26.45  
% 36.39/26.45  #Partial instantiations: 0
% 36.39/26.45  #Strategies tried      : 1
% 36.39/26.45  
% 36.39/26.45  Timing (in seconds)
% 36.39/26.45  ----------------------
% 36.39/26.45  Preprocessing        : 0.31
% 36.39/26.45  Parsing              : 0.17
% 36.39/26.45  CNF conversion       : 0.02
% 36.39/26.45  Main loop            : 25.38
% 36.39/26.45  Inferencing          : 2.93
% 36.39/26.45  Reduction            : 8.73
% 36.39/26.45  Demodulation         : 7.23
% 36.39/26.45  BG Simplification    : 0.40
% 36.39/26.45  Subsumption          : 11.99
% 36.39/26.45  Abstraction          : 0.59
% 36.39/26.45  MUC search           : 0.00
% 36.39/26.45  Cooper               : 0.00
% 36.39/26.45  Total                : 25.73
% 36.39/26.45  Index Insertion      : 0.00
% 36.39/26.45  Index Deletion       : 0.00
% 36.39/26.45  Index Matching       : 0.00
% 36.39/26.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
