%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:24 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 189 expanded)
%              Number of leaves         :   22 (  71 expanded)
%              Depth                    :   10
%              Number of atoms          :  105 ( 292 expanded)
%              Number of equality atoms :   12 (  66 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k5_xboole_0(B,C))
      <=> ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(c_26,plain,
    ( ~ r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3'))
    | r1_tarski('#skF_4',k5_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_146,plain,(
    ~ r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,
    ( r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | r1_tarski('#skF_4',k5_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_31,plain,
    ( r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2'))
    | r1_tarski('#skF_4',k5_xboole_0('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_30])).

tff(c_147,plain,(
    r1_tarski('#skF_4',k5_xboole_0('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_31])).

tff(c_119,plain,(
    ! [A_36,B_37] : k4_xboole_0(k2_xboole_0(A_36,B_37),k3_xboole_0(A_36,B_37)) = k5_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_xboole_0(A_5,C_7)
      | ~ r1_tarski(A_5,k4_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_296,plain,(
    ! [A_56,A_57,B_58] :
      ( r1_xboole_0(A_56,k3_xboole_0(A_57,B_58))
      | ~ r1_tarski(A_56,k5_xboole_0(A_57,B_58)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_6])).

tff(c_24,plain,
    ( r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | ~ r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_6'))
    | ~ r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_32,plain,
    ( r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2'))
    | ~ r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_6'))
    | ~ r1_tarski('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_24])).

tff(c_171,plain,(
    ~ r1_tarski('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_8,plain,(
    ! [A_5,B_6,C_7] :
      ( r1_tarski(A_5,B_6)
      | ~ r1_tarski(A_5,k4_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_276,plain,(
    ! [A_53,A_54,B_55] :
      ( r1_tarski(A_53,k2_xboole_0(A_54,B_55))
      | ~ r1_tarski(A_53,k5_xboole_0(A_54,B_55)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_8])).

tff(c_283,plain,(
    r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_147,c_276])).

tff(c_286,plain,(
    r1_tarski('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_283])).

tff(c_288,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_171,c_286])).

tff(c_289,plain,
    ( ~ r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_6'))
    | r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_291,plain,(
    ~ r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_289])).

tff(c_299,plain,(
    ~ r1_tarski('#skF_4',k5_xboole_0('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_296,c_291])).

tff(c_306,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_299])).

tff(c_307,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_289])).

tff(c_98,plain,(
    ! [A_34,B_35] : k2_xboole_0(k5_xboole_0(A_34,B_35),k3_xboole_0(A_34,B_35)) = k2_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_113,plain,(
    ! [A_34,B_35] : k2_xboole_0(k3_xboole_0(A_34,B_35),k5_xboole_0(A_34,B_35)) = k2_xboole_0(A_34,B_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_98])).

tff(c_290,plain,(
    r1_tarski('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_308,plain,(
    r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_289])).

tff(c_22,plain,
    ( r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3'))
    | ~ r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_6'))
    | ~ r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_33,plain,
    ( r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3'))
    | ~ r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_6'))
    | ~ r1_tarski('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_22])).

tff(c_335,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_308,c_33])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = A_13
      | ~ r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_339,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_335,c_14])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] :
      ( r1_tarski(k4_xboole_0(A_8,B_9),C_10)
      | ~ r1_tarski(A_8,k2_xboole_0(B_9,C_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_563,plain,(
    ! [C_70] :
      ( r1_tarski('#skF_1',C_70)
      | ~ r1_tarski('#skF_1',k2_xboole_0(k3_xboole_0('#skF_2','#skF_3'),C_70)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_10])).

tff(c_567,plain,
    ( r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3'))
    | ~ r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_563])).

tff(c_577,plain,(
    r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_2,c_567])).

tff(c_579,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_577])).

tff(c_580,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_31])).

tff(c_116,plain,(
    ! [A_34,B_35] : k2_xboole_0(k3_xboole_0(A_34,B_35),k5_xboole_0(A_34,B_35)) = k2_xboole_0(A_34,B_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_98])).

tff(c_581,plain,(
    ~ r1_tarski('#skF_4',k5_xboole_0('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_31])).

tff(c_28,plain,
    ( r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3'))
    | r1_tarski('#skF_4',k5_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_582,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_581,c_28])).

tff(c_586,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_582,c_14])).

tff(c_605,plain,(
    ! [A_72,B_73,C_74] :
      ( r1_tarski(k4_xboole_0(A_72,B_73),C_74)
      | ~ r1_tarski(A_72,k2_xboole_0(B_73,C_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_871,plain,(
    ! [C_98] :
      ( r1_tarski('#skF_1',C_98)
      | ~ r1_tarski('#skF_1',k2_xboole_0(k3_xboole_0('#skF_2','#skF_3'),C_98)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_586,c_605])).

tff(c_875,plain,
    ( r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3'))
    | ~ r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_871])).

tff(c_885,plain,(
    r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_2,c_875])).

tff(c_887,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_885])).

tff(c_888,plain,(
    r1_tarski('#skF_4',k5_xboole_0('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_1089,plain,(
    ! [A_119,A_120,B_121] :
      ( r1_xboole_0(A_119,k3_xboole_0(A_120,B_121))
      | ~ r1_tarski(A_119,k5_xboole_0(A_120,B_121)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_6])).

tff(c_889,plain,(
    r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_20,plain,
    ( ~ r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3'))
    | ~ r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_6'))
    | ~ r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_34,plain,
    ( ~ r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3'))
    | ~ r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_6'))
    | ~ r1_tarski('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_916,plain,
    ( ~ r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_6'))
    | ~ r1_tarski('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_889,c_34])).

tff(c_917,plain,(
    ~ r1_tarski('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_916])).

tff(c_1018,plain,(
    ! [A_111,A_112,B_113] :
      ( r1_tarski(A_111,k2_xboole_0(A_112,B_113))
      | ~ r1_tarski(A_111,k5_xboole_0(A_112,B_113)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_8])).

tff(c_1028,plain,(
    r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_888,c_1018])).

tff(c_1033,plain,(
    r1_tarski('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1028])).

tff(c_1035,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_917,c_1033])).

tff(c_1036,plain,(
    ~ r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_916])).

tff(c_1092,plain,(
    ~ r1_tarski('#skF_4',k5_xboole_0('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_1089,c_1036])).

tff(c_1099,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_888,c_1092])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:21:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.44  
% 2.59/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.44  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.59/1.44  
% 2.59/1.44  %Foreground sorts:
% 2.59/1.44  
% 2.59/1.44  
% 2.59/1.44  %Background operators:
% 2.59/1.44  
% 2.59/1.44  
% 2.59/1.44  %Foreground operators:
% 2.59/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.59/1.44  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.59/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.59/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.59/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.59/1.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.59/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.59/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.59/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.59/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.59/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.59/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.59/1.44  
% 2.87/1.46  tff(f_54, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k5_xboole_0(B, C)) <=> (r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, k3_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_xboole_1)).
% 2.87/1.46  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.87/1.46  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l98_xboole_1)).
% 2.87/1.46  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.87/1.46  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_xboole_1)).
% 2.87/1.46  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.87/1.46  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 2.87/1.46  tff(c_26, plain, (~r1_tarski('#skF_1', k5_xboole_0('#skF_2', '#skF_3')) | r1_tarski('#skF_4', k5_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.87/1.46  tff(c_146, plain, (~r1_tarski('#skF_1', k5_xboole_0('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_26])).
% 2.87/1.46  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.87/1.46  tff(c_30, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | r1_tarski('#skF_4', k5_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.87/1.46  tff(c_31, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2')) | r1_tarski('#skF_4', k5_xboole_0('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_30])).
% 2.87/1.46  tff(c_147, plain, (r1_tarski('#skF_4', k5_xboole_0('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_31])).
% 2.87/1.46  tff(c_119, plain, (![A_36, B_37]: (k4_xboole_0(k2_xboole_0(A_36, B_37), k3_xboole_0(A_36, B_37))=k5_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.87/1.46  tff(c_6, plain, (![A_5, C_7, B_6]: (r1_xboole_0(A_5, C_7) | ~r1_tarski(A_5, k4_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.87/1.46  tff(c_296, plain, (![A_56, A_57, B_58]: (r1_xboole_0(A_56, k3_xboole_0(A_57, B_58)) | ~r1_tarski(A_56, k5_xboole_0(A_57, B_58)))), inference(superposition, [status(thm), theory('equality')], [c_119, c_6])).
% 2.87/1.46  tff(c_24, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | ~r1_xboole_0('#skF_4', k3_xboole_0('#skF_5', '#skF_6')) | ~r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.87/1.46  tff(c_32, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2')) | ~r1_xboole_0('#skF_4', k3_xboole_0('#skF_5', '#skF_6')) | ~r1_tarski('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_24])).
% 2.87/1.46  tff(c_171, plain, (~r1_tarski('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_32])).
% 2.87/1.46  tff(c_8, plain, (![A_5, B_6, C_7]: (r1_tarski(A_5, B_6) | ~r1_tarski(A_5, k4_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.87/1.46  tff(c_276, plain, (![A_53, A_54, B_55]: (r1_tarski(A_53, k2_xboole_0(A_54, B_55)) | ~r1_tarski(A_53, k5_xboole_0(A_54, B_55)))), inference(superposition, [status(thm), theory('equality')], [c_119, c_8])).
% 2.87/1.46  tff(c_283, plain, (r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_147, c_276])).
% 2.87/1.46  tff(c_286, plain, (r1_tarski('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_283])).
% 2.87/1.46  tff(c_288, plain, $false, inference(negUnitSimplification, [status(thm)], [c_171, c_286])).
% 2.87/1.46  tff(c_289, plain, (~r1_xboole_0('#skF_4', k3_xboole_0('#skF_5', '#skF_6')) | r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_32])).
% 2.87/1.46  tff(c_291, plain, (~r1_xboole_0('#skF_4', k3_xboole_0('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_289])).
% 2.87/1.46  tff(c_299, plain, (~r1_tarski('#skF_4', k5_xboole_0('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_296, c_291])).
% 2.87/1.46  tff(c_306, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_147, c_299])).
% 2.87/1.46  tff(c_307, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_289])).
% 2.87/1.46  tff(c_98, plain, (![A_34, B_35]: (k2_xboole_0(k5_xboole_0(A_34, B_35), k3_xboole_0(A_34, B_35))=k2_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.87/1.46  tff(c_113, plain, (![A_34, B_35]: (k2_xboole_0(k3_xboole_0(A_34, B_35), k5_xboole_0(A_34, B_35))=k2_xboole_0(A_34, B_35))), inference(superposition, [status(thm), theory('equality')], [c_2, c_98])).
% 2.87/1.46  tff(c_290, plain, (r1_tarski('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitRight, [status(thm)], [c_32])).
% 2.87/1.46  tff(c_308, plain, (r1_xboole_0('#skF_4', k3_xboole_0('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_289])).
% 2.87/1.46  tff(c_22, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3')) | ~r1_xboole_0('#skF_4', k3_xboole_0('#skF_5', '#skF_6')) | ~r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.87/1.46  tff(c_33, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3')) | ~r1_xboole_0('#skF_4', k3_xboole_0('#skF_5', '#skF_6')) | ~r1_tarski('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_22])).
% 2.87/1.46  tff(c_335, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_290, c_308, c_33])).
% 2.87/1.46  tff(c_14, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=A_13 | ~r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.87/1.46  tff(c_339, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_335, c_14])).
% 2.87/1.46  tff(c_10, plain, (![A_8, B_9, C_10]: (r1_tarski(k4_xboole_0(A_8, B_9), C_10) | ~r1_tarski(A_8, k2_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.87/1.46  tff(c_563, plain, (![C_70]: (r1_tarski('#skF_1', C_70) | ~r1_tarski('#skF_1', k2_xboole_0(k3_xboole_0('#skF_2', '#skF_3'), C_70)))), inference(superposition, [status(thm), theory('equality')], [c_339, c_10])).
% 2.87/1.46  tff(c_567, plain, (r1_tarski('#skF_1', k5_xboole_0('#skF_2', '#skF_3')) | ~r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_113, c_563])).
% 2.87/1.46  tff(c_577, plain, (r1_tarski('#skF_1', k5_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_307, c_2, c_567])).
% 2.87/1.46  tff(c_579, plain, $false, inference(negUnitSimplification, [status(thm)], [c_146, c_577])).
% 2.87/1.46  tff(c_580, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_31])).
% 2.87/1.46  tff(c_116, plain, (![A_34, B_35]: (k2_xboole_0(k3_xboole_0(A_34, B_35), k5_xboole_0(A_34, B_35))=k2_xboole_0(A_34, B_35))), inference(superposition, [status(thm), theory('equality')], [c_2, c_98])).
% 2.87/1.46  tff(c_581, plain, (~r1_tarski('#skF_4', k5_xboole_0('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_31])).
% 2.87/1.46  tff(c_28, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3')) | r1_tarski('#skF_4', k5_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.87/1.46  tff(c_582, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_581, c_28])).
% 2.87/1.46  tff(c_586, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_582, c_14])).
% 2.87/1.46  tff(c_605, plain, (![A_72, B_73, C_74]: (r1_tarski(k4_xboole_0(A_72, B_73), C_74) | ~r1_tarski(A_72, k2_xboole_0(B_73, C_74)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.87/1.46  tff(c_871, plain, (![C_98]: (r1_tarski('#skF_1', C_98) | ~r1_tarski('#skF_1', k2_xboole_0(k3_xboole_0('#skF_2', '#skF_3'), C_98)))), inference(superposition, [status(thm), theory('equality')], [c_586, c_605])).
% 2.87/1.46  tff(c_875, plain, (r1_tarski('#skF_1', k5_xboole_0('#skF_2', '#skF_3')) | ~r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_871])).
% 2.87/1.46  tff(c_885, plain, (r1_tarski('#skF_1', k5_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_580, c_2, c_875])).
% 2.87/1.46  tff(c_887, plain, $false, inference(negUnitSimplification, [status(thm)], [c_146, c_885])).
% 2.87/1.46  tff(c_888, plain, (r1_tarski('#skF_4', k5_xboole_0('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_26])).
% 2.87/1.46  tff(c_1089, plain, (![A_119, A_120, B_121]: (r1_xboole_0(A_119, k3_xboole_0(A_120, B_121)) | ~r1_tarski(A_119, k5_xboole_0(A_120, B_121)))), inference(superposition, [status(thm), theory('equality')], [c_119, c_6])).
% 2.87/1.46  tff(c_889, plain, (r1_tarski('#skF_1', k5_xboole_0('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_26])).
% 2.87/1.46  tff(c_20, plain, (~r1_tarski('#skF_1', k5_xboole_0('#skF_2', '#skF_3')) | ~r1_xboole_0('#skF_4', k3_xboole_0('#skF_5', '#skF_6')) | ~r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.87/1.46  tff(c_34, plain, (~r1_tarski('#skF_1', k5_xboole_0('#skF_2', '#skF_3')) | ~r1_xboole_0('#skF_4', k3_xboole_0('#skF_5', '#skF_6')) | ~r1_tarski('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20])).
% 2.87/1.46  tff(c_916, plain, (~r1_xboole_0('#skF_4', k3_xboole_0('#skF_5', '#skF_6')) | ~r1_tarski('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_889, c_34])).
% 2.87/1.46  tff(c_917, plain, (~r1_tarski('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_916])).
% 2.87/1.46  tff(c_1018, plain, (![A_111, A_112, B_113]: (r1_tarski(A_111, k2_xboole_0(A_112, B_113)) | ~r1_tarski(A_111, k5_xboole_0(A_112, B_113)))), inference(superposition, [status(thm), theory('equality')], [c_119, c_8])).
% 2.87/1.46  tff(c_1028, plain, (r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_888, c_1018])).
% 2.87/1.46  tff(c_1033, plain, (r1_tarski('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1028])).
% 2.87/1.46  tff(c_1035, plain, $false, inference(negUnitSimplification, [status(thm)], [c_917, c_1033])).
% 2.87/1.46  tff(c_1036, plain, (~r1_xboole_0('#skF_4', k3_xboole_0('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_916])).
% 2.87/1.46  tff(c_1092, plain, (~r1_tarski('#skF_4', k5_xboole_0('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_1089, c_1036])).
% 2.87/1.46  tff(c_1099, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_888, c_1092])).
% 2.87/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.46  
% 2.87/1.46  Inference rules
% 2.87/1.46  ----------------------
% 2.87/1.46  #Ref     : 0
% 2.87/1.46  #Sup     : 268
% 2.87/1.46  #Fact    : 0
% 2.87/1.46  #Define  : 0
% 2.87/1.46  #Split   : 8
% 2.87/1.46  #Chain   : 0
% 2.87/1.46  #Close   : 0
% 2.87/1.46  
% 2.87/1.46  Ordering : KBO
% 2.87/1.46  
% 2.87/1.46  Simplification rules
% 2.87/1.46  ----------------------
% 2.87/1.46  #Subsume      : 20
% 2.87/1.46  #Demod        : 65
% 2.87/1.46  #Tautology    : 106
% 2.87/1.46  #SimpNegUnit  : 5
% 2.87/1.46  #BackRed      : 0
% 2.87/1.46  
% 2.87/1.46  #Partial instantiations: 0
% 2.87/1.46  #Strategies tried      : 1
% 2.87/1.46  
% 2.87/1.46  Timing (in seconds)
% 2.87/1.46  ----------------------
% 2.87/1.46  Preprocessing        : 0.27
% 2.87/1.46  Parsing              : 0.15
% 2.87/1.46  CNF conversion       : 0.02
% 2.87/1.46  Main loop            : 0.41
% 2.87/1.46  Inferencing          : 0.14
% 2.87/1.46  Reduction            : 0.15
% 2.87/1.46  Demodulation         : 0.11
% 2.87/1.46  BG Simplification    : 0.02
% 2.87/1.46  Subsumption          : 0.07
% 2.87/1.46  Abstraction          : 0.02
% 2.87/1.46  MUC search           : 0.00
% 2.87/1.46  Cooper               : 0.00
% 2.87/1.46  Total                : 0.72
% 2.87/1.46  Index Insertion      : 0.00
% 2.87/1.46  Index Deletion       : 0.00
% 2.87/1.46  Index Matching       : 0.00
% 2.87/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
