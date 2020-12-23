%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:14 EST 2020

% Result     : Theorem 11.54s
% Output     : CNFRefutation 11.64s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 141 expanded)
%              Number of leaves         :   29 (  58 expanded)
%              Depth                    :   12
%              Number of atoms          :  144 ( 303 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,B)
            <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_82,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_78,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_87,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_68,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_42,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_44,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_4379,plain,(
    ! [A_472,B_473] :
      ( r1_tarski(A_472,B_473)
      | ~ r1_ordinal1(A_472,B_473)
      | ~ v3_ordinal1(B_473)
      | ~ v3_ordinal1(A_472) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_46,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3')
    | ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_79,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_38,plain,(
    ! [A_36] :
      ( v3_ordinal1(k1_ordinal1(A_36))
      | ~ v3_ordinal1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_52,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_80,plain,(
    r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_34,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | ~ r1_ordinal1(A_33,B_34)
      | ~ v3_ordinal1(B_34)
      | ~ v3_ordinal1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_36,plain,(
    ! [A_35] : r2_hidden(A_35,k1_ordinal1(A_35)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_235,plain,(
    ! [C_80,B_81,A_82] :
      ( r2_hidden(C_80,B_81)
      | ~ r2_hidden(C_80,A_82)
      | ~ r1_tarski(A_82,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_582,plain,(
    ! [A_120,B_121] :
      ( r2_hidden(A_120,B_121)
      | ~ r1_tarski(k1_ordinal1(A_120),B_121) ) ),
    inference(resolution,[status(thm)],[c_36,c_235])).

tff(c_3959,plain,(
    ! [A_413,B_414] :
      ( r2_hidden(A_413,B_414)
      | ~ r1_ordinal1(k1_ordinal1(A_413),B_414)
      | ~ v3_ordinal1(B_414)
      | ~ v3_ordinal1(k1_ordinal1(A_413)) ) ),
    inference(resolution,[status(thm)],[c_34,c_582])).

tff(c_3982,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_80,c_3959])).

tff(c_3992,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3982])).

tff(c_3993,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_3992])).

tff(c_3996,plain,(
    ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_3993])).

tff(c_4000,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3996])).

tff(c_4001,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_4003,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_4001])).

tff(c_4005,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_40,plain,(
    ! [B_38,A_37] :
      ( ~ r1_tarski(B_38,A_37)
      | ~ r2_hidden(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4017,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_4005,c_40])).

tff(c_4421,plain,
    ( ~ r1_ordinal1('#skF_3','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4379,c_4017])).

tff(c_4440,plain,(
    ~ r1_ordinal1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_4421])).

tff(c_28,plain,(
    ! [B_31,A_30] :
      ( r1_ordinal1(B_31,A_30)
      | r1_ordinal1(A_30,B_31)
      | ~ v3_ordinal1(B_31)
      | ~ v3_ordinal1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4299,plain,(
    ! [B_463,A_464] :
      ( r1_ordinal1(B_463,A_464)
      | r1_ordinal1(A_464,B_463)
      | ~ v3_ordinal1(B_463)
      | ~ v3_ordinal1(A_464) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4004,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_4006,plain,(
    r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_4011,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4004,c_4006])).

tff(c_4013,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_4302,plain,
    ( r1_ordinal1('#skF_3',k1_ordinal1('#skF_2'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_2'))
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4299,c_4013])).

tff(c_4308,plain,
    ( r1_ordinal1('#skF_3',k1_ordinal1('#skF_2'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_4302])).

tff(c_4325,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_4308])).

tff(c_4328,plain,(
    ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_4325])).

tff(c_4332,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_4328])).

tff(c_4334,plain,(
    v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_4308])).

tff(c_12,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4874,plain,(
    ! [A_526,B_527,C_528] :
      ( r1_tarski(k2_tarski(A_526,B_527),C_528)
      | ~ r2_hidden(B_527,C_528)
      | ~ r2_hidden(A_526,C_528) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4899,plain,(
    ! [A_12,C_528] :
      ( r1_tarski(k1_tarski(A_12),C_528)
      | ~ r2_hidden(A_12,C_528)
      | ~ r2_hidden(A_12,C_528) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_4874])).

tff(c_30,plain,(
    ! [A_32] : k2_xboole_0(A_32,k1_tarski(A_32)) = k1_ordinal1(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_5057,plain,(
    ! [A_544,C_545,B_546] :
      ( r1_tarski(k2_xboole_0(A_544,C_545),B_546)
      | ~ r1_tarski(C_545,B_546)
      | ~ r1_tarski(A_544,B_546) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_32,plain,(
    ! [A_33,B_34] :
      ( r1_ordinal1(A_33,B_34)
      | ~ r1_tarski(A_33,B_34)
      | ~ v3_ordinal1(B_34)
      | ~ v3_ordinal1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6765,plain,(
    ! [A_707,C_708,B_709] :
      ( r1_ordinal1(k2_xboole_0(A_707,C_708),B_709)
      | ~ v3_ordinal1(B_709)
      | ~ v3_ordinal1(k2_xboole_0(A_707,C_708))
      | ~ r1_tarski(C_708,B_709)
      | ~ r1_tarski(A_707,B_709) ) ),
    inference(resolution,[status(thm)],[c_5057,c_32])).

tff(c_6774,plain,(
    ! [A_32,B_709] :
      ( r1_ordinal1(k1_ordinal1(A_32),B_709)
      | ~ v3_ordinal1(B_709)
      | ~ v3_ordinal1(k2_xboole_0(A_32,k1_tarski(A_32)))
      | ~ r1_tarski(k1_tarski(A_32),B_709)
      | ~ r1_tarski(A_32,B_709) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_6765])).

tff(c_12299,plain,(
    ! [A_1052,B_1053] :
      ( r1_ordinal1(k1_ordinal1(A_1052),B_1053)
      | ~ v3_ordinal1(B_1053)
      | ~ v3_ordinal1(k1_ordinal1(A_1052))
      | ~ r1_tarski(k1_tarski(A_1052),B_1053)
      | ~ r1_tarski(A_1052,B_1053) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_6774])).

tff(c_21327,plain,(
    ! [A_1418,C_1419] :
      ( r1_ordinal1(k1_ordinal1(A_1418),C_1419)
      | ~ v3_ordinal1(C_1419)
      | ~ v3_ordinal1(k1_ordinal1(A_1418))
      | ~ r1_tarski(A_1418,C_1419)
      | ~ r2_hidden(A_1418,C_1419) ) ),
    inference(resolution,[status(thm)],[c_4899,c_12299])).

tff(c_21361,plain,
    ( ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_3')
    | ~ r2_hidden('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_21327,c_4013])).

tff(c_21385,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4005,c_4334,c_42,c_21361])).

tff(c_21388,plain,
    ( ~ r1_ordinal1('#skF_2','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_21385])).

tff(c_21391,plain,(
    ~ r1_ordinal1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_21388])).

tff(c_21397,plain,
    ( r1_ordinal1('#skF_3','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_21391])).

tff(c_21406,plain,(
    r1_ordinal1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_21397])).

tff(c_21408,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4440,c_21406])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:39:19 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.54/5.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.54/5.41  
% 11.54/5.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.54/5.41  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_3 > #skF_1
% 11.54/5.41  
% 11.54/5.41  %Foreground sorts:
% 11.54/5.41  
% 11.54/5.41  
% 11.54/5.41  %Background operators:
% 11.54/5.41  
% 11.54/5.41  
% 11.54/5.41  %Foreground operators:
% 11.54/5.41  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 11.54/5.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.54/5.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.54/5.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.54/5.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.54/5.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.54/5.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.54/5.41  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 11.54/5.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.54/5.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.54/5.41  tff('#skF_2', type, '#skF_2': $i).
% 11.54/5.41  tff('#skF_3', type, '#skF_3': $i).
% 11.54/5.41  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 11.54/5.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.54/5.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.54/5.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.54/5.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.54/5.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.54/5.41  
% 11.64/5.43  tff(f_97, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_ordinal1)).
% 11.64/5.43  tff(f_76, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 11.64/5.43  tff(f_82, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 11.64/5.43  tff(f_78, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 11.64/5.43  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 11.64/5.43  tff(f_87, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 11.64/5.43  tff(f_66, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 11.64/5.43  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 11.64/5.43  tff(f_58, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 11.64/5.43  tff(f_68, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 11.64/5.43  tff(f_42, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 11.64/5.43  tff(c_42, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.64/5.43  tff(c_44, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.64/5.43  tff(c_4379, plain, (![A_472, B_473]: (r1_tarski(A_472, B_473) | ~r1_ordinal1(A_472, B_473) | ~v3_ordinal1(B_473) | ~v3_ordinal1(A_472))), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.64/5.43  tff(c_46, plain, (~r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3') | ~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.64/5.43  tff(c_79, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_46])).
% 11.64/5.43  tff(c_38, plain, (![A_36]: (v3_ordinal1(k1_ordinal1(A_36)) | ~v3_ordinal1(A_36))), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.64/5.43  tff(c_52, plain, (r2_hidden('#skF_2', '#skF_3') | r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.64/5.43  tff(c_80, plain, (r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_52])).
% 11.64/5.43  tff(c_34, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | ~r1_ordinal1(A_33, B_34) | ~v3_ordinal1(B_34) | ~v3_ordinal1(A_33))), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.64/5.43  tff(c_36, plain, (![A_35]: (r2_hidden(A_35, k1_ordinal1(A_35)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.64/5.43  tff(c_235, plain, (![C_80, B_81, A_82]: (r2_hidden(C_80, B_81) | ~r2_hidden(C_80, A_82) | ~r1_tarski(A_82, B_81))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.64/5.43  tff(c_582, plain, (![A_120, B_121]: (r2_hidden(A_120, B_121) | ~r1_tarski(k1_ordinal1(A_120), B_121))), inference(resolution, [status(thm)], [c_36, c_235])).
% 11.64/5.43  tff(c_3959, plain, (![A_413, B_414]: (r2_hidden(A_413, B_414) | ~r1_ordinal1(k1_ordinal1(A_413), B_414) | ~v3_ordinal1(B_414) | ~v3_ordinal1(k1_ordinal1(A_413)))), inference(resolution, [status(thm)], [c_34, c_582])).
% 11.64/5.43  tff(c_3982, plain, (r2_hidden('#skF_2', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(resolution, [status(thm)], [c_80, c_3959])).
% 11.64/5.43  tff(c_3992, plain, (r2_hidden('#skF_2', '#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_3982])).
% 11.64/5.43  tff(c_3993, plain, (~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_79, c_3992])).
% 11.64/5.43  tff(c_3996, plain, (~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_38, c_3993])).
% 11.64/5.43  tff(c_4000, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_3996])).
% 11.64/5.43  tff(c_4001, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_52])).
% 11.64/5.43  tff(c_4003, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_4001])).
% 11.64/5.43  tff(c_4005, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_46])).
% 11.64/5.43  tff(c_40, plain, (![B_38, A_37]: (~r1_tarski(B_38, A_37) | ~r2_hidden(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_87])).
% 11.64/5.43  tff(c_4017, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_4005, c_40])).
% 11.64/5.43  tff(c_4421, plain, (~r1_ordinal1('#skF_3', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_4379, c_4017])).
% 11.64/5.43  tff(c_4440, plain, (~r1_ordinal1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_4421])).
% 11.64/5.43  tff(c_28, plain, (![B_31, A_30]: (r1_ordinal1(B_31, A_30) | r1_ordinal1(A_30, B_31) | ~v3_ordinal1(B_31) | ~v3_ordinal1(A_30))), inference(cnfTransformation, [status(thm)], [f_66])).
% 11.64/5.43  tff(c_4299, plain, (![B_463, A_464]: (r1_ordinal1(B_463, A_464) | r1_ordinal1(A_464, B_463) | ~v3_ordinal1(B_463) | ~v3_ordinal1(A_464))), inference(cnfTransformation, [status(thm)], [f_66])).
% 11.64/5.43  tff(c_4004, plain, (~r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_46])).
% 11.64/5.43  tff(c_4006, plain, (r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_52])).
% 11.64/5.43  tff(c_4011, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4004, c_4006])).
% 11.64/5.43  tff(c_4013, plain, (~r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_52])).
% 11.64/5.43  tff(c_4302, plain, (r1_ordinal1('#skF_3', k1_ordinal1('#skF_2')) | ~v3_ordinal1(k1_ordinal1('#skF_2')) | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_4299, c_4013])).
% 11.64/5.43  tff(c_4308, plain, (r1_ordinal1('#skF_3', k1_ordinal1('#skF_2')) | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_4302])).
% 11.64/5.43  tff(c_4325, plain, (~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(splitLeft, [status(thm)], [c_4308])).
% 11.64/5.43  tff(c_4328, plain, (~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_38, c_4325])).
% 11.64/5.43  tff(c_4332, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_4328])).
% 11.64/5.43  tff(c_4334, plain, (v3_ordinal1(k1_ordinal1('#skF_2'))), inference(splitRight, [status(thm)], [c_4308])).
% 11.64/5.43  tff(c_12, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.64/5.43  tff(c_4874, plain, (![A_526, B_527, C_528]: (r1_tarski(k2_tarski(A_526, B_527), C_528) | ~r2_hidden(B_527, C_528) | ~r2_hidden(A_526, C_528))), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.64/5.43  tff(c_4899, plain, (![A_12, C_528]: (r1_tarski(k1_tarski(A_12), C_528) | ~r2_hidden(A_12, C_528) | ~r2_hidden(A_12, C_528))), inference(superposition, [status(thm), theory('equality')], [c_12, c_4874])).
% 11.64/5.43  tff(c_30, plain, (![A_32]: (k2_xboole_0(A_32, k1_tarski(A_32))=k1_ordinal1(A_32))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.64/5.43  tff(c_5057, plain, (![A_544, C_545, B_546]: (r1_tarski(k2_xboole_0(A_544, C_545), B_546) | ~r1_tarski(C_545, B_546) | ~r1_tarski(A_544, B_546))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.64/5.43  tff(c_32, plain, (![A_33, B_34]: (r1_ordinal1(A_33, B_34) | ~r1_tarski(A_33, B_34) | ~v3_ordinal1(B_34) | ~v3_ordinal1(A_33))), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.64/5.43  tff(c_6765, plain, (![A_707, C_708, B_709]: (r1_ordinal1(k2_xboole_0(A_707, C_708), B_709) | ~v3_ordinal1(B_709) | ~v3_ordinal1(k2_xboole_0(A_707, C_708)) | ~r1_tarski(C_708, B_709) | ~r1_tarski(A_707, B_709))), inference(resolution, [status(thm)], [c_5057, c_32])).
% 11.64/5.43  tff(c_6774, plain, (![A_32, B_709]: (r1_ordinal1(k1_ordinal1(A_32), B_709) | ~v3_ordinal1(B_709) | ~v3_ordinal1(k2_xboole_0(A_32, k1_tarski(A_32))) | ~r1_tarski(k1_tarski(A_32), B_709) | ~r1_tarski(A_32, B_709))), inference(superposition, [status(thm), theory('equality')], [c_30, c_6765])).
% 11.64/5.43  tff(c_12299, plain, (![A_1052, B_1053]: (r1_ordinal1(k1_ordinal1(A_1052), B_1053) | ~v3_ordinal1(B_1053) | ~v3_ordinal1(k1_ordinal1(A_1052)) | ~r1_tarski(k1_tarski(A_1052), B_1053) | ~r1_tarski(A_1052, B_1053))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_6774])).
% 11.64/5.43  tff(c_21327, plain, (![A_1418, C_1419]: (r1_ordinal1(k1_ordinal1(A_1418), C_1419) | ~v3_ordinal1(C_1419) | ~v3_ordinal1(k1_ordinal1(A_1418)) | ~r1_tarski(A_1418, C_1419) | ~r2_hidden(A_1418, C_1419))), inference(resolution, [status(thm)], [c_4899, c_12299])).
% 11.64/5.43  tff(c_21361, plain, (~v3_ordinal1('#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2')) | ~r1_tarski('#skF_2', '#skF_3') | ~r2_hidden('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_21327, c_4013])).
% 11.64/5.43  tff(c_21385, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4005, c_4334, c_42, c_21361])).
% 11.64/5.43  tff(c_21388, plain, (~r1_ordinal1('#skF_2', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_34, c_21385])).
% 11.64/5.43  tff(c_21391, plain, (~r1_ordinal1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_21388])).
% 11.64/5.43  tff(c_21397, plain, (r1_ordinal1('#skF_3', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_21391])).
% 11.64/5.43  tff(c_21406, plain, (r1_ordinal1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_21397])).
% 11.64/5.43  tff(c_21408, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4440, c_21406])).
% 11.64/5.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.64/5.43  
% 11.64/5.43  Inference rules
% 11.64/5.43  ----------------------
% 11.64/5.43  #Ref     : 0
% 11.64/5.43  #Sup     : 4422
% 11.64/5.43  #Fact    : 4
% 11.64/5.43  #Define  : 0
% 11.64/5.43  #Split   : 19
% 11.64/5.43  #Chain   : 0
% 11.64/5.43  #Close   : 0
% 11.64/5.43  
% 11.64/5.43  Ordering : KBO
% 11.64/5.43  
% 11.64/5.43  Simplification rules
% 11.64/5.43  ----------------------
% 11.64/5.43  #Subsume      : 803
% 11.64/5.43  #Demod        : 750
% 11.64/5.43  #Tautology    : 626
% 11.64/5.43  #SimpNegUnit  : 4
% 11.64/5.43  #BackRed      : 0
% 11.64/5.43  
% 11.64/5.43  #Partial instantiations: 0
% 11.64/5.43  #Strategies tried      : 1
% 11.64/5.43  
% 11.64/5.43  Timing (in seconds)
% 11.64/5.43  ----------------------
% 11.64/5.43  Preprocessing        : 0.32
% 11.64/5.43  Parsing              : 0.16
% 11.64/5.43  CNF conversion       : 0.02
% 11.64/5.43  Main loop            : 4.20
% 11.64/5.43  Inferencing          : 0.95
% 11.64/5.43  Reduction            : 1.66
% 11.64/5.43  Demodulation         : 1.20
% 11.64/5.43  BG Simplification    : 0.08
% 11.64/5.43  Subsumption          : 1.22
% 11.64/5.43  Abstraction          : 0.10
% 11.64/5.43  MUC search           : 0.00
% 11.64/5.43  Cooper               : 0.00
% 11.64/5.43  Total                : 4.55
% 11.64/5.43  Index Insertion      : 0.00
% 11.64/5.43  Index Deletion       : 0.00
% 11.64/5.43  Index Matching       : 0.00
% 11.64/5.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
