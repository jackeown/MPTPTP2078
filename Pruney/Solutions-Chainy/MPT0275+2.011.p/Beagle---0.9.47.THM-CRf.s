%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:17 EST 2020

% Result     : Theorem 10.93s
% Output     : CNFRefutation 10.93s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 153 expanded)
%              Number of leaves         :   37 (  65 expanded)
%              Depth                    :    8
%              Number of atoms          :  134 ( 257 expanded)
%              Number of equality atoms :   32 (  73 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_1 > #skF_11 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k4_xboole_0(k2_tarski(A,B),C) = k1_xboole_0
      <=> ( r2_hidden(A,C)
          & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_63,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_61,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_65,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & r2_hidden(C,B) )
     => k3_xboole_0(k2_tarski(A,C),B) = k2_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).

tff(c_84,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | ~ r2_hidden('#skF_10','#skF_11')
    | ~ r2_hidden('#skF_9','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_234,plain,(
    ~ r2_hidden('#skF_9','#skF_11') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_197,plain,(
    ! [A_61,B_62] : k1_enumset1(A_61,A_61,B_62) = k2_tarski(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_52,plain,(
    ! [E_28,B_23,C_24] : r2_hidden(E_28,k1_enumset1(E_28,B_23,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_203,plain,(
    ! [A_61,B_62] : r2_hidden(A_61,k2_tarski(A_61,B_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_52])).

tff(c_42,plain,(
    ! [A_20] : r1_xboole_0(A_20,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_40,plain,(
    ! [A_19] : k3_xboole_0(A_19,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_216,plain,(
    ! [A_65,B_66,C_67] :
      ( ~ r1_xboole_0(A_65,B_66)
      | ~ r2_hidden(C_67,k3_xboole_0(A_65,B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_228,plain,(
    ! [A_19,C_67] :
      ( ~ r1_xboole_0(A_19,k1_xboole_0)
      | ~ r2_hidden(C_67,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_216])).

tff(c_230,plain,(
    ! [C_67] : ~ r2_hidden(C_67,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_228])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_88,plain,
    ( r2_hidden('#skF_7','#skF_8')
    | k4_xboole_0(k2_tarski('#skF_9','#skF_10'),'#skF_11') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_190,plain,(
    k4_xboole_0(k2_tarski('#skF_9','#skF_10'),'#skF_11') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_38,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_673,plain,(
    ! [A_124,C_125,B_126] :
      ( r2_hidden(A_124,C_125)
      | ~ r2_hidden(A_124,B_126)
      | r2_hidden(A_124,k5_xboole_0(B_126,C_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8341,plain,(
    ! [A_11946,A_11947,B_11948] :
      ( r2_hidden(A_11946,k3_xboole_0(A_11947,B_11948))
      | ~ r2_hidden(A_11946,A_11947)
      | r2_hidden(A_11946,k4_xboole_0(A_11947,B_11948)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_673])).

tff(c_8392,plain,(
    ! [A_11946] :
      ( r2_hidden(A_11946,k3_xboole_0(k2_tarski('#skF_9','#skF_10'),'#skF_11'))
      | ~ r2_hidden(A_11946,k2_tarski('#skF_9','#skF_10'))
      | r2_hidden(A_11946,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_8341])).

tff(c_8409,plain,(
    ! [A_11946] :
      ( r2_hidden(A_11946,k3_xboole_0('#skF_11',k2_tarski('#skF_9','#skF_10')))
      | ~ r2_hidden(A_11946,k2_tarski('#skF_9','#skF_10'))
      | r2_hidden(A_11946,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8392])).

tff(c_9835,plain,(
    ! [A_12465] :
      ( r2_hidden(A_12465,k3_xboole_0('#skF_11',k2_tarski('#skF_9','#skF_10')))
      | ~ r2_hidden(A_12465,k2_tarski('#skF_9','#skF_10')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_230,c_8409])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,A_3)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_9892,plain,(
    ! [A_12592] :
      ( r2_hidden(A_12592,'#skF_11')
      | ~ r2_hidden(A_12592,k2_tarski('#skF_9','#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_9835,c_8])).

tff(c_9948,plain,(
    r2_hidden('#skF_9','#skF_11') ),
    inference(resolution,[status(thm)],[c_203,c_9892])).

tff(c_9965,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_234,c_9948])).

tff(c_9966,plain,
    ( ~ r2_hidden('#skF_10','#skF_11')
    | r2_hidden('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_9968,plain,(
    ~ r2_hidden('#skF_10','#skF_11') ),
    inference(splitLeft,[status(thm)],[c_9966])).

tff(c_48,plain,(
    ! [E_28,A_22,B_23] : r2_hidden(E_28,k1_enumset1(A_22,B_23,E_28)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_206,plain,(
    ! [B_62,A_61] : r2_hidden(B_62,k2_tarski(A_61,B_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_48])).

tff(c_10442,plain,(
    ! [A_12778,C_12779,B_12780] :
      ( r2_hidden(A_12778,C_12779)
      | ~ r2_hidden(A_12778,B_12780)
      | r2_hidden(A_12778,k5_xboole_0(B_12780,C_12779)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20117,plain,(
    ! [A_25314,A_25315,B_25316] :
      ( r2_hidden(A_25314,k3_xboole_0(A_25315,B_25316))
      | ~ r2_hidden(A_25314,A_25315)
      | r2_hidden(A_25314,k4_xboole_0(A_25315,B_25316)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_10442])).

tff(c_20171,plain,(
    ! [A_25314] :
      ( r2_hidden(A_25314,k3_xboole_0(k2_tarski('#skF_9','#skF_10'),'#skF_11'))
      | ~ r2_hidden(A_25314,k2_tarski('#skF_9','#skF_10'))
      | r2_hidden(A_25314,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_20117])).

tff(c_20189,plain,(
    ! [A_25314] :
      ( r2_hidden(A_25314,k3_xboole_0('#skF_11',k2_tarski('#skF_9','#skF_10')))
      | ~ r2_hidden(A_25314,k2_tarski('#skF_9','#skF_10'))
      | r2_hidden(A_25314,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20171])).

tff(c_20747,plain,(
    ! [A_25573] :
      ( r2_hidden(A_25573,k3_xboole_0('#skF_11',k2_tarski('#skF_9','#skF_10')))
      | ~ r2_hidden(A_25573,k2_tarski('#skF_9','#skF_10')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_230,c_20189])).

tff(c_20804,plain,(
    ! [A_25700] :
      ( r2_hidden(A_25700,'#skF_11')
      | ~ r2_hidden(A_25700,k2_tarski('#skF_9','#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_20747,c_8])).

tff(c_20856,plain,(
    r2_hidden('#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_206,c_20804])).

tff(c_20876,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9968,c_20856])).

tff(c_20877,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_9966])).

tff(c_9967,plain,(
    r2_hidden('#skF_9','#skF_11') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_20878,plain,(
    r2_hidden('#skF_10','#skF_11') ),
    inference(splitRight,[status(thm)],[c_9966])).

tff(c_82,plain,
    ( r2_hidden('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_10','#skF_11')
    | ~ r2_hidden('#skF_9','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_20956,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9967,c_20878,c_82])).

tff(c_44,plain,(
    ! [A_21] : k5_xboole_0(A_21,A_21) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_21638,plain,(
    ! [A_25921,C_25922,B_25923] :
      ( k3_xboole_0(k2_tarski(A_25921,C_25922),B_25923) = k2_tarski(A_25921,C_25922)
      | ~ r2_hidden(C_25922,B_25923)
      | ~ r2_hidden(A_25921,B_25923) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_21695,plain,(
    ! [A_25921,C_25922,B_25923] :
      ( k5_xboole_0(k2_tarski(A_25921,C_25922),k2_tarski(A_25921,C_25922)) = k4_xboole_0(k2_tarski(A_25921,C_25922),B_25923)
      | ~ r2_hidden(C_25922,B_25923)
      | ~ r2_hidden(A_25921,B_25923) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21638,c_38])).

tff(c_28530,plain,(
    ! [A_37892,C_37893,B_37894] :
      ( k4_xboole_0(k2_tarski(A_37892,C_37893),B_37894) = k1_xboole_0
      | ~ r2_hidden(C_37893,B_37894)
      | ~ r2_hidden(A_37892,B_37894) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_21695])).

tff(c_80,plain,
    ( k4_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') != k1_xboole_0
    | ~ r2_hidden('#skF_10','#skF_11')
    | ~ r2_hidden('#skF_9','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_21227,plain,(
    k4_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9967,c_20878,c_80])).

tff(c_28544,plain,
    ( ~ r2_hidden('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_6','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_28530,c_21227])).

tff(c_28565,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20877,c_20956,c_28544])).

tff(c_28567,plain,(
    k4_xboole_0(k2_tarski('#skF_9','#skF_10'),'#skF_11') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_90,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | k4_xboole_0(k2_tarski('#skF_9','#skF_10'),'#skF_11') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_28708,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_28567,c_90])).

tff(c_28566,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_29328,plain,(
    ! [A_38126,C_38127,B_38128] :
      ( k3_xboole_0(k2_tarski(A_38126,C_38127),B_38128) = k2_tarski(A_38126,C_38127)
      | ~ r2_hidden(C_38127,B_38128)
      | ~ r2_hidden(A_38126,B_38128) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_29387,plain,(
    ! [A_38126,C_38127,B_38128] :
      ( k5_xboole_0(k2_tarski(A_38126,C_38127),k2_tarski(A_38126,C_38127)) = k4_xboole_0(k2_tarski(A_38126,C_38127),B_38128)
      | ~ r2_hidden(C_38127,B_38128)
      | ~ r2_hidden(A_38126,B_38128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29328,c_38])).

tff(c_35953,plain,(
    ! [A_49846,C_49847,B_49848] :
      ( k4_xboole_0(k2_tarski(A_49846,C_49847),B_49848) = k1_xboole_0
      | ~ r2_hidden(C_49847,B_49848)
      | ~ r2_hidden(A_49846,B_49848) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_29387])).

tff(c_86,plain,
    ( k4_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') != k1_xboole_0
    | k4_xboole_0(k2_tarski('#skF_9','#skF_10'),'#skF_11') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_28828,plain,(
    k4_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_28567,c_86])).

tff(c_35967,plain,
    ( ~ r2_hidden('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_6','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_35953,c_28828])).

tff(c_35985,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28708,c_28566,c_35967])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:35:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.93/4.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.93/4.54  
% 10.93/4.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.93/4.54  %$ r2_hidden > r1_xboole_0 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_1 > #skF_11 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_5
% 10.93/4.54  
% 10.93/4.54  %Foreground sorts:
% 10.93/4.54  
% 10.93/4.54  
% 10.93/4.54  %Background operators:
% 10.93/4.54  
% 10.93/4.54  
% 10.93/4.54  %Foreground operators:
% 10.93/4.54  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 10.93/4.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.93/4.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.93/4.54  tff('#skF_11', type, '#skF_11': $i).
% 10.93/4.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.93/4.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.93/4.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.93/4.54  tff('#skF_7', type, '#skF_7': $i).
% 10.93/4.54  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.93/4.54  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.93/4.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.93/4.54  tff('#skF_10', type, '#skF_10': $i).
% 10.93/4.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.93/4.54  tff('#skF_6', type, '#skF_6': $i).
% 10.93/4.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.93/4.54  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.93/4.54  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.93/4.54  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.93/4.54  tff('#skF_9', type, '#skF_9': $i).
% 10.93/4.54  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 10.93/4.54  tff('#skF_8', type, '#skF_8': $i).
% 10.93/4.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.93/4.54  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 10.93/4.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.93/4.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.93/4.54  
% 10.93/4.56  tff(f_101, negated_conjecture, ~(![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_xboole_0) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_zfmisc_1)).
% 10.93/4.56  tff(f_82, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 10.93/4.56  tff(f_80, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 10.93/4.56  tff(f_63, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 10.93/4.56  tff(f_61, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 10.93/4.56  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 10.93/4.56  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.93/4.56  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.93/4.56  tff(f_43, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 10.93/4.56  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 10.93/4.56  tff(f_65, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 10.93/4.56  tff(f_94, axiom, (![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k3_xboole_0(k2_tarski(A, C), B) = k2_tarski(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_zfmisc_1)).
% 10.93/4.56  tff(c_84, plain, (r2_hidden('#skF_6', '#skF_8') | ~r2_hidden('#skF_10', '#skF_11') | ~r2_hidden('#skF_9', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.93/4.56  tff(c_234, plain, (~r2_hidden('#skF_9', '#skF_11')), inference(splitLeft, [status(thm)], [c_84])).
% 10.93/4.56  tff(c_197, plain, (![A_61, B_62]: (k1_enumset1(A_61, A_61, B_62)=k2_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.93/4.56  tff(c_52, plain, (![E_28, B_23, C_24]: (r2_hidden(E_28, k1_enumset1(E_28, B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.93/4.56  tff(c_203, plain, (![A_61, B_62]: (r2_hidden(A_61, k2_tarski(A_61, B_62)))), inference(superposition, [status(thm), theory('equality')], [c_197, c_52])).
% 10.93/4.56  tff(c_42, plain, (![A_20]: (r1_xboole_0(A_20, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.93/4.56  tff(c_40, plain, (![A_19]: (k3_xboole_0(A_19, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.93/4.56  tff(c_216, plain, (![A_65, B_66, C_67]: (~r1_xboole_0(A_65, B_66) | ~r2_hidden(C_67, k3_xboole_0(A_65, B_66)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.93/4.56  tff(c_228, plain, (![A_19, C_67]: (~r1_xboole_0(A_19, k1_xboole_0) | ~r2_hidden(C_67, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40, c_216])).
% 10.93/4.56  tff(c_230, plain, (![C_67]: (~r2_hidden(C_67, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_228])).
% 10.93/4.56  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.93/4.56  tff(c_88, plain, (r2_hidden('#skF_7', '#skF_8') | k4_xboole_0(k2_tarski('#skF_9', '#skF_10'), '#skF_11')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.93/4.56  tff(c_190, plain, (k4_xboole_0(k2_tarski('#skF_9', '#skF_10'), '#skF_11')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_88])).
% 10.93/4.56  tff(c_38, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.93/4.56  tff(c_673, plain, (![A_124, C_125, B_126]: (r2_hidden(A_124, C_125) | ~r2_hidden(A_124, B_126) | r2_hidden(A_124, k5_xboole_0(B_126, C_125)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.93/4.56  tff(c_8341, plain, (![A_11946, A_11947, B_11948]: (r2_hidden(A_11946, k3_xboole_0(A_11947, B_11948)) | ~r2_hidden(A_11946, A_11947) | r2_hidden(A_11946, k4_xboole_0(A_11947, B_11948)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_673])).
% 10.93/4.56  tff(c_8392, plain, (![A_11946]: (r2_hidden(A_11946, k3_xboole_0(k2_tarski('#skF_9', '#skF_10'), '#skF_11')) | ~r2_hidden(A_11946, k2_tarski('#skF_9', '#skF_10')) | r2_hidden(A_11946, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_190, c_8341])).
% 10.93/4.56  tff(c_8409, plain, (![A_11946]: (r2_hidden(A_11946, k3_xboole_0('#skF_11', k2_tarski('#skF_9', '#skF_10'))) | ~r2_hidden(A_11946, k2_tarski('#skF_9', '#skF_10')) | r2_hidden(A_11946, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8392])).
% 10.93/4.56  tff(c_9835, plain, (![A_12465]: (r2_hidden(A_12465, k3_xboole_0('#skF_11', k2_tarski('#skF_9', '#skF_10'))) | ~r2_hidden(A_12465, k2_tarski('#skF_9', '#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_230, c_8409])).
% 10.93/4.56  tff(c_8, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, A_3) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.93/4.56  tff(c_9892, plain, (![A_12592]: (r2_hidden(A_12592, '#skF_11') | ~r2_hidden(A_12592, k2_tarski('#skF_9', '#skF_10')))), inference(resolution, [status(thm)], [c_9835, c_8])).
% 10.93/4.56  tff(c_9948, plain, (r2_hidden('#skF_9', '#skF_11')), inference(resolution, [status(thm)], [c_203, c_9892])).
% 10.93/4.56  tff(c_9965, plain, $false, inference(negUnitSimplification, [status(thm)], [c_234, c_9948])).
% 10.93/4.56  tff(c_9966, plain, (~r2_hidden('#skF_10', '#skF_11') | r2_hidden('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_84])).
% 10.93/4.56  tff(c_9968, plain, (~r2_hidden('#skF_10', '#skF_11')), inference(splitLeft, [status(thm)], [c_9966])).
% 10.93/4.56  tff(c_48, plain, (![E_28, A_22, B_23]: (r2_hidden(E_28, k1_enumset1(A_22, B_23, E_28)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.93/4.56  tff(c_206, plain, (![B_62, A_61]: (r2_hidden(B_62, k2_tarski(A_61, B_62)))), inference(superposition, [status(thm), theory('equality')], [c_197, c_48])).
% 10.93/4.56  tff(c_10442, plain, (![A_12778, C_12779, B_12780]: (r2_hidden(A_12778, C_12779) | ~r2_hidden(A_12778, B_12780) | r2_hidden(A_12778, k5_xboole_0(B_12780, C_12779)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.93/4.56  tff(c_20117, plain, (![A_25314, A_25315, B_25316]: (r2_hidden(A_25314, k3_xboole_0(A_25315, B_25316)) | ~r2_hidden(A_25314, A_25315) | r2_hidden(A_25314, k4_xboole_0(A_25315, B_25316)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_10442])).
% 10.93/4.56  tff(c_20171, plain, (![A_25314]: (r2_hidden(A_25314, k3_xboole_0(k2_tarski('#skF_9', '#skF_10'), '#skF_11')) | ~r2_hidden(A_25314, k2_tarski('#skF_9', '#skF_10')) | r2_hidden(A_25314, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_190, c_20117])).
% 10.93/4.56  tff(c_20189, plain, (![A_25314]: (r2_hidden(A_25314, k3_xboole_0('#skF_11', k2_tarski('#skF_9', '#skF_10'))) | ~r2_hidden(A_25314, k2_tarski('#skF_9', '#skF_10')) | r2_hidden(A_25314, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20171])).
% 10.93/4.56  tff(c_20747, plain, (![A_25573]: (r2_hidden(A_25573, k3_xboole_0('#skF_11', k2_tarski('#skF_9', '#skF_10'))) | ~r2_hidden(A_25573, k2_tarski('#skF_9', '#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_230, c_20189])).
% 10.93/4.56  tff(c_20804, plain, (![A_25700]: (r2_hidden(A_25700, '#skF_11') | ~r2_hidden(A_25700, k2_tarski('#skF_9', '#skF_10')))), inference(resolution, [status(thm)], [c_20747, c_8])).
% 10.93/4.56  tff(c_20856, plain, (r2_hidden('#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_206, c_20804])).
% 10.93/4.56  tff(c_20876, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9968, c_20856])).
% 10.93/4.56  tff(c_20877, plain, (r2_hidden('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_9966])).
% 10.93/4.56  tff(c_9967, plain, (r2_hidden('#skF_9', '#skF_11')), inference(splitRight, [status(thm)], [c_84])).
% 10.93/4.56  tff(c_20878, plain, (r2_hidden('#skF_10', '#skF_11')), inference(splitRight, [status(thm)], [c_9966])).
% 10.93/4.56  tff(c_82, plain, (r2_hidden('#skF_7', '#skF_8') | ~r2_hidden('#skF_10', '#skF_11') | ~r2_hidden('#skF_9', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.93/4.56  tff(c_20956, plain, (r2_hidden('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_9967, c_20878, c_82])).
% 10.93/4.56  tff(c_44, plain, (![A_21]: (k5_xboole_0(A_21, A_21)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.93/4.56  tff(c_21638, plain, (![A_25921, C_25922, B_25923]: (k3_xboole_0(k2_tarski(A_25921, C_25922), B_25923)=k2_tarski(A_25921, C_25922) | ~r2_hidden(C_25922, B_25923) | ~r2_hidden(A_25921, B_25923))), inference(cnfTransformation, [status(thm)], [f_94])).
% 10.93/4.56  tff(c_21695, plain, (![A_25921, C_25922, B_25923]: (k5_xboole_0(k2_tarski(A_25921, C_25922), k2_tarski(A_25921, C_25922))=k4_xboole_0(k2_tarski(A_25921, C_25922), B_25923) | ~r2_hidden(C_25922, B_25923) | ~r2_hidden(A_25921, B_25923))), inference(superposition, [status(thm), theory('equality')], [c_21638, c_38])).
% 10.93/4.56  tff(c_28530, plain, (![A_37892, C_37893, B_37894]: (k4_xboole_0(k2_tarski(A_37892, C_37893), B_37894)=k1_xboole_0 | ~r2_hidden(C_37893, B_37894) | ~r2_hidden(A_37892, B_37894))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_21695])).
% 10.93/4.56  tff(c_80, plain, (k4_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')!=k1_xboole_0 | ~r2_hidden('#skF_10', '#skF_11') | ~r2_hidden('#skF_9', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.93/4.56  tff(c_21227, plain, (k4_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_9967, c_20878, c_80])).
% 10.93/4.56  tff(c_28544, plain, (~r2_hidden('#skF_7', '#skF_8') | ~r2_hidden('#skF_6', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_28530, c_21227])).
% 10.93/4.56  tff(c_28565, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20877, c_20956, c_28544])).
% 10.93/4.56  tff(c_28567, plain, (k4_xboole_0(k2_tarski('#skF_9', '#skF_10'), '#skF_11')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_88])).
% 10.93/4.56  tff(c_90, plain, (r2_hidden('#skF_6', '#skF_8') | k4_xboole_0(k2_tarski('#skF_9', '#skF_10'), '#skF_11')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.93/4.56  tff(c_28708, plain, (r2_hidden('#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_28567, c_90])).
% 10.93/4.56  tff(c_28566, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_88])).
% 10.93/4.56  tff(c_29328, plain, (![A_38126, C_38127, B_38128]: (k3_xboole_0(k2_tarski(A_38126, C_38127), B_38128)=k2_tarski(A_38126, C_38127) | ~r2_hidden(C_38127, B_38128) | ~r2_hidden(A_38126, B_38128))), inference(cnfTransformation, [status(thm)], [f_94])).
% 10.93/4.56  tff(c_29387, plain, (![A_38126, C_38127, B_38128]: (k5_xboole_0(k2_tarski(A_38126, C_38127), k2_tarski(A_38126, C_38127))=k4_xboole_0(k2_tarski(A_38126, C_38127), B_38128) | ~r2_hidden(C_38127, B_38128) | ~r2_hidden(A_38126, B_38128))), inference(superposition, [status(thm), theory('equality')], [c_29328, c_38])).
% 10.93/4.56  tff(c_35953, plain, (![A_49846, C_49847, B_49848]: (k4_xboole_0(k2_tarski(A_49846, C_49847), B_49848)=k1_xboole_0 | ~r2_hidden(C_49847, B_49848) | ~r2_hidden(A_49846, B_49848))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_29387])).
% 10.93/4.56  tff(c_86, plain, (k4_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')!=k1_xboole_0 | k4_xboole_0(k2_tarski('#skF_9', '#skF_10'), '#skF_11')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.93/4.56  tff(c_28828, plain, (k4_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_28567, c_86])).
% 10.93/4.56  tff(c_35967, plain, (~r2_hidden('#skF_7', '#skF_8') | ~r2_hidden('#skF_6', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_35953, c_28828])).
% 10.93/4.56  tff(c_35985, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28708, c_28566, c_35967])).
% 10.93/4.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.93/4.56  
% 10.93/4.56  Inference rules
% 10.93/4.56  ----------------------
% 10.93/4.56  #Ref     : 0
% 10.93/4.56  #Sup     : 7729
% 10.93/4.56  #Fact    : 72
% 10.93/4.56  #Define  : 0
% 10.93/4.56  #Split   : 4
% 10.93/4.56  #Chain   : 0
% 10.93/4.56  #Close   : 0
% 10.93/4.56  
% 10.93/4.56  Ordering : KBO
% 10.93/4.56  
% 10.93/4.56  Simplification rules
% 10.93/4.56  ----------------------
% 10.93/4.56  #Subsume      : 3203
% 10.93/4.56  #Demod        : 2327
% 10.93/4.56  #Tautology    : 2004
% 10.93/4.56  #SimpNegUnit  : 208
% 10.93/4.56  #BackRed      : 0
% 10.93/4.56  
% 10.93/4.56  #Partial instantiations: 23280
% 10.93/4.56  #Strategies tried      : 1
% 10.93/4.56  
% 10.93/4.56  Timing (in seconds)
% 10.93/4.56  ----------------------
% 10.93/4.56  Preprocessing        : 0.34
% 10.93/4.56  Parsing              : 0.16
% 10.93/4.56  CNF conversion       : 0.03
% 10.93/4.56  Main loop            : 3.43
% 10.93/4.56  Inferencing          : 1.40
% 10.93/4.56  Reduction            : 1.02
% 10.93/4.56  Demodulation         : 0.80
% 10.93/4.56  BG Simplification    : 0.13
% 10.93/4.56  Subsumption          : 0.71
% 10.93/4.56  Abstraction          : 0.18
% 10.93/4.56  MUC search           : 0.00
% 10.93/4.56  Cooper               : 0.00
% 10.93/4.56  Total                : 3.81
% 10.93/4.56  Index Insertion      : 0.00
% 10.93/4.56  Index Deletion       : 0.00
% 11.11/4.56  Index Matching       : 0.00
% 11.11/4.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
