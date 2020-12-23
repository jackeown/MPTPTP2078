%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0275+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:02 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   54 (  94 expanded)
%              Number of leaves         :   17 (  38 expanded)
%              Depth                    :    6
%              Number of atoms          :   71 ( 171 expanded)
%              Number of equality atoms :   17 (  43 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_41,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k4_xboole_0(k2_tarski(A,B),C) = k1_xboole_0
      <=> ( r2_hidden(A,C)
          & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).

tff(f_28,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_16,plain,
    ( r2_hidden('#skF_1','#skF_3')
    | ~ r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_47,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_20,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_41,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_35,plain,(
    ! [A_13,C_14,B_15] :
      ( r2_hidden(A_13,C_14)
      | ~ r1_tarski(k2_tarski(A_13,B_15),C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_48,plain,(
    ! [A_16,B_17,B_18] :
      ( r2_hidden(A_16,B_17)
      | k4_xboole_0(k2_tarski(A_16,B_18),B_17) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_35])).

tff(c_51,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_48])).

tff(c_55,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_51])).

tff(c_56,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_58,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_29,plain,(
    ! [B_10,C_11,A_12] :
      ( r2_hidden(B_10,C_11)
      | ~ r1_tarski(k2_tarski(A_12,B_10),C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_74,plain,(
    ! [B_22,B_23,A_24] :
      ( r2_hidden(B_22,B_23)
      | k4_xboole_0(k2_tarski(A_24,B_22),B_23) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_29])).

tff(c_77,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_74])).

tff(c_81,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_77])).

tff(c_82,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_57,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_83,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_14,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | ~ r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_85,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_83,c_14])).

tff(c_98,plain,(
    ! [A_31,B_32,C_33] :
      ( r1_tarski(k2_tarski(A_31,B_32),C_33)
      | ~ r2_hidden(B_32,C_33)
      | ~ r2_hidden(A_31,C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_114,plain,(
    ! [A_34,B_35,C_36] :
      ( k4_xboole_0(k2_tarski(A_34,B_35),C_36) = k1_xboole_0
      | ~ r2_hidden(B_35,C_36)
      | ~ r2_hidden(A_34,C_36) ) ),
    inference(resolution,[status(thm)],[c_98,c_4])).

tff(c_12,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_xboole_0
    | ~ r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_113,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_83,c_12])).

tff(c_120,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | ~ r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_113])).

tff(c_140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_85,c_120])).

tff(c_142,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_22,plain,
    ( r2_hidden('#skF_1','#skF_3')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_145,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_22])).

tff(c_141,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_148,plain,(
    ! [A_43,B_44,C_45] :
      ( r1_tarski(k2_tarski(A_43,B_44),C_45)
      | ~ r2_hidden(B_44,C_45)
      | ~ r2_hidden(A_43,C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_162,plain,(
    ! [A_46,B_47,C_48] :
      ( k4_xboole_0(k2_tarski(A_46,B_47),C_48) = k1_xboole_0
      | ~ r2_hidden(B_47,C_48)
      | ~ r2_hidden(A_46,C_48) ) ),
    inference(resolution,[status(thm)],[c_148,c_4])).

tff(c_18,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_xboole_0
    | k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_161,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_18])).

tff(c_168,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | ~ r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_161])).

tff(c_185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_141,c_168])).

%------------------------------------------------------------------------------
